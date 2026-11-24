-- Prove2me | Definitions.Def_CSL_Shared_Programs_BufferedGatherInvariant
-- name    : CSL_Shared_Programs_BufferedGatherInvariant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:57.561494+00:00
-- url     : https://prove2.me/theorems/827ac697-6bc8-4f5e-8845-f87a3ca07bb2
-- title:
--   Coded sorting library: Shared / Programs / BufferedGatherInvariant
-- statement:
--   Module `CodedSorting.Shared.Programs.BufferedGatherInvariant` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A buffered scatter with one RAM bank per bucket.  Input records are read
--   in their original order.  Only a full bank, or the last partial bank of a
--   bucket, is written to disk.  All initial RAM and disk contents are arbitrary.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.BufferedGatherInvariant

import Definitions.Def_CSL_Compat
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

section BufferedScatterInvariant
/-! A buffered scatter with one RAM bank per bucket.  Input records are read
in their original order.  Only a full bank, or the last partial bank of a
bucket, is written to disk.  All initial RAM and disk contents are arbitrary. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CSL.BufferedScatterInvariant

structure State (K W : ℕ) (α : Type*) where
  bank : Fin K → Fin W → α
  disk : Fin K → ℕ → Fin W → α

variable {V K L W : ℕ} {α : Type*}

def slot (hW : 0<W) (r : ℕ) : Fin W := ⟨r%W, Nat.mod_lt _ hW⟩

def Flush (W L r : ℕ) : Prop := r%W=W-1 ∨ r+1=L
instance (W L r : ℕ) : Decidable (Flush W L r) := inferInstanceAs (Decidable (_ ∨ _))

def step (hW : 0<W) (e : Fin V ≃ Fin K × Fin L) (F : Fin V → α)
    (i : Fin V) (s : State K W α) : State K W α :=
  let k := (e i).1
  let r := (e i).2.val
  let bank := Function.update s.bank k (Function.update (s.bank k) (slot hW r) (F i))
  ⟨bank, if Flush W L r then
    Function.update s.disk k (Function.update (s.disk k) (r/W) (bank k)) else s.disk⟩

def run (hW : 0<W) (e : Fin V ≃ Fin K × Fin L) (F : Fin V → α)
    (s : State K W α) : ℕ → State K W α
  | 0 => s
  | n+1 => if h : n<V then step hW e F ⟨n,h⟩ (run hW e F s n)
    else run hW e F s n

def index (e : Fin V ≃ Fin K × Fin L) (k : Fin K) (r : Fin L) : ℕ :=
  (e.symm (k,r)).val

def Ordered (e : Fin V ≃ Fin K × Fin L) : Prop :=
  ∀ k : Fin K, StrictMono (fun r : Fin L => index e k r)

def Latest (e : Fin V ≃ Fin K × Fin L) (n : ℕ) (k : Fin K) (r : Fin L) : Prop :=
  index e k r<n ∧ ∀ t : Fin L, index e k t<n → t.val%W=r.val%W → t≤r

def Complete (e : Fin V ≃ Fin K × Fin L) (n : ℕ) (k : Fin K) (r : Fin L) : Prop :=
  ∃ t : Fin L, index e k t<n ∧ Flush W L t.val ∧ r.val/W=t.val/W

def Invariant (hW : 0<W) (e : Fin V ≃ Fin K × Fin L) (F : Fin V → α)
    (n : ℕ) (s : State K W α) : Prop :=
  (∀ k r, Latest (W:=W) e n k r → s.bank k (slot hW r.val)=F (e.symm (k,r))) ∧
  (∀ k r, Complete (W:=W) e n k r → s.disk k (r.val/W) (slot hW r.val)=F (e.symm (k,r)))

private theorem rank_le {e : Fin V ≃ Fin K × Fin L} (ho : Ordered e)
    {k : Fin K} {r t : Fin L} (h : index e k r≤index e k t) : r≤t :=
  (ho k).le_iff_le.mp h

private theorem flush_largest (hW : 0<W) (r t : Fin L)
    (h : Flush W L t.val) (hp : r.val/W=t.val/W) : r≤t := by
  have hr := Nat.mod_lt r.val hW
  have ht := Nat.mod_lt t.val hW
  have er := Nat.mod_add_div r.val W
  have et := Nat.mod_add_div t.val W
  rcases h with h | h
  · rw [hp] at er
    apply Fin.le_iff_val_le_val.mpr
    omega
  · exact Fin.le_iff_val_le_val.mpr (by omega)

private theorem same_slot_le (hW : 0<W) {r t u : ℕ}
    (htu : t≤u) (hpage : r/W=u/W) (hslot : t%W=r%W) : t≤r := by
  have hd := Nat.div_le_div_right htu (c:=W)
  have hm := Nat.mul_le_mul_left W hd
  have er := Nat.mod_add_div r W
  have et := Nat.mod_add_div t W
  rw [← hpage] at hm
  omega

private theorem flush_unique (hW : 0<W) (r t : Fin L)
    (hr : Flush W L r.val) (ht : Flush W L t.val)
    (hp : r.val/W=t.val/W) : r=t :=
  le_antisymm (flush_largest hW r t ht hp) (flush_largest hW t r hr hp.symm)

private theorem invariant_zero (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (F : Fin V → α) (s : State K W α) : Invariant hW e F 0 s := by
  constructor
  · intro k r h
    exact (Nat.not_lt_zero _ h.1).elim
  · intro k r h
    obtain ⟨t,ht,-,-⟩ := h
    exact (Nat.not_lt_zero _ ht).elim

private theorem index_eq_input (e : Fin V ≃ Fin K × Fin L)
    (i : Fin V) {k : Fin K} {r : Fin L} (h : index e k r=i.val) :
    (k,r)=e i := by
  apply e.symm.injective
  apply Fin.ext
  simpa only [Equiv.symm_apply_apply, index] using h

private theorem index_current (e : Fin V ≃ Fin K × Fin L) (i : Fin V) :
    index e (e i).1 (e i).2=i.val := by simp [index]

private theorem step_bank (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (F : Fin V → α) (i : Fin V) (s : State K W α) (k : Fin K) (p : Fin W) :
    (step hW e F i s).bank k p=
      if k=(e i).1 ∧ p=slot hW (e i).2.val then F i else s.bank k p := by
  by_cases hk : k=(e i).1
  · subst k
    by_cases hp : p=slot hW (e i).2.val <;> simp [step,hp]
  · simp [step,hk]

private theorem step_disk (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (F : Fin V → α) (i : Fin V) (s : State K W α) (k : Fin K) (p : ℕ) :
    (step hW e F i s).disk k p=
      if Flush W L (e i).2.val ∧ k=(e i).1 ∧ p=(e i).2.val/W
      then (step hW e F i s).bank k else s.disk k p := by
  by_cases hf : Flush W L (e i).2.val
  · by_cases hk : k=(e i).1
    · subst k
      by_cases hp : p=(e i).2.val/W <;> simp [step,hf,hp]
    · simp [step,hf,hk]
  · simp [step,hf]

theorem invariant_step (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (F : Fin V → α) (i : Fin V) (s : State K W α)
    (h : Invariant hW e F i.val s) :
    Invariant hW e F (i.val+1) (step hW e F i s) := by
  have hi := index_current e i
  have hb : ∀ k r, Latest (W:=W) e (i.val+1) k r →
      (step hW e F i s).bank k (slot hW r.val)=F (e.symm (k,r)) := by
    intro k r hr
    obtain ⟨hrdone,hrlast⟩ := hr
    rw [step_bank]
    split_ifs with hu
    · obtain ⟨hk,hs⟩ := hu
      subst k
      have he : r=(e i).2 := by
        apply le_antisymm
        · exact rank_le ho (k:=(e i).1) (by omega)
        · apply hrlast (e i).2 (by omega)
          exact (congrArg Fin.val hs).symm
      subst r
      simp
    · have hri : index e k r<i.val := by
        by_contra hn
        have he := index_eq_input e i (show index e k r=i.val by omega)
        have hk : k=(e i).1 := congrArg Prod.fst he
        have hs : r=(e i).2 := congrArg Prod.snd he
        exact hu ⟨hk,by rw [hs]⟩
      exact h.1 k r ⟨hri,fun t ht hs => hrlast t (by omega) hs⟩
  refine ⟨hb,?_⟩
  intro k r hr
  obtain ⟨t,ht,hf,hp⟩ := hr
  by_cases hold : index e k t<i.val
  · rw [step_disk]
    split_ifs with hu
    · obtain ⟨hf',hk,hp'⟩ := hu
      have he : t=(e i).2 := flush_unique hW t (e i).2 hf hf' (hp.symm.trans hp')
      subst k
      rw [he] at hold
      omega
    · exact h.2 k r ⟨t,hold,hf,hp⟩
  · have he := index_eq_input e i (show index e k t=i.val by omega)
    have hk : k=(e i).1 := congrArg Prod.fst he
    have ht' : t=(e i).2 := congrArg Prod.snd he
    subst k
    subst t
    rw [step_disk,if_pos ⟨hf,rfl,hp⟩]
    apply hb
    have hle : r≤(e i).2 := flush_largest hW r (e i).2 hf hp
    refine ⟨?_,?_⟩
    · have hh := (ho (e i).1).monotone hle
      omega
    · intro u hu hs
      have hule : u≤(e i).2 := rank_le ho (k:=(e i).1) (by omega)
      exact Fin.le_iff_val_le_val.mpr (same_slot_le hW hule hp hs)

theorem invariant_run (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (F : Fin V → α) (s : State K W α)
    (n : ℕ) (hn : n≤V) : Invariant hW e F n (run hW e F s n) := by
  induction n with
  | zero => exact invariant_zero hW e F s
  | succ n ih =>
    have hlt : n<V := by omega
    rw [run, dif_pos hlt]
    exact invariant_step hW e ho F ⟨n,hlt⟩ _ (ih (by omega))

/-- Each nonempty bucket page ends in exactly one flushing record. -/
theorem flush_cover (hW : 0<W) (r : Fin L) :
    ∃ t : Fin L, Flush W L t.val ∧ r.val/W=t.val/W := by
  let E := min ((r.val/W+1)*W) L
  have er := Nat.mod_add_div r.val W
  have hr := Nat.mod_lt r.val hW
  have hlt : r.val<(r.val/W+1)*W := by nlinarith
  have hE : r.val<E := lt_min hlt r.isLt
  have hEL : E≤L := min_le_right _ _
  have hEB : E≤(r.val/W+1)*W := min_le_left _ _
  let t : Fin L := ⟨E-1,by omega⟩
  have ht : t.val+1=E := by dsimp [t]; omega
  have hrt : r.val≤t.val := by omega
  have hp : t.val/W=r.val/W := by
    apply Nat.div_eq_of_lt_le
    · exact (Nat.div_mul_le_self r.val W).trans hrt
    · omega
  refine ⟨t,?_,hp.symm⟩
  by_cases he : (r.val/W+1)*W≤L
  · have heq : E=(r.val/W+1)*W := min_eq_left he
    have et := Nat.mod_add_div t.val W
    rw [hp] at et
    left
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (r.val/W) W] at heq
    omega
  · right
    have heq : E=L := min_eq_right (by omega)
    omega

/-- Running the actual buffered updates over the whole input scatters every
record to its bucket and rank. No zero-initialization premise is needed. -/
theorem run_correct (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (F : Fin V → α) (s : State K W α)
    (k : Fin K) (r : Fin L) :
    (run hW e F s V).disk k (r.val/W) (slot hW r.val)=F (e.symm (k,r)) := by
  apply (invariant_run hW e ho F s V le_rfl).2
  obtain ⟨t,hf,hp⟩ := flush_cover hW r
  exact ⟨t,(e.symm (k,t)).isLt,hf,hp⟩

end CSL.BufferedScatterInvariant
end BufferedScatterInvariant

section BufferedGatherInvariant
/-! Buffered reconstruction of a stream from ordered bucket files. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace CSL.BufferedGatherInvariant

structure State (K W : ℕ) (α : Type*) where
  bank : Fin K → Fin W → α
  output : Fin W → α
  disk : ℕ → Fin W → α

variable {V K L W : ℕ} {α : Type*}

def slot (hW : 0<W) (r : ℕ) : Fin W := ⟨r%W,Nat.mod_lt _ hW⟩

def Flush (W V i : ℕ) : Prop := i%W=W-1 ∨ i+1=V
instance (W V i : ℕ) : Decidable (Flush W V i) := inferInstanceAs (Decidable (_ ∨ _))

def index (e : Fin V ≃ Fin K × Fin L) (k : Fin K) (r : Fin L) : ℕ :=
  (e.symm (k,r)).val

def Ordered (e : Fin V ≃ Fin K × Fin L) : Prop :=
  ∀ k : Fin K, StrictMono (fun r : Fin L => index e k r)

def firstRank (r : Fin L) : Fin L :=
  ⟨r.val/W*W,(Nat.div_mul_le_self _ _).trans_lt r.isLt⟩

@[simp] theorem firstRank_page (hW : 0<W) (r : Fin L) :
    (firstRank (W:=W) r).val/W=r.val/W := by
  exact Nat.mul_div_cancel _ hW

@[simp] theorem firstRank_slot (r : Fin L) :
    (firstRank (W:=W) r).val%W=0 := by simp [firstRank]

@[simp] theorem index_at (e : Fin V ≃ Fin K × Fin L) (i : Fin V) :
    index e (e i).1 (e i).2=i.val := by
  simp [index]

def loadBank (e : Fin V ≃ Fin K × Fin L)
    (D : Fin K → ℕ → Fin W → α) (i : Fin V)
    (bank : Fin K → Fin W → α) : Fin K → Fin W → α :=
  if (e i).2.val%W=0 then
    Function.update bank (e i).1 (D (e i).1 ((e i).2.val/W)) else bank

def value (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (D : Fin K → ℕ → Fin W → α) (i : Fin V) : α :=
  D (e i).1 ((e i).2.val/W) (slot hW (e i).2.val)

def step (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (D : Fin K → ℕ → Fin W → α) (i : Fin V) (s : State K W α) : State K W α :=
  let bank := loadBank e D i s.bank
  let output := Function.update s.output (slot hW i.val)
    (bank (e i).1 (slot hW (e i).2.val))
  ⟨bank,output,if Flush W V i.val then Function.update s.disk (i.val/W) output else s.disk⟩

def run (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (D : Fin K → ℕ → Fin W → α) (s : State K W α) : ℕ → State K W α
  | 0 => s
  | n+1 => if h : n<V then step hW e D ⟨n,h⟩ (run hW e D s n)
    else run hW e D s n

/-- A block whose first visit has happened and whose requested visit is
still ahead remains in that bucket's existing RAM bank. -/
def Ready (e : Fin V ≃ Fin K × Fin L) (D : Fin K → ℕ → Fin W → α)
    (n : ℕ) (bank : Fin K → Fin W → α) : Prop :=
  ∀ j : Fin V, n≤j.val → index e (e j).1 (firstRank (W:=W) (e j).2)<n →
    bank (e j).1=D (e j).1 ((e j).2.val/W)

theorem loaded_bank (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (D : Fin K → ℕ → Fin W → α) (i : Fin V)
    (bank : Fin K → Fin W → α) (hr : Ready e D i.val bank) :
    loadBank e D i bank (e i).1=D (e i).1 ((e i).2.val/W) := by
  by_cases hz : (e i).2.val%W=0
  · simp [loadBank,hz]
  · rw [loadBank,if_neg hz]
    apply hr i le_rfl
    have hlt : firstRank (W:=W) (e i).2 < (e i).2 := by
      apply Fin.lt_iff_val_lt_val.mpr
      have hh := Nat.mod_add_div (e i).2.val W
      change (e i).2.val/W*W < (e i).2.val
      rw [Nat.mul_comm W] at hh
      omega
    simpa only [index_at] using ho (e i).1 hlt

theorem ready_step (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (D : Fin K → ℕ → Fin W → α) (i : Fin V)
    (bank : Fin K → Fin W → α) (hr : Ready e D i.val bank) :
    Ready e D (i.val+1) (loadBank e D i bank) := by
  intro j hj hf
  by_cases hfirst : index e (e j).1 (firstRank (W:=W) (e j).2)<i.val
  · have hold := hr j (by omega) hfirst
    by_cases hz : (e i).2.val%W=0
    · by_cases hk : (e j).1=(e i).1
      · have hposi : index e (e j).1 (e i).2=i.val := by rw [hk,index_at]
        have hlow : firstRank (W:=W) (e j).2 ≤ (e i).2 := by
          apply (ho (e j).1).le_iff_le.mp
          rw [hposi]
          exact hfirst.le
        have hhigh : (e i).2 ≤ (e j).2 := by
          apply (ho (e j).1).le_iff_le.mp
          rw [hposi,index_at]
          omega
        have hlo := Nat.div_le_div_right
          (Fin.le_iff_val_le_val.mp hlow) (c:=W)
        have hhi := Nat.div_le_div_right
          (Fin.le_iff_val_le_val.mp hhigh) (c:=W)
        rw [firstRank_page hW] at hlo
        have hp : (e i).2.val/W=(e j).2.val/W := Nat.le_antisymm hhi hlo
        simp only [loadBank,if_pos hz]
        rw [hk,Function.update_self,hp]
      · simpa [loadBank,hz,hk] using hold
    · simpa [loadBank,hz] using hold
  · have heq : index e (e j).1 (firstRank (W:=W) (e j).2)=i.val := by omega
    have hei : e.symm ((e j).1,firstRank (W:=W) (e j).2)=i :=
      Fin.ext heq
    have hep : ((e j).1,firstRank (W:=W) (e j).2)=e i := by
      simpa only [e.apply_symm_apply] using congrArg e hei
    have hk := congrArg (fun p : Fin K × Fin L => p.1) hep
    have hrank := congrArg (fun p : Fin K × Fin L => p.2) hep
    change (e j).1=(e i).1 at hk
    change firstRank (W:=W) (e j).2=(e i).2 at hrank
    have hz : (e i).2.val%W=0 := by rw [←hrank,firstRank_slot]
    have hp : (e i).2.val/W=(e j).2.val/W := by rw [←hrank,firstRank_page hW]
    simp only [loadBank,if_pos hz]
    rw [hk,Function.update_self,hp]

theorem ready_run (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (D : Fin K → ℕ → Fin W → α)
    (s : State K W α) (n : ℕ) : Ready e D n (run hW e D s n).bank := by
  induction n with
  | zero =>
    intro j hj hf
    omega
  | succ n ih =>
    by_cases hn : n<V
    · rw [run,dif_pos hn]
      exact ready_step hW e ho D ⟨n,hn⟩ _ ih
    · intro j hj hf
      have := j.isLt
      omega

theorem run_loaded_bank (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (D : Fin K → ℕ → Fin W → α)
    (s : State K W α) (i : Fin V) :
    loadBank e D i (run hW e D s i.val).bank (e i).1=
      D (e i).1 ((e i).2.val/W) :=
  loaded_bank hW e ho D i _ (ready_run hW e ho D s i.val)

/-- The output buffer is an ordinary one-bucket sequential scatter. -/
def outputEquiv (V : ℕ) : Fin V ≃ Fin 1 × Fin V where
  toFun i := (0,i)
  invFun p := p.2
  left_inv i := rfl
  right_inv p := by
    obtain ⟨k,i⟩ := p
    have hk : k=0 := Subsingleton.elim _ _
    subst k
    rfl

theorem output_ordered (V : ℕ) : BufferedScatterInvariant.Ordered (outputEquiv V) := by
  intro k a b hab
  exact hab

def outputState (s : State K W α) : BufferedScatterInvariant.State 1 W α :=
  ⟨fun _ => s.output,fun _ => s.disk⟩

theorem output_step (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (D : Fin K → ℕ → Fin W → α) (i : Fin V) (s : State K W α)
    (hl : loadBank e D i s.bank (e i).1=D (e i).1 ((e i).2.val/W)) :
    outputState (step hW e D i s)=
      BufferedScatterInvariant.step hW (outputEquiv V) (value hW e D) i (outputState s) := by
  try dsimp only [step,outputState,BufferedScatterInvariant.step,outputEquiv]
  rw [hl]
  change BufferedScatterInvariant.State.mk
      (fun _ => Function.update s.output (slot hW i.val) (value hW e D i))
      (fun _ => if Flush W V i.val then
        Function.update s.disk (i.val/W)
          (Function.update s.output (slot hW i.val) (value hW e D i)) else s.disk) = _
  congr 1
  · funext k
    have hk : k=0 := Subsingleton.elim _ _
    subst k
    simp [BufferedScatterInvariant.slot,slot]
  · funext k
    have hk : k=0 := Subsingleton.elim _ _
    subst k
    by_cases hf : Flush W V i.val
    · simp only [if_pos hf]
      have hfs : BufferedScatterInvariant.Flush W V i.val := hf
      simp [hfs,BufferedScatterInvariant.slot,slot]
    · simp only [if_neg hf]
      have hfs : ¬BufferedScatterInvariant.Flush W V i.val := hf
      simp [hfs]

theorem output_run (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (D : Fin K → ℕ → Fin W → α)
    (s : State K W α) (n : ℕ) :
    outputState (run hW e D s n)=
      BufferedScatterInvariant.run hW (outputEquiv V) (value hW e D) (outputState s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n<V
    · rw [run,dif_pos hn,BufferedScatterInvariant.run,dif_pos hn,←ih]
      apply output_step
      exact run_loaded_bank hW e ho D s ⟨n,hn⟩
    · rw [run,dif_neg hn,BufferedScatterInvariant.run,dif_neg hn,ih]

/-- Every requested live output is written to the actual output disk.
All initial bank, output-buffer, and disk contents are arbitrary. -/
theorem run_correct (hW : 0<W) (e : Fin V ≃ Fin K × Fin L)
    (ho : Ordered e) (D : Fin K → ℕ → Fin W → α)
    (s : State K W α) (i : Fin V) :
    (run hW e D s V).disk (i.val/W) (slot hW i.val)=
      D (e i).1 ((e i).2.val/W) (slot hW (e i).2.val) := by
  have h := BufferedScatterInvariant.run_correct hW (outputEquiv V)
    (output_ordered V) (value hW e D) (outputState s) 0 i
  rw [←output_run hW e ho D s V] at h
  exact h

end CSL.BufferedGatherInvariant
end BufferedGatherInvariant


