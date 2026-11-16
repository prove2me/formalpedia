-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreALeaf
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:12:15.333658+00:00
-- url     : https://prove2.me/theorems/7352414e-407d-421a-a401-c8df8e36dedd
-- title:
--   Block-0 leaf-mix instructions and interval disjointness
-- statement:
--   # Block-0 leaf-mix generators
--
--   Leaf-slot bounds, pairwise-disjoint source intervals, and the leaf-mix instruction sequence `leafMix` that writes each code `cND t` onto the wires in the interval of leaf $t$. The pack also records abstract `MovesV` append-bounds lemmas and the preservation of `MovesV` when `leafMix` is appended after `preF` and `copyoND` under the already-established prefix hypotheses.
--
--   Depends on the published `Block0CoreAData`, `Block0CoreABits`, and `Block0CoreACopy` packs. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean identifiers: `leafMix`, `leafAt`, `leafHi`, `leafSlotBound`, `MovesV_leafMix`, `MovesV_genF_append_bounds`, `MovesV_preF_copyoND_leaves_holds`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: CoreA leaf split. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Block-0 `leafMix` and `MovesV_preF_copyoND_leaves_holds`.
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem srcS_vals_isChain : List.IsChain (fun a b : ℕ => a < b) srcS_vals := by
  decide

theorem srcS_lt_succ {t : ℕ} (ht : t + 1 < v) : srcS t < srcS (t + 1) := by
  have hv : v = 1771 := rfl
  have h1 : t + 1 < srcS_vals.length := by rw [srcS_vals_len]; omega
  have ht0 : t < v := Nat.lt_of_succ_lt ht
  rw [srcS_get ht0, srcS_get ht]
  exact List.IsChain.getElem srcS_vals_isChain t h1

theorem srcS_lt_of_lt {t t' : ℕ} (h : t < t') (ht' : t' < v) :
    srcS t < srcS t' := by
  have hv : v = 1771 := rfl
  have ht : t < v := Nat.lt_trans h ht'
  rw [srcS_get ht, srcS_get ht']
  have hp : List.Pairwise (fun a b : ℕ => a < b) srcS_vals :=
    List.isChain_iff_pairwise.mp srcS_vals_isChain
  have hi : t < srcS_vals.length := by rw [srcS_vals_len]; omega
  have hj : t' < srcS_vals.length := by rw [srcS_vals_len]; omega
  exact (List.pairwise_iff_getElem.mp hp) t t' hi hj h

def leafSlotBound : ℕ := 11099

def leafHi (t : ℕ) : ℕ := if t + 1 = v then leafSlotBound else srcS (t + 1)

theorem srcS_succ_lt_of_ne {t : ℕ} (ht : t < v) (hne : t + 1 ≠ v) : t + 1 < v :=
  Nat.lt_of_le_of_ne (Nat.succ_le_of_lt ht) hne

theorem leafHi_succ {t : ℕ} (ht : t + 1 < v) : leafHi t = srcS (t + 1) := by
  have : t + 1 ≠ v := Nat.ne_of_lt ht
  simp [leafHi, this]

theorem srcS_lt_leafHi {t : ℕ} (ht : t < v) : srcS t + 1 ≤ leafHi t := by
  unfold leafHi
  split_ifs with h
  · have : srcS t < 11091 := srcS_lt ht
    unfold leafSlotBound; omega
  · have ht' : t + 1 < v := srcS_succ_lt_of_ne ht h
    have : srcS t < srcS (t + 1) := srcS_lt_succ ht'
    omega

theorem leafHi_le_slotBound {t : ℕ} (ht : t < v) : leafHi t ≤ leafSlotBound := by
  unfold leafHi
  split_ifs with h
  · exact Nat.le_refl _
  · have ht' : t + 1 < v := srcS_succ_lt_of_ne ht h
    have : srcS (t + 1) < 11091 := srcS_lt ht'
    unfold leafSlotBound; omega

def leafExtras (t : ℕ) : List ℕ :=
  List.range' (srcS t + 1) (leafHi t - (srcS t + 1))

theorem mem_leafExtras {t q : ℕ} (ht : t < v) :
    q ∈ leafExtras t ↔ srcS t < q ∧ q < leafHi t := by
  have hle : srcS t + 1 ≤ leafHi t := srcS_lt_leafHi ht
  have hsum : srcS t + 1 + (leafHi t - (srcS t + 1)) = leafHi t := Nat.add_sub_of_le hle
  unfold leafExtras
  rw [List.mem_range'_1, hsum]
  exact ⟨fun ⟨hlo, hhi⟩ => ⟨Nat.lt_of_succ_le hlo, hhi⟩,
    fun ⟨hlo, hhi⟩ => ⟨Nat.succ_le_of_lt hlo, hhi⟩⟩

theorem leafExtras_ne_srcS {t q t' : ℕ} (ht : t < v) (ht' : t' < v)
    (hq : q ∈ leafExtras t) : srcS t' ≠ q := by
  have ⟨hlo, hhi⟩ := (mem_leafExtras ht).1 hq
  rcases Nat.lt_trichotomy t' t with h | h | h
  · exact Nat.ne_of_lt (Nat.lt_trans (srcS_lt_of_lt h ht) hlo)
  · subst h; exact (Nat.ne_of_lt hlo)
  · have ht1 : t + 1 ≤ t' := Nat.succ_le_of_lt h
    by_cases hnv : t + 1 = v
    · omega
    · have ht's : t + 1 < v := srcS_succ_lt_of_ne ht hnv
      have hHi : leafHi t = srcS (t + 1) := leafHi_succ ht's
      have hss : srcS (t + 1) ≤ srcS t' := by
        rcases Nat.eq_or_lt_of_le ht1 with heq | hlt
        · rw [heq]
        · exact Nat.le_of_lt (srcS_lt_of_lt hlt ht')
      rw [hHi] at hhi
      have : q < srcS t' := Nat.lt_of_lt_of_le hhi hss
      exact (Nat.ne_of_lt this).symm

theorem leafInterval_disjoint {t t' : ℕ} (ht : t < v) (ht' : t' < v) (hne : t ≠ t')
    {q : ℕ} (hq : q ∈ leafExtras t) : q ∉ leafExtras t' := by
  intro hq'
  have ⟨lo, hi⟩ := (mem_leafExtras ht).1 hq
  have ⟨lo', hi'⟩ := (mem_leafExtras ht').1 hq'
  rcases Nat.lt_trichotomy t t' with h | h | h
  · have ht1 : t + 1 ≤ t' := Nat.succ_le_of_lt h
    by_cases hnv : t + 1 = v
    · omega
    · have hts : t + 1 < v := srcS_succ_lt_of_ne ht hnv
      have : leafHi t = srcS (t + 1) := leafHi_succ hts
      have : srcS (t + 1) ≤ srcS t' := by
        rcases Nat.eq_or_lt_of_le ht1 with heq | hlt
        · rw [heq]
        · exact Nat.le_of_lt (srcS_lt_of_lt hlt ht')
      -- q < leafHi t = srcS (t+1) ≤ srcS t' < q, contradiction
      omega
  · exact hne h
  · have ht1 : t' + 1 ≤ t := Nat.succ_le_of_lt h
    by_cases hnv : t' + 1 = v
    · omega
    · have hts : t' + 1 < v := srcS_succ_lt_of_ne ht' hnv
      have : leafHi t' = srcS (t' + 1) := leafHi_succ hts
      have : srcS (t' + 1) ≤ srcS t := by
        rcases Nat.eq_or_lt_of_le ht1 with heq | hlt
        · rw [heq]
        · exact Nat.le_of_lt (srcS_lt_of_lt hlt ht)
      omega

theorem leafExtras_wS_lt_aux {t q : ℕ} (ht : t < v) (hq : q ∈ leafExtras t) :
    wS q < wAuxEnd := by
  have ⟨_, hhi⟩ := (mem_leafExtras ht).1 hq
  have hbound : leafHi t ≤ leafSlotBound := leafHi_le_slotBound ht
  have : q < 11099 := Nat.lt_of_lt_of_le hhi hbound
  have : wS q = wEnt + q := wS_eq q
  have : wEnt = 3542 := rfl
  have : wAuxEnd = 31336 := rfl
  omega

def leafAt (t : ℕ) : LInstr :=
  mk (cND t) (leafExtras t |>.map fun o => (wS o, wS (srcS t)))

theorem leafAt_code (t : ℕ) : (leafAt t).1 = cND t := rfl

theorem leafAt_touch (t : ℕ) :
    (leafAt t).2.1 =
      (leafExtras t).flatMap fun o => [wS o, wS (srcS t)] := by
  simp [leafAt, mk, touch, List.flatMap_map]

theorem preF_wS_any (q : ℕ) (hq : wS q < wAuxEnd) :
    (genF initR preF).1 (wS q) = 0 := by
  have h := preF_state (wS q)
  have h0 : initR (wS q) = 0 := initR_wS q hq
  rcases h with h | h
  · rwa [h0] at h
  · exact h

theorem copyo_map_state (f : ℕ → ℕ) (ts : List ℕ)
    (hnd : ts.Nodup)
    (htv : ∀ t ∈ ts, t < v)
    (hS : ∀ t ∈ ts, f (wS (srcS t)) = 0)
    (hX : ∀ t ∈ ts, f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound) :
    ∀ x, (genF f (ts.map copyoAt)).1 x = f x ∨
      (∃ t ∈ ts, (x = wS (srcS t) ∨ x = wX t) ∧
        (genF f (ts.map copyoAt)).1 x = cND t) := by
  induction ts generalizing f with
  | nil =>
    intro x; simp [genF]
  | cons t ts ih =>
    have hcons := List.nodup_cons.1 hnd
    have htnin : t ∉ ts := hcons.1
    have hnd' : ts.Nodup := hcons.2
    have ht : t < v := htv t (List.mem_cons.2 (Or.inl rfl))
    have htv' : ∀ t' ∈ ts, t' < v := fun t' ht' => htv t' (List.mem_cons_of_mem _ ht')
    have hone := MovesV_copyoAt f t ht (hS t (List.mem_cons.2 (Or.inl rfl)))
      (hX t (List.mem_cons.2 (Or.inl rfl))) hf
    have happ := genF_append f [copyoAt t] (ts.map copyoAt)
    simp only [List.singleton_append] at happ
    have hmap : (t :: ts).map copyoAt = copyoAt t :: ts.map copyoAt := rfl
    intro x
    rw [hmap, happ]
    set f' := (genF f [copyoAt t]).1
    have hf' : ∀ y, f' y < SupG.codeBound := hone.2.1
    have hinv := hone.2.2
    have hS' : ∀ t' ∈ ts, f' (wS (srcS t')) = 0 := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne_t : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hneS : wS (srcS t') ≠ wS (srcS t) := by
        intro heq
        have heq' : wEnt + srcS t' = wEnt + srcS t := by
          rw [← wS_eq, ← wS_eq, heq]
        exact hne_t (srcS_inj ht'v ht (Nat.add_left_cancel heq'))
      have hneX : wS (srcS t') ≠ wX t := wS_ne_wX (srcS t') t ht
      have hx := hinv (wS (srcS t'))
      rcases hx with hx | hx
      · rw [hx]; exact hS t' (List.mem_cons_of_mem _ ht')
      · rcases hx.1 with hx1 | hx1
        · exact (hneS hx1).elim
        · exact (hneX hx1).elim
    have hX' : ∀ t' ∈ ts, f' (wX t') = 0 ∨ f' (wX t') = cND t' := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne_t : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hneX : wX t' ≠ wX t := by
        intro heq
        exact hne_t (by simpa [wX_eq] using heq)
      have hneS : wX t' ≠ wS (srcS t) := (wS_ne_wX (srcS t) t' ht'v).symm
      have hx := hinv (wX t')
      rcases hx with hx | hx
      · rw [hx]; exact hX t' (List.mem_cons_of_mem _ ht')
      · rcases hx.1 with hx1 | hx1
        · exact (hneS hx1).elim
        · exact (hneX hx1).elim
    have hind := ih f' hnd' htv' hS' hX' hf' x
    rcases hind with hx | hx
    · have hx0 := hinv x
      rcases hx0 with hx0 | hx0
      · exact Or.inl (hx.trans hx0)
      · refine Or.inr ⟨t, List.mem_cons.2 (Or.inl rfl), hx0.1, ?_⟩
        rw [hx, hx0.2]
    · rcases hx with ⟨t', ht', hx1, hx2⟩
      exact Or.inr ⟨t', List.mem_cons_of_mem _ ht', hx1, hx2⟩


theorem copyoAt_get_srcS (f : ℕ → ℕ) {t : ℕ} (ht : t < v)
    (hS : f (wS (srcS t)) = 0)
    (hX : f (wX t) = 0 ∨ f (wX t) = cND t) :
    (genF f [copyoAt t]).1 (wS (srcS t)) = cND t := by
  have hgen := genF_singleton f (copyoAt t)
  have htouch := copyoAt_touch t
  have hcode := copyoAt_code t
  have hne : f (wS (srcS t)) ≠ cND t := by
    rw [hS]; exact (cND_ne_zero t).symm
  have hstep :
      mvF (cND t) (f, []) (wS (srcS t)) =
        (fun x => if x = wS (srcS t) then cND t else f x,
          (wS (srcS t), f (wS (srcS t))) :: []) := by
    simp [mvF, hne]
  have hneX : wX t ≠ wS (srcS t) := (wS_ne_wX (srcS t) t ht).symm
  rw [hgen, htouch, hcode]
  -- foldl on [wS, wX]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hstep]
  -- second mvF may or may not write wX; it does not change wS
  by_cases hfw : (fun x => if x = wS (srcS t) then cND t else f x) (wX t) = cND t
  · have : mvF (cND t)
        (fun x => if x = wS (srcS t) then cND t else f x,
          [(wS (srcS t), f (wS (srcS t)))]) (wX t) =
        (fun x => if x = wS (srcS t) then cND t else f x,
          [(wS (srcS t), f (wS (srcS t)))]) := by
      simp [mvF, hfw]
    rw [this]
    simp [hneX]
  · have : mvF (cND t)
        (fun x => if x = wS (srcS t) then cND t else f x,
          [(wS (srcS t), f (wS (srcS t)))]) (wX t) =
        (fun x => if x = wX t then cND t
          else if x = wS (srcS t) then cND t else f x,
          (wX t, (fun x => if x = wS (srcS t) then cND t else f x) (wX t)) ::
            [(wS (srcS t), f (wS (srcS t)))]) := by
      simp [mvF, hfw]
    rw [this]
    simp [hneX]

theorem copyo_map_wS_other (f : ℕ → ℕ) (ts : List ℕ)
    (hnd : ts.Nodup)
    (htv : ∀ t ∈ ts, t < v)
    (hS : ∀ t ∈ ts, f (wS (srcS t)) = 0)
    (hX : ∀ t ∈ ts, f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound)
    {q : ℕ}
    (hnone : ∀ t ∈ ts, srcS t ≠ q) :
    (genF f (ts.map copyoAt)).1 (wS q) = f (wS q) := by
  have h := copyo_map_state f ts hnd htv hS hX hf (wS q)
  rcases h with h | h
  · exact h
  · rcases h with ⟨t, ht, hx1, hx2⟩
    have ht' : t < v := htv t ht
    rcases hx1 with hx1 | hx1
    · have : srcS t = q := by
        have : wEnt + srcS t = wEnt + q := by
          rw [← wS_eq, ← wS_eq, hx1]
        exact Nat.add_left_cancel this
      exact (hnone t ht this).elim
    · exact (wS_ne_wX q t ht' hx1).elim

theorem copyo_map_get_srcS (f : ℕ → ℕ) (ts : List ℕ)
    (hnd : ts.Nodup)
    (htv : ∀ t ∈ ts, t < v)
    (hS : ∀ t ∈ ts, f (wS (srcS t)) = 0)
    (hX : ∀ t ∈ ts, f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound)
    {t0 : ℕ} (ht0 : t0 ∈ ts) :
    (genF f (ts.map copyoAt)).1 (wS (srcS t0)) = cND t0 := by
  induction ts generalizing f with
  | nil => cases ht0
  | cons t ts ih =>
    have hcons := List.nodup_cons.1 hnd
    have htnin : t ∉ ts := hcons.1
    have hnd' : ts.Nodup := hcons.2
    have ht : t < v := htv t (List.mem_cons.2 (Or.inl rfl))
    have htv' : ∀ t' ∈ ts, t' < v := fun t' ht' => htv t' (List.mem_cons_of_mem _ ht')
    have hone := MovesV_copyoAt f t ht (hS t (List.mem_cons.2 (Or.inl rfl)))
      (hX t (List.mem_cons.2 (Or.inl rfl))) hf
    have happ := genF_append f [copyoAt t] (ts.map copyoAt)
    simp only [List.singleton_append] at happ
    have hmap : (t :: ts).map copyoAt = copyoAt t :: ts.map copyoAt := rfl
    rw [hmap, happ]
    set f' := (genF f [copyoAt t]).1
    have hf' : ∀ x, f' x < SupG.codeBound := hone.2.1
    have hinv := hone.2.2
    have hS' : ∀ t' ∈ ts, f' (wS (srcS t')) = 0 := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne_t : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hneS : wS (srcS t') ≠ wS (srcS t) := by
        intro heq
        have heq' : wEnt + srcS t' = wEnt + srcS t := by
          rw [← wS_eq, ← wS_eq, heq]
        exact hne_t (srcS_inj ht'v ht (Nat.add_left_cancel heq'))
      have hneX : wS (srcS t') ≠ wX t := wS_ne_wX (srcS t') t ht
      have hx := hinv (wS (srcS t'))
      rcases hx with hx | hx
      · rw [hx]; exact hS t' (List.mem_cons_of_mem _ ht')
      · rcases hx.1 with hx1 | hx1
        · exact (hneS hx1).elim
        · exact (hneX hx1).elim
    have hX' : ∀ t' ∈ ts, f' (wX t') = 0 ∨ f' (wX t') = cND t' := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne_t : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hneX : wX t' ≠ wX t := by
        intro heq
        exact hne_t (by simpa [wX_eq] using heq)
      have hneS : wX t' ≠ wS (srcS t) := (wS_ne_wX (srcS t) t' ht'v).symm
      have hx := hinv (wX t')
      rcases hx with hx | hx
      · rw [hx]; exact hX t' (List.mem_cons_of_mem _ ht')
      · rcases hx.1 with hx1 | hx1
        · exact (hneS hx1).elim
        · exact (hneX hx1).elim
    rcases List.mem_cons.1 ht0 with hteq | ht0s
    · have ht0t : t0 = t := by
        first | exact hteq | exact hteq.symm
      have hf't : f' (wS (srcS t0)) = cND t0 := by
        rw [ht0t]
        exact copyoAt_get_srcS f ht (hS t (List.mem_cons.2 (Or.inl rfl)))
          (hX t (List.mem_cons.2 (Or.inl rfl)))
      have hnone : ∀ t' ∈ ts, srcS t' ≠ srcS t0 := by
        intro t' ht'
        have ht'v : t' < v := htv' t' ht'
        intro heq
        have hne : t' ≠ t := by
          intro h; subst h; exact htnin ht'
        have heq' : srcS t' = srcS t := ht0t ▸ heq
        exact hne (srcS_inj ht'v ht heq')
      have hrest :=
        copyo_map_wS_other f' ts hnd' htv' hS' hX' hf' hnone
      exact hrest.trans hf't
    · exact ih f' hnd' htv' hS' hX' hf' ht0s

theorem copyoND_get_srcS (f : ℕ → ℕ)
    (hS : ∀ t, t < v → f (wS (srcS t)) = 0)
    (hX : ∀ t, t < v → f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound)
    {t0 : ℕ} (ht0 : t0 < v) :
    (genF f copyoND).1 (wS (srcS t0)) = cND t0 := by
  have H : ∀ n, n = v → t0 < n →
      (genF f ((List.range n).map copyoAt)).1 (wS (srcS t0)) = cND t0 := by
    intro n hn ht0n
    refine copyo_map_get_srcS f (List.range n) List.nodup_range
      (fun t ht => Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn)
      (fun t ht => hS t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      (fun t ht => hX t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      hf (List.mem_range.2 ht0n)
  have h := H v rfl ht0
  exact copyoND_eq ▸ h

theorem copyoND_wS_other (f : ℕ → ℕ)
    (hS : ∀ t, t < v → f (wS (srcS t)) = 0)
    (hX : ∀ t, t < v → f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound)
    {q : ℕ}
    (hnone : ∀ t, t < v → srcS t ≠ q) :
    (genF f copyoND).1 (wS q) = f (wS q) := by
  have H : ∀ n, n = v →
      (genF f ((List.range n).map copyoAt)).1 (wS q) = f (wS q) := by
    intro n hn
    refine copyo_map_wS_other f (List.range n) List.nodup_range
      (fun t ht => Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn)
      (fun t ht => hS t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      (fun t ht => hX t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      hf ?none
    intro t ht
    exact hnone t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn)
  have h := H v rfl
  exact copyoND_eq ▸ h

theorem foldl_mvF_untouched (c : ℕ) (ws : List ℕ) (f : ℕ → ℕ) (acc : List (ℕ × ℕ))
    {x : ℕ} (hx : x ∉ ws) :
    (ws.foldl (mvF c) (f, acc)).1 x = f x := by
  induction ws generalizing f acc with
  | nil => simp
  | cons w ws ih =>
    have hxw : x ≠ w := fun h => hx (List.mem_cons.2 (Or.inl h))
    have hx' : x ∉ ws := fun h => hx (List.mem_cons.2 (Or.inr h))
    simp only [List.foldl_cons]
    by_cases hfw : f w = c
    · have : mvF c (f, acc) w = (f, acc) := by simp [mvF, hfw]
      rw [this]
      exact ih f acc hx'
    · have : mvF c (f, acc) w =
        (fun y => if y = w then c else f y, (w, f w) :: acc) := by
        simp [mvF, hfw]
      rw [this]
      have hih := ih (fun y => if y = w then c else f y) ((w, f w) :: acc) hx'
      simpa [hxw] using hih

theorem foldl_mvF_skip (c : ℕ) (ws : List ℕ) (f : ℕ → ℕ)
    {w : ℕ} (hw : f w = c) :
    ∀ mv ∈ (ws.foldl (mvF c) (f, [])).2, mv.1 ≠ w := by
  have H : ∀ (fcur : ℕ → ℕ) (acc : List (ℕ × ℕ)),
      fcur w = c →
      (∀ mv ∈ acc, mv.1 ≠ w) →
      ∀ mv ∈ (ws.foldl (mvF c) (fcur, acc)).2, mv.1 ≠ w := by
    induction ws with
    | nil =>
      intro fcur acc _ hacc mv hmv; exact hacc mv hmv
    | cons u ws ih =>
      intro fcur acc hwcur hacc mv hmv
      simp only [List.foldl_cons] at hmv
      by_cases hfu : fcur u = c
      · have : mvF c (fcur, acc) u = (fcur, acc) := by simp [mvF, hfu]
        rw [this] at hmv
        exact ih fcur acc hwcur hacc mv hmv
      · have hstep : mvF c (fcur, acc) u =
          (fun y => if y = u then c else fcur y, (u, fcur u) :: acc) := by
          simp [mvF, hfu]
        rw [hstep] at hmv
        refine ih (fun y => if y = u then c else fcur y)
          ((u, fcur u) :: acc) ?_ ?_ mv hmv
        · have hwu : u ≠ w := fun h => hfu (h ▸ hwcur)
          simp [hwu.symm, hwcur]
        · intro mv' hmv'
          rcases List.mem_cons.1 hmv' with h | h
          · subst h; exact fun huw => hfu (by have : u = w := huw; subst this; exact hwcur)
          · exact hacc mv' h
  exact H f [] hw (fun mv h => by cases h)

theorem foldl_mvF_mem (c : ℕ) (ws : List ℕ) (f : ℕ → ℕ) :
    ∀ mv ∈ (ws.foldl (mvF c) (f, [])).2, mv.1 ∈ ws := by
  suffices ∀ (rest : List ℕ) (fcur : ℕ → ℕ) (acc : List (ℕ × ℕ)),
      (∀ mv ∈ acc, mv.1 ∈ ws) →
      (∀ u ∈ rest, u ∈ ws) →
      ∀ mv ∈ (rest.foldl (mvF c) (fcur, acc)).2, mv.1 ∈ ws by
    exact this ws f [] (fun _ h => by cases h) (fun _ hu => hu)
  intro rest
  induction rest with
  | nil =>
    intro fcur acc hacc _ mv hmv; exact hacc mv hmv
  | cons u rest ih =>
    intro fcur acc hacc hrest mv hmv
    simp only [List.foldl_cons] at hmv
    have hu : u ∈ ws := hrest u (List.mem_cons.2 (Or.inl rfl))
    have hrest' : ∀ z ∈ rest, z ∈ ws :=
      fun z hz => hrest z (List.mem_cons.2 (Or.inr hz))
    by_cases hfu : fcur u = c
    · have : mvF c (fcur, acc) u = (fcur, acc) := by simp [mvF, hfu]
      rw [this] at hmv
      exact ih fcur acc hacc hrest' mv hmv
    · have : mvF c (fcur, acc) u =
        (fun y => if y = u then c else fcur y, (u, fcur u) :: acc) := by
        simp [mvF, hfu]
      rw [this] at hmv
      refine ih (fun y => if y = u then c else fcur y)
        ((u, fcur u) :: acc) ?_ hrest' mv hmv
      intro mv' hmv'
      rcases List.mem_cons.1 hmv' with h | h
      · subst h; exact hu
      · exact hacc mv' h

theorem wS_inj {q q' : ℕ} (h : wS q = wS q') : q = q' := by
  have : wEnt + q = wEnt + q' := by rw [← wS_eq, ← wS_eq, h]
  exact Nat.add_left_cancel this

theorem MovesV_leafAt (f : ℕ → ℕ) {t : ℕ} (ht : t < v)
    (hP : f (wS (srcS t)) = cND t)
    (hE : ∀ o ∈ leafExtras t, f (wS o) = 0)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f [leafAt t]).2 ∧
      ∀ x, (genF f [leafAt t]).1 x < SupG.codeBound := by
  have hgen := genF_singleton f (leafAt t)
  have hcode : (leafAt t).1 = cND t := leafAt_code t
  have hcB : cND t < SupG.codeBound := cND_lt_bound ht
  have hold := (foldl_mvF_old (cND t) (leafAt t).2.1 f).1
  have hskip := foldl_mvF_skip (cND t) (leafAt t).2.1 f hP
  have hmem := foldl_mvF_mem (cND t) (leafAt t).2.1 f
  rw [hgen, hcode]
  constructor
  · intro ch hch mv hmv
    simp only [List.mem_singleton] at hch
    subst ch
    have hmv' : mv ∈ ((leafAt t).2.1.foldl (mvF (cND t)) (f, [])).2 :=
      List.mem_reverse.1 hmv
    have hold0 : mv.2 = f mv.1 := hold mv hmv'
    have hneP : mv.1 ≠ wS (srcS t) := hskip mv hmv'
    have hin : mv.1 ∈ (leafAt t).2.1 := hmem mv hmv'
    have holdz : mv.2 = 0 := by
      have hx := (leafAt_touch t) ▸ hin
      rcases List.mem_flatMap.1 hx with ⟨o, ho, hx'⟩
      have : mv.1 = wS o ∨ mv.1 = wS (srcS t) := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx'
        exact hx'
      rcases this with hwo | hp
      · rw [hold0, hwo]; exact hE o ho
      · exact (hneP hp).elim
    refine ⟨nestOK_of_le1 (Or.inl (by rw [holdz]; exact Nat.zero_le 1)), ?_, hcB⟩
    · rw [holdz]
      have : SupG.codeBound = 64251 := SupG.codeBound_eq
      omega
  · intro x
    have hx := (foldl_mvF_old (cND t) (leafAt t).2.1 f).2 x
    rcases hx with hx | hx
    · rw [hx]; exact hf x
    · rw [hx]; exact hcB

theorem not_mem_leafAt_touch_srcS {t t' : ℕ} (ht : t < v) (ht' : t' < v)
    (hne : t ≠ t') : wS (srcS t') ∉ (leafAt t).2.1 := by
  rw [leafAt_touch]
  intro hx
  rcases List.mem_flatMap.1 hx with ⟨o, ho, hx'⟩
  have : wS (srcS t') = wS o ∨ wS (srcS t') = wS (srcS t) := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx'
    exact hx'
  rcases this with h | h
  · exact leafExtras_ne_srcS ht ht' ho (wS_inj h)
  · exact hne.symm (srcS_inj (t := t') (t' := t) ht' ht (wS_inj h))

theorem not_mem_leafAt_touch_extra {t t' : ℕ} (ht : t < v) (ht' : t' < v)
    (hne : t ≠ t') {o' : ℕ} (ho' : o' ∈ leafExtras t') :
    wS o' ∉ (leafAt t).2.1 := by
  rw [leafAt_touch]
  intro hx
  rcases List.mem_flatMap.1 hx with ⟨o, ho, hx'⟩
  have : wS o' = wS o ∨ wS o' = wS (srcS t) := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx'
    exact hx'
  rcases this with h | h
  · have : o' = o := wS_inj h
    exact (leafInterval_disjoint ht' ht hne.symm ho') (this ▸ ho)
  · exact leafExtras_ne_srcS ht' ht ho' (wS_inj h).symm

theorem MovesV_leaf_map (f : ℕ → ℕ) (ts : List ℕ)
    (hnd : ts.Nodup)
    (htv : ∀ t ∈ ts, t < v)
    (hP : ∀ t ∈ ts, f (wS (srcS t)) = cND t)
    (hE : ∀ t ∈ ts, ∀ o ∈ leafExtras t, f (wS o) = 0)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f (ts.map leafAt)).2 ∧
      ∀ x, (genF f (ts.map leafAt)).1 x < SupG.codeBound := by
  induction ts generalizing f with
  | nil =>
    constructor
    · intro ch hc; cases hc
    · intro x; simpa [genF] using hf x
  | cons t ts ih =>
    have hcons := List.nodup_cons.1 hnd
    have htnin : t ∉ ts := hcons.1
    have hnd' : ts.Nodup := hcons.2
    have ht : t < v := htv t (List.mem_cons.2 (Or.inl rfl))
    have htv' : ∀ t' ∈ ts, t' < v := fun t' ht' => htv t' (List.mem_cons_of_mem _ ht')
    have hone := MovesV_leafAt f ht
      (hP t (List.mem_cons.2 (Or.inl rfl)))
      (hE t (List.mem_cons.2 (Or.inl rfl))) hf
    have happ := genF_append f [leafAt t] (ts.map leafAt)
    simp only [List.singleton_append] at happ
    have hmap : (t :: ts).map leafAt = leafAt t :: ts.map leafAt := rfl
    rw [hmap, happ]
    set f' := (genF f [leafAt t]).1
    have hf' : ∀ x, f' x < SupG.codeBound := hone.2
    have hP' : ∀ t' ∈ ts, f' (wS (srcS t')) = cND t' := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hnt : wS (srcS t') ∉ (leafAt t).2.1 :=
        not_mem_leafAt_touch_srcS ht ht'v hne.symm
      have hgen := genF_singleton f (leafAt t)
      have : f' (wS (srcS t')) = f (wS (srcS t')) := by
        unfold f'
        rw [hgen, leafAt_code]
        exact foldl_mvF_untouched (cND t) (leafAt t).2.1 f [] hnt
      rw [this]
      exact hP t' (List.mem_cons_of_mem _ ht')
    have hE' : ∀ t' ∈ ts, ∀ o ∈ leafExtras t', f' (wS o) = 0 := by
      intro t' ht' o ho
      have ht'v : t' < v := htv' t' ht'
      have hne : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hnt : wS o ∉ (leafAt t).2.1 :=
        not_mem_leafAt_touch_extra ht ht'v hne.symm ho
      have hgen := genF_singleton f (leafAt t)
      have : f' (wS o) = f (wS o) := by
        unfold f'
        rw [hgen, leafAt_code]
        exact foldl_mvF_untouched (cND t) (leafAt t).2.1 f [] hnt
      rw [this]
      exact hE t' (List.mem_cons_of_mem _ ht') o ho
    have ⟨hMVrest, hBrest⟩ := ih f' hnd' htv' hP' hE' hf'
    constructor
    · exact MovesV_append.2 ⟨hone.1, hMVrest⟩
    · exact hBrest

def leafMixOf (n : ℕ) : List LInstr := (List.range n).map leafAt

def leafMix : List LInstr := (List.range v).map leafAt

theorem MovesV_leafMix (f : ℕ → ℕ)
    (hP : ∀ t, t < v → f (wS (srcS t)) = cND t)
    (hE : ∀ t, t < v → ∀ o ∈ leafExtras t, f (wS o) = 0)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f leafMix).2 ∧
      ∀ x, (genF f leafMix).1 x < SupG.codeBound := by
  have H : ∀ n, n = v →
      MovesV (genF f (leafMixOf n)).2 ∧
        ∀ x, (genF f (leafMixOf n)).1 x < SupG.codeBound := by
    intro n hn
    refine MovesV_leaf_map f (List.range n) List.nodup_range
      (fun t ht => Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn)
      (fun t ht => hP t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      (fun t ht => hE t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn))
      hf
  unfold leafMix
  exact H v rfl

theorem MovesV_genF_append_bounds (f : ℕ → ℕ)
    (W W' : List (ℕ × List ℕ × List (ℕ × ℕ)))
    (hW : MovesV (genF f W).2 ∧ ∀ x, (genF f W).1 x < SupG.codeBound)
    (hW' : MovesV (genF (genF f W).1 W').2 ∧
           ∀ x, (genF (genF f W).1 W').1 x < SupG.codeBound) :
    MovesV (genF f (W ++ W')).2 ∧
      ∀ x, (genF f (W ++ W')).1 x < SupG.codeBound := by
  have hsnd := congrArg Prod.snd (genF_append f W W')
  have hfst := congrArg Prod.fst (genF_append f W W')
  refine ⟨?mv, ?bd⟩
  · rw [hsnd]
    exact MovesV_append.2 ⟨hW.1, hW'.1⟩
  · intro x
    have : (genF f (W ++ W')).1 x = (genF (genF f W).1 W').1 x := by
      rw [hfst]
    rw [this]
    exact hW'.2 x


theorem MovesV_genF_append_of3 (f : ℕ → ℕ)
    (A B C : List (ℕ × List ℕ × List (ℕ × ℕ)))
    (hA : MovesV (genF f A).2 ∧ ∀ x, (genF f A).1 x < SupG.codeBound)
    (hBC : MovesV (genF (genF f A).1 (B ++ C)).2 ∧
           ∀ x, (genF (genF f A).1 (B ++ C)).1 x < SupG.codeBound) :
    MovesV (genF f (A ++ B ++ C)).2 ∧
      ValidOn (genF f (A ++ B ++ C)).1 := by
  have hassoc : A ++ B ++ C = A ++ (B ++ C) := List.append_assoc A B C
  rw [hassoc]
  exact MovesV_genF_append_of f A (B ++ C) hA hBC

theorem MovesV_preF_copyoND_leaves_holds :
    ValidOn initR ∧
      MovesV (genF initR (preF ++ copyoND ++ leafMix)).2 ∧
        ValidOn (genF initR (preF ++ copyoND ++ leafMix)).1 := by
  refine ⟨initR_ValidOn, ?_⟩
  have hpre := genF_codes_le1 preF initR preF_codes_le1 (fun _ => initR_lt _)
  have hcopy :=
    MovesV_copyoND_from (genF initR preF).1
      (fun t ht => preF_wS t ht)
      (fun t ht => preF_wX t ht)
      hpre.2
  have hP : ∀ t, t < v →
      (genF (genF initR preF).1 copyoND).1 (wS (srcS t)) = cND t :=
    fun t ht =>
      copyoND_get_srcS (genF initR preF).1
        (fun t ht => preF_wS t ht)
        (fun t ht => preF_wX t ht)
        hpre.2 ht
  have hE : ∀ t, t < v → ∀ o ∈ leafExtras t,
      (genF (genF initR preF).1 copyoND).1 (wS o) = 0 := by
    intro t ht o ho
    have hnone : ∀ t', t' < v → srcS t' ≠ o :=
      fun t' ht' => leafExtras_ne_srcS ht ht' ho
    have hq : wS o < wAuxEnd := leafExtras_wS_lt_aux ht ho
    have h := copyoND_wS_other (genF initR preF).1
      (fun t ht => preF_wS t ht)
      (fun t ht => preF_wX t ht)
      hpre.2 hnone
    exact h.trans (preF_wS_any o hq)
  have hleaves :=
    MovesV_leafMix (genF (genF initR preF).1 copyoND).1 hP hE hcopy.2
  have hcl :=
    MovesV_genF_append_bounds (genF initR preF).1 copyoND leafMix hcopy hleaves
  exact MovesV_genF_append_of3 initR preF copyoND leafMix hpre hcl


