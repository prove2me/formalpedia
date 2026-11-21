-- Prove2me | solution 1 for ArithmeticKakeya.katz_tao_counting_lemma
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T15:44:44.33893+00:00
-- url     : https://prove2.me/submissions/e7e7c0a7-d34c-4724-b423-2c59186be54c

import Mathlib

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArithmeticKakeya

open Finset
open scoped BigOperators

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Fibre size of `g` over the value `y`. -/
def fsz {W : Type} [DecidableEq W] (g : X → W) (y : W) : ℕ :=
  (Finset.univ.filter (fun b => g b = y)).card

lemma fsz_eq_card_subtype {W : Type} [DecidableEq W] (g : X → W) (y : W) :
    fsz g y = Fintype.card {a : X // g a = y} := by
  rw [fsz, Fintype.card_subtype]

/-- The type of valid tuples. -/
abbrev Good (k : ℕ) (Y : Fin k → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (f : (i : Fin k) → X → Y i) : Type :=
  {x : Fin (k + 1) → X // ∀ i : Fin k, f i (x i.castSucc) = f i (x i.succ)}

instance (k : ℕ) (Y : Fin k → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (f : (i : Fin k) → X → Y i) : Fintype (Good (X := X) k Y f) := by
  unfold Good; infer_instance

/-! ### Decomposition of `Good (n+1)` and the key injection -/

section Decomp

variable {n : ℕ} {Y : Fin (n + 1) → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
  {f : (i : Fin (n + 1)) → X → Y i}

/-- Given a `Good n` tuple over a subtype `Xp` (with inclusion `F`) and a compatible last
coordinate, build a `Good (n+1)` tuple over `X`. -/
def consGood {Xp : Type} [Fintype Xp] [DecidableEq Xp] (F : Xp → X)
    (y : Good (X := Xp) n (fun j => Y j.castSucc) (fun j a => f j.castSucc (F a)))
    (c : X) (hc : f (Fin.last n) c = f (Fin.last n) (F (y.val (Fin.last n)))) :
    Good (X := X) (n + 1) Y f :=
  ⟨Fin.snoc (fun j => F (y.val j)) c, by
    intro i
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, Fin.snoc_castSucc, Fin.snoc_last]
      exact hc.symm
    | cast j =>
      have h := y.prop j
      simp only [Fin.snoc_castSucc, Fin.succ_castSucc]
      exact h⟩

/-- The domain of the injection: a `Good n` tuple in the subtype together with a compatible last
coordinate. -/
abbrev Ext {Xp : Type} [Fintype Xp] [DecidableEq Xp] (F : Xp → X) : Type :=
  Sigma fun y : Good (X := Xp) n (fun j => Y j.castSucc) (fun j a => f j.castSucc (F a)) =>
    {c : X // f (Fin.last n) c = f (Fin.last n) (F (y.val (Fin.last n)))}

variable {Xp : Type} [Fintype Xp] [DecidableEq Xp]

/-- The injection of `Ext` into `Good (n+1)`. -/
def extToGood (F : Xp → X) (p : Ext (X := X) (n := n) (Y := Y) (f := f) F) :
    Good (X := X) (n + 1) Y f :=
  consGood F p.1 p.2.1 p.2.2

lemma extToGood_injective (F : Xp → X) (hF : Function.Injective F) :
    Function.Injective (extToGood (X := X) (n := n) (Y := Y) (f := f) F) := by
  rintro ⟨py, pc⟩ ⟨qy, qc⟩ hpq
  have h1 : py = qy := by
    have h := congrArg Fin.init (congrArg Subtype.val hpq)
    simp only [extToGood, consGood, Fin.init_snoc] at h
    exact Subtype.ext (funext (fun j => hF (congrFun h j)))
  subst h1
  have h2 : pc = qc := by
    have h := congrFun (congrArg Subtype.val hpq) (Fin.last (n + 1))
    simp only [extToGood, consGood, Fin.snoc_last] at h
    exact Subtype.ext h
  rw [h2]

end Decomp

/-! ### The "lossy" counting lemma -/

section Lossy

/-- An explicit constant for the lossy counting lemma. -/
def KT (k : ℕ) : ℝ := (2:ℝ) ^ (k*k + 5*k + 10)

lemma KT_pos (k : ℕ) : 0 < KT k := by rw [KT]; positivity

lemma KT_ge_one (k : ℕ) : 1 ≤ KT k := by
  rw [KT]
  exact one_le_pow₀ (by norm_num)

lemma KT_step (n : ℕ) : (2:ℝ) ^ (n+2) * KT n ≤ KT (n+1) := by
  have hexp : n*n + 6*n + 12 ≤ (n+1)*(n+1) + 5*(n+1) + 10 := by
    ring_nf; omega
  have h1 : (2:ℝ) ^ (n+2) * KT n = (2:ℝ) ^ (n*n + 6*n + 12) := by
    rw [KT, ← pow_add]; congr 1; ring
  rw [h1, KT]
  exact pow_le_pow_right₀ (by norm_num) hexp

/-- Katz--Tao's lossy counting lemma: there is a constant `C > 0` depending only on `k` with
`(#X)^{k+1} ≤ C · #(valid tuples) · ∏ #(Y i)`. -/
theorem lossyB (k : ℕ) : ∀ (X : Type) [Fintype X] [DecidableEq X]
    (Y : Fin k → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (f : (i : Fin k) → X → Y i),
    (Fintype.card X : ℝ) ^ (k + 1) ≤
      KT k * (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) : ℝ) * ∏ i, (Fintype.card (Y i) : ℝ) := by
  induction k with
  | zero =>
    intro X _ _ Y _ _ f
    have hcard : Fintype.card (Good (X := X) 0 Y f) = Fintype.card X := by
      have e : Good (X := X) 0 Y f ≃ (Fin 1 → X) :=
        { toFun := fun x => x.val
          invFun := fun u => ⟨u, by intro i; exact i.elim0⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun u => rfl }
      rw [Fintype.card_congr e]
      simp
    have h1 : (∏ i : Fin 0, (Fintype.card (Y i) : ℝ)) = 1 := by simp
    rw [hcard, h1, pow_one]
    have hK : (1024:ℝ) ≤ KT 0 := by
      rw [KT]; norm_num
    norm_num
    have : (0:ℝ) ≤ (Fintype.card X : ℝ) := by positivity
    nlinarith [hK, this]
  | succ n ih =>
    intro X _ _ Y _ _ f
    classical
    set g : X → Y (Fin.last n) := f (Fin.last n) with hg
    set m : ℕ := Fintype.card (Y (Fin.last n)) with hm
    set N : ℕ := Fintype.card X with hN
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- `X` empty: trivial
      rw [hN0]
      simp only [Nat.cast_zero]
      rw [zero_pow (by omega : n + 1 + 1 ≠ 0)]
      have h1 : (0:ℝ) ≤ (Fintype.card (Good (X := X) (n + 1) Y f) : ℝ) := by positivity
      have h2 : (0:ℝ) ≤ ∏ i : Fin (n+1), (Fintype.card (Y i) : ℝ) := by
        apply Finset.prod_nonneg
        intro i _
        positivity
      have h0 : (0:ℝ) ≤ KT (n+1) := (KT_pos (n+1)).le
      exact mul_nonneg (mul_nonneg h0 h1) h2
    -- all fibres are nonempty
    have hYpos : ∀ i : Fin (n + 1), 0 < Fintype.card (Y i) := by
      intro i
      have hne : Nonempty X := Fintype.card_pos_iff.mp hNpos
      exact Fintype.card_pos_iff.mpr ⟨f i hne.some⟩
    -- the set of "small" fibres
    set S : Finset (Y (Fin.last n)) := Finset.univ.filter (fun y => 2 * m * fsz g y < N) with hS
    -- the popular points
    set Xp : Type := {a : X // g a ∉ S} with hXp
    haveI hXpF : Fintype Xp := inferInstance
    haveI hXpD : DecidableEq Xp := inferInstance
    -- IH for the restricted problem
    have hIH := ih Xp (fun j => Y j.castSucc) (fun j a => f j.castSucc a.val)
    set G : ℝ := (Fintype.card (Good (X := Xp) n (fun j => Y j.castSucc)
      (fun j a => f j.castSucc a.val)) : ℝ) with hG
    set SG : ℝ := (Fintype.card (Good (X := X) (n + 1) Y f) : ℝ) with hSG
    set Pn : ℝ := ∏ j : Fin n, (Fintype.card (Y j.castSucc) : ℝ) with hPn
    have hPnnn : 0 ≤ Pn := by rw [hPn]; positivity
    -- popularity of points of `Xp`
    have hpop : ∀ a : Xp, (N : ℝ) ≤ 2 * (m : ℝ) * (fsz g (g a.val) : ℝ) := by
      intro a
      have h : g a.val ∉ S := a.2
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at h
      exact_mod_cast h
    -- 1.  `N ≤ 2 * card Xp`
    have hNp : (N : ℝ) ≤ 2 * (Fintype.card Xp : ℝ) := by
      set A : Finset X := Finset.univ.filter (fun a => g a ∈ S) with hA
      have hAcard : (Fintype.card {a : X // g a ∈ S} : ℝ) = (A.card : ℝ) := by
        rw [hA, Fintype.card_subtype]
      -- `A.card = ∑_{y ∈ S} fsz g y`
      have hAsum : (A.card : ℝ) = S.sum (fun y => (fsz g y : ℝ)) := by
        rw [hA, Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ.filter (fun a => g a ∈ S))) (t := S) (f := g)
          (by intro a ha; simpa using ha)]
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl (fun y hy => ?_)
        have hfil : (Finset.univ.filter (fun a => g a ∈ S)).filter (fun a => g a = y)
            = Finset.univ.filter (fun a => g a = y) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨-, h⟩; exact h
          · intro h; exact ⟨h ▸ hy, h⟩
        rw [fsz_eq_card_subtype, Fintype.card_subtype, hfil]
      -- bound
      have hbound : S.sum (fun y => (fsz g y : ℝ)) ≤ (N : ℝ) / 2 := by
        have hmpos : (0:ℝ) < (m:ℝ) := by
          rw [hm]; exact_mod_cast hYpos (Fin.last n)
        have hb : ∀ y ∈ S, (fsz g y : ℝ) ≤ (N : ℝ) / (2 * m) := by
          intro y hy
          simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [le_div_iff₀ (by positivity)]
          have hle : fsz g y * (2 * m) ≤ N := by rw [mul_comm]; exact Nat.le_of_lt hy
          have hthis : (fsz g y : ℝ) * (2 * (m:ℝ)) ≤ (N:ℝ) := by exact_mod_cast hle
          simpa [mul_comm, mul_left_comm, mul_assoc] using hthis
        have hcardS : ((S.card : ℝ)) ≤ (m : ℝ) := by
          rw [hS, hm]
          exact_mod_cast Finset.card_filter_le (Finset.univ : Finset (Y (Fin.last n)))
            (fun y => 2 * m * fsz g y < N)
        calc S.sum (fun y => (fsz g y : ℝ)) ≤ S.sum (fun _ => ((N : ℝ) / (2 * m))) :=
              Finset.sum_le_sum hb
          _ = (S.card : ℝ) * ((N : ℝ) / (2 * m)) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (m : ℝ) * ((N : ℝ) / (2 * m)) := by gcongr
          _ = (N : ℝ) / 2 := by
              have : (0:ℝ) < m := by exact_mod_cast hYpos (Fin.last n)
              field_simp
      -- decompose `N`
      have hsum : (N : ℝ) = (Fintype.card Xp : ℝ) + (Fintype.card {a : X // g a ∈ S} : ℝ) := by
        have h1 : Fintype.card X = Fintype.card {a : X // g a ∈ S} + Fintype.card {a : X // g a ∉ S} := by
          have hsub := Fintype.card_subtype_compl (α := X) (fun a => g a ∈ S)
          have hle : Fintype.card {a : X // g a ∈ S} ≤ Fintype.card X :=
            Fintype.card_subtype_le _
          omega
        have h2 : Fintype.card Xp = Fintype.card {a : X // g a ∉ S} := rfl
        rw [hN, h2]
        rw [h1]
        push_cast
        ring
      rw [hsum, hAcard]
      linarith
    -- 2. the extension count
    have hcardExt : (Fintype.card (Ext (X := X) (n := n) (Y := Y) (f := f)
        (Subtype.val : Xp → X)) : ℝ)
        = ∑ y : Good (X := Xp) n (fun j => Y j.castSucc) (fun j a => f j.castSucc a.val),
            (fsz g (g (y.val (Fin.last n)).val) : ℝ) := by
      change (Fintype.card (Sigma fun y : Good (X := Xp) n (fun j => Y j.castSucc)
          (fun j a => f j.castSucc a.val) =>
            {c : X // f (Fin.last n) c = f (Fin.last n) (↑(y.val (Fin.last n)))}) : ℝ) = _
      rw [Fintype.card_sigma]
      push_cast
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [fsz_eq_card_subtype]
    have hGs : G = ∑ _y : Good (X := Xp) n (fun j => Y j.castSucc)
        (fun j a => f j.castSucc a.val), (1:ℝ) := by
      rw [hG]; simp
    have hGN : G * (N : ℝ) ≤ 2 * (m : ℝ) *
        (Fintype.card (Ext (X := X) (n := n) (Y := Y) (f := f) (Subtype.val : Xp → X)) : ℝ) := by
      calc G * (N : ℝ)
          = (∑ _y : Good (X := Xp) n (fun j => Y j.castSucc)
              (fun j a => f j.castSucc a.val), (1:ℝ)) * (N : ℝ) := by rw [hGs]
        _ = ∑ _y : Good (X := Xp) n (fun j => Y j.castSucc)
              (fun j a => f j.castSucc a.val), (N : ℝ) := by
              rw [Finset.sum_mul]; simp
        _ ≤ ∑ y : Good (X := Xp) n (fun j => Y j.castSucc) (fun j a => f j.castSucc a.val),
              (2 * (m : ℝ)) * (fsz g (g (y.val (Fin.last n)).val) : ℝ) := by
              apply Finset.sum_le_sum
              intro y _
              exact hpop (y.val (Fin.last n))
        _ = (2 * (m : ℝ)) * (∑ y : Good (X := Xp) n (fun j => Y j.castSucc)
              (fun j a => f j.castSucc a.val), (fsz g (g (y.val (Fin.last n)).val) : ℝ)) := by
              rw [Finset.mul_sum]
        _ = (2 * (m : ℝ)) * (Fintype.card (Ext (X := X) (n := n) (Y := Y) (f := f)
              (Subtype.val : Xp → X)) : ℝ) := by rw [hcardExt]
    -- 3. the injection
    have hinj : (Fintype.card (Ext (X := X) (n := n) (Y := Y) (f := f)
        (Subtype.val : Xp → X)) : ℝ) ≤ SG := by
      rw [hSG]
      have := Fintype.card_le_of_injective
        (extToGood (X := X) (n := n) (Y := Y) (f := f) (Subtype.val : Xp → X))
        (extToGood_injective (Subtype.val : Xp → X) Subtype.val_injective)
      exact_mod_cast this
    -- 4. IH
    have hIH' : (Fintype.card Xp : ℝ) ^ (n + 1) ≤ KT n * G * Pn := by
      rw [hG, hPn]
      exact hIH
    -- 5. product identity
    have hprodeq : (∏ i : Fin (n + 1), (Fintype.card (Y i) : ℝ)) = Pn * (m : ℝ) := by
      rw [Fin.prod_univ_castSucc, hPn, hm]
    -- 6. assemble
    have hmain : (N : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (n + 1) * KT n * G * Pn := by
      calc (N : ℝ) ^ (n + 1) ≤ (2 * (Fintype.card Xp : ℝ)) ^ (n + 1) := by gcongr
        _ = (2 : ℝ) ^ (n + 1) * (Fintype.card Xp : ℝ) ^ (n + 1) := by rw [mul_pow]
        _ ≤ (2 : ℝ) ^ (n + 1) * (KT n * G * Pn) := by
            have h2 : (0:ℝ) ≤ (2:ℝ) ^ (n+1) := by positivity
            have hK := KT_pos n
            nlinarith [hIH', h2, hK.le, mul_nonneg hK.le (by positivity : (0:ℝ) ≤ G)]
        _ = (2 : ℝ) ^ (n + 1) * KT n * G * Pn := by ring
    have hfin : (N : ℝ) ^ (n + 2) ≤ (2 : ℝ) ^ (n + 2) * KT n * SG * (Pn * (m : ℝ)) := by
      have h1 : (N : ℝ) ^ (n + 2) = (N : ℝ) ^ (n + 1) * N := by ring
      rw [h1]
      calc (N : ℝ) ^ (n + 1) * N ≤ ((2 : ℝ) ^ (n + 1) * KT n * G * Pn) * N := by
            have hNnn : (0:ℝ) ≤ N := by positivity
            gcongr
        _ = ((2 : ℝ) ^ (n + 1) * KT n * Pn) * (G * N) := by ring
        _ ≤ ((2 : ℝ) ^ (n + 1) * KT n * Pn) * (2 * (m : ℝ) * SG) := by
            have hcoef : (0:ℝ) ≤ (2 : ℝ) ^ (n + 1) * KT n * Pn :=
              mul_nonneg (mul_nonneg (by positivity) (KT_pos n).le) hPnnn
            have h2 : G * (N:ℝ) ≤ 2 * (m:ℝ) * SG := by
              calc G * (N:ℝ) ≤ 2 * (m:ℝ) * (Fintype.card (Ext (X := X) (n := n) (Y := Y)
                    (f := f) (Subtype.val : Xp → X)) : ℝ) := hGN
                _ ≤ 2 * (m:ℝ) * SG := by
                    have hmnn : (0:ℝ) ≤ (m:ℝ) := by positivity
                    gcongr
            nlinarith [hcoef, h2, mul_nonneg hcoef (by positivity : (0:ℝ) ≤ G * (N:ℝ))]
        _ = (2 : ℝ) ^ (n + 2) * KT n * SG * (Pn * (m : ℝ)) := by ring
    -- replace the step constant by `KT (n+1)`
    have hfinal : (N : ℝ) ^ (n + 2) ≤ KT (n + 1) * SG * (Pn * (m : ℝ)) := by
      have hstep := KT_step n
      have hSGnn : (0:ℝ) ≤ SG := by rw [hSG]; positivity
      have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
      have hPm : (0:ℝ) ≤ Pn * (m:ℝ) := mul_nonneg hPnnn hmnn
      calc (N : ℝ) ^ (n + 2) ≤ (2 : ℝ) ^ (n + 2) * KT n * SG * (Pn * (m : ℝ)) := hfin
        _ = ((2 : ℝ) ^ (n + 2) * KT n) * (SG * (Pn * (m : ℝ))) := by ring
        _ ≤ KT (n + 1) * (SG * (Pn * (m : ℝ))) := by gcongr
        _ = KT (n + 1) * SG * (Pn * (m : ℝ)) := by ring
    rw [hprodeq]
    exact hfinal

end Lossy

/-! ### Tensor power trick and the final theorem -/

section Final

variable {k : ℕ} {Y : Fin k → Type} [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
  {f : (i : Fin k) → X → Y i}

/-- Currying equivalence for the `M`-fold product problem. -/
def curryGood (M : ℕ) :
    Good (X := Fin M → X) k (fun i => Fin M → Y i) (fun i x j => f i (x j)) ≃
      (Fin M → Good (X := X) k Y f) where
  toFun x := fun j => ⟨fun i => x.val i j, fun i => congrFun (x.prop i) j⟩
  invFun z := ⟨fun i j => (z j).val i, fun i => funext (fun j => (z j).prop i)⟩
  left_inv x := by
    apply Subtype.ext; funext i j; rfl
  right_inv z := by
    funext j; apply Subtype.ext; funext i; rfl

lemma card_good_prod (M : ℕ) :
    Fintype.card (Good (X := Fin M → X) k (fun i => Fin M → Y i) (fun i x j => f i (x j)))
      = (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f)) ^ M := by
  rw [Fintype.card_congr (curryGood (Y := Y) (f := f) M)]
  simp

/-- The counting lemma without loss. -/
theorem key_real (hN : 0 < Fintype.card X) :
    (Fintype.card X : ℝ) ^ (k + 1) ≤ (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) : ℝ) *
      ∏ i, (Fintype.card (Y i) : ℝ) := by
  classical
  have hNpos : (0:ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hN
  have hmpos : ∀ i, (0:ℝ) < (Fintype.card (Y i) : ℝ) := by
    intro i
    have hne : Nonempty X := Fintype.card_pos_iff.mp hN
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨f i hne.some⟩
  set A : ℝ := (Fintype.card X : ℝ)^(k+1) with hA
  set B : ℝ := (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) : ℝ) *
    ∏ i, (Fintype.card (Y i) : ℝ) with hB
  have hApos : 0 < A := by rw [hA]; positivity
  -- a uniform bound for all tensor powers
  have key : ∀ M : ℕ, A^M ≤ KT k * B^M := by
    intro M
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      simp only [pow_zero, mul_one]
      exact KT_ge_one k
    · have h := lossyB k (Fin M → X) (fun i => Fin M → Y i) (fun i x j => f i (x j))
      have hNm : (Fintype.card (Fin M → X) : ℝ) = (Fintype.card X : ℝ)^M := by simp
      have hmM : ∀ i, (Fintype.card (Fin M → Y i) : ℝ) = (Fintype.card (Y i) : ℝ)^M := by
        intro i; simp
      have hS : (Fintype.card (Good (X := Fin M → X) k (fun i => Fin M → Y i)
          (fun i x j => f i (x j))) : ℝ) = ((Fintype.card (ArithmeticKakeya.Good (X := X) k Y f)) ^ M : ℕ) := by
        rw [card_good_prod]
      simp only [hNm, hmM, Finset.prod_pow, hS] at h
      push_cast at h
      have hleft : ((Fintype.card X : ℝ)^M)^(k+1) = A^M := by
        rw [hA, ← pow_mul, ← pow_mul, mul_comm]
      rw [hleft] at h
      have hKeq : KT k * (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) : ℝ)^M *
          (∏ i, (Fintype.card (Y i) : ℝ))^M = KT k * B^M := by
        rw [hB, mul_pow]
        ring
      rw [hKeq] at h
      exact h
  by_cases hle : A ≤ B
  · rw [hA, hB] at hle
    exact hle
  push_neg at hle
  exfalso
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  set r : ℝ := B / A with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hApos]
    exact hle
  have hkey' : ∀ M : ℕ, A^M ≤ KT k * (r^M * A^M) := by
    intro M
    have h := key M
    have hBA : B = r * A := by
      rw [hr]; field_simp
    rw [hBA, mul_pow] at h
    exact h
  have hb : ∀ M : ℕ, 1 / KT k ≤ r^M := by
    intro M
    have h := hkey' M
    have hAM : (0:ℝ) < A^M := by positivity
    have hK := KT_pos k
    have h2 : A^M ≤ KT k * r^M * A^M := by
      calc A^M ≤ KT k * (r^M * A^M) := h
        _ = KT k * r^M * A^M := by ring
    have h3 : A^M / A^M ≤ (KT k * r^M * A^M) / A^M := by gcongr
    rw [div_self (ne_of_gt hAM)] at h3
    have h4 : (KT k * r^M * A^M) / A^M = KT k * r^M := by field_simp
    rw [h4] at h3
    rw [div_le_iff₀ hK]
    linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < 1 / KT k by rw [one_div]; exact inv_pos.mpr (KT_pos k)) hr1
  have := hb M
  linarith

end Final

end ArithmeticKakeya

/-- **Katz--Tao counting lemma**. -/
theorem solution
    (X : Type) [Fintype X] [DecidableEq X]
    (k : ℕ) (Y : Fin k → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (f : (i : Fin k) → X → Y i) (M : Fin k → ℕ)
    (hM : ∀ i, Fintype.card (Y i) ≤ M i) :
    Fintype.card X ^ (k + 1) ≤
      Fintype.card { x : Fin (k + 1) → X // ∀ i : Fin k, f i (x i.castSucc) = f i (x i.succ) } *
        Finset.univ.prod M := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hN | hN
  · rw [hN]; simp
  have hkey := ArithmeticKakeya.key_real (X := X) (k := k) (Y := Y) (f := f) hN
  have hprod_le : (∏ i, (Fintype.card (Y i) : ℝ)) ≤ ∏ i, (M i : ℝ) := by
    apply Finset.prod_le_prod
    · intro i _; positivity
    · intro i _; exact_mod_cast hM i
  have hmain : (Fintype.card X : ℝ) ^ (k + 1) ≤
      (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) : ℝ) * ∏ i, (M i : ℝ) := by
    calc (Fintype.card X : ℝ) ^ (k + 1)
        ≤ (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) : ℝ) *
            ∏ i, (Fintype.card (Y i) : ℝ) := hkey
      _ ≤ (Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) : ℝ) * ∏ i, (M i : ℝ) := by
          apply mul_le_mul_of_nonneg_left hprod_le
          positivity
  have hmain' : ((Fintype.card X ^ (k + 1) : ℕ) : ℝ) ≤
      ((Fintype.card (ArithmeticKakeya.Good (X := X) k Y f) * Finset.univ.prod M : ℕ) : ℝ) := by
    push_cast
    exact hmain
  exact_mod_cast hmain'
