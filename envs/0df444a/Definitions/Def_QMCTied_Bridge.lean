-- Prove2me | Definitions.Def_QMCTied_Bridge
-- name    : QMCTied_Bridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:19:06.965041+00:00
-- url     : https://prove2.me/theorems/23c63ed9-f9d1-4c3e-bcb7-b1f990a34291
-- title:
--   The guarded table program computes the integer iteration
-- statement:
--   If the program's tables represent a tied-entry instance and the size guards are long enough, the outer loop returns the table of class values of the iterate $\lambda^{(T)}$ and the best recorded value of the integer iteration.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Fold
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_Iter
import Definitions.Def_QMCSub_Bridge1
import Definitions.Def_QMCSub_Bridge2
import Definitions.Def_QMCTied_Defs
import Definitions.Def_QMCTied_Core
import Definitions.Def_QMCTied_Prog

/-!
The guarded table program computes the integer iteration of a tied-entry SDP instance whenever
its tables represent the instance and the size guards are large enough.
-/

namespace QMCTied
open Matrix QMCSub
open scoped BigOperators

variable {N : ℕ} {κ : Type} [DecidableEq κ]

/-- The table of class values of `lam`, as a list matrix. -/
def tabOf (I : Inst N κ) (lam : κ → ℤ) : Mat :=
  toM (Matrix.of fun i j : Fin N => lam (I.cls i j))

omit [DecidableEq κ] in
theorem gm_tabOf (I : Inst N κ) (lam : κ → ℤ) (i j : Fin N) :
    gm (tabOf I lam) i.val j.val = (lam (I.cls i j) : ℚ) :=
  gm_toM (Matrix.of fun i j : Fin N => lam (I.cls i j)) i j

/-- The static data of the table program for an instance. -/
abbrev stT (I : Inst N κ) (P : Par) (clsT sgnT gCT csT : Mat) (fK pI pO : List Unit) : ST :=
  (List.range N, clsT, sgnT, gCT, csT, fK, pI, pO,
    [(P.D : ℚ), P.eta, (P.dN : ℚ), (P.D2 : ℚ), I.c0])

theorem qrnd_eq (q : ℚ) : qrnd q = ((rnd q : ℤ) : ℚ) := by
  unfold qrnd rnd
  split_ifs with h
  · rw [qfloor_eq_floor _ (by linarith), Int.cast_neg]
  · rw [qfloor_eq_floor _ (not_lt.mp h)]

theorem clampQ_eq (D x : ℤ) (hD : 0 ≤ D) :
    clampQ (D : ℚ) (x : ℚ) = ((clampZ D x : ℤ) : ℚ) := by
  unfold clampQ clampZ
  by_cases h1 : x < -D
  · have h1' : (x : ℚ) < -(D : ℚ) := by exact_mod_cast h1
    rw [if_pos h1', min_eq_right (show x ≤ D by omega), max_eq_left (show x ≤ -D by omega),
      Int.cast_neg]
  · have h1' : ¬ (x : ℚ) < -(D : ℚ) := by
      intro h
      apply h1
      exact_mod_cast h
    rw [if_neg h1']
    by_cases h2 : D < x
    · have h2' : (D : ℚ) < (x : ℚ) := by exact_mod_cast h2
      rw [if_pos h2', min_eq_left (show D ≤ x by omega), max_eq_right (show -D ≤ D by omega)]
    · have h2' : ¬ (D : ℚ) < (x : ℚ) := by
        intro h
        apply h2
        exact_mod_cast h
      rw [if_neg h2', min_eq_right (show x ≤ D by omega), max_eq_right (show -D ≤ x by omega)]

theorem clampZ_natAbs (D x : ℤ) (hD : 0 ≤ D) : (clampZ D x).natAbs ≤ D.natAbs := by
  unfold clampZ
  omega

theorem maxQ_eq (a b : ℚ) : maxQ a b = max a b := by
  unfold maxQ
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (not_lt.mp h)).symm

omit [DecidableEq κ] in
theorem shiftT_tab (I : Inst N κ) (sgnT : Mat)
    (hsgn : ∀ i j : Fin N, gm sgnT i j = (I.sgn i j : ℚ)) (D : ℤ) (lam : κ → ℤ) :
    shiftT (List.range N) sgnT (D : ℚ) (tabOf I lam) = toM (Mz I D lam) := by
  show (List.range N).map (fun i => (List.range N).map (fun j =>
      (if i = j then ((List.range N).length : ℚ) * (D : ℚ) else 0) -
        gm sgnT i j * gm (tabOf I lam) i j)) =
    List.ofFn (fun i : Fin N => List.ofFn (fun j : Fin N => ((Mz I D lam i j : ℤ) : ℚ)))
  apply map_range_congr
  intro i
  apply map_range_congr
  intro j
  rw [hsgn, gm_tabOf, List.length_range]
  unfold Mz Ghat
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
    simp [h, h']

theorem gQT_tab (I : Inst N κ) (clsT sgnT : Mat)
    (hsgn : ∀ i j : Fin N, gm sgnT i j = (I.sgn i j : ℚ))
    (hcls : ∀ i j i' j' : Fin N, gm clsT i j = gm clsT i' j' ↔ I.cls i j = I.cls i' j')
    (Q : Matrix (Fin N) (Fin N) ℤ) (i j : Fin N) :
    gQT (List.range N) clsT sgnT (toM Q) i j =
      ((∑ i', ∑ j', if I.cls i' j' = I.cls i j then I.sgn i' j' * Q i' j' else 0 : ℤ) : ℚ) := by
  unfold gQT
  rw [sum_range_congr N
    (fun i' => ((List.range N).map (fun j' =>
      if gm clsT i' j' = gm clsT i j then gm sgnT i' j' * gm (toM Q) i' j' else 0)).sum)
    (fun i' : Fin N => ∑ j' : Fin N,
      if I.cls i' j' = I.cls i j then ((I.sgn i' j' : ℤ) : ℚ) * ((Q i' j' : ℤ) : ℚ) else 0)
    (fun i' => sum_range_congr N
      (fun j' => if gm clsT i' j' = gm clsT i j then gm sgnT i' j' * gm (toM Q) i' j' else 0) _
      (fun j' => by
        rw [hsgn, gm_toM]
        by_cases h : I.cls i' j' = I.cls i j
        · rw [if_pos h, if_pos ((hcls i' j' i j).mpr h)]
        · rw [if_neg h, if_neg (fun e => h ((hcls i' j' i j).mp e))]))]
  push_cast
  rfl

/-- One guarded step of the table program is one step of the integer iteration. -/
theorem stepO_tab (I : Inst N κ) (hI : I.Good) (P : Par)
    (clsT sgnT gCT csT : Mat) (fK pI pO : List Unit)
    (hsgn : ∀ i j : Fin N, gm sgnT i j = (I.sgn i j : ℚ))
    (hcls : ∀ i j i' j' : Fin N, gm clsT i j = gm clsT i' j' ↔ I.cls i j = I.cls i' j')
    (hcs : ∀ i j : Fin N, gm csT i j = I.Cs i j)
    (hgC : ∀ i j : Fin N, gm gCT i j = gC I (I.cls i j))
    (hD : 0 < P.D)
    (hfK : fK.length = 2 * P.K) (hpI : 1 ≤ pI.length) (hpO : 1 ≤ pO.length)
    (hfitI : ∀ lam : κ → ℤ, (∀ c, |lam c| ≤ P.D) → ∀ m, m ≤ fK.length → ∀ a b,
      ((Mz I P.D lam ^ m) a b).natAbs < 2 ^ pI.length)
    (hfitD : P.D.natAbs < 2 ^ pO.length) (hfitB : 2 * P.D2 < 2 ^ pO.length)
    (lam : κ → ℤ) (b : ℤ) (hbox : ∀ c, |lam c| ≤ P.D) (hk0 : lam I.k0 = P.D)
    (hb1 : 0 ≤ bestStep I P lam b) (hb2 : bestStep I P lam b ≤ 2 * (P.D2 : ℤ)) :
    stepO (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam, (b : ℚ)) =
      (tabOf I (next I P lam), ((bestStep I P lam b : ℤ) : ℚ)) := by
  have hshift : shiftT (List.range N) sgnT (P.D : ℚ) (tabOf I lam) = toM (Mz I P.D lam) :=
    shiftT_tab I sgnT hsgn P.D lam
  have hpow : powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) =
      toM (Qz I P.D P.K lam) := by
    show matPow (List.range N) (shiftT (List.range N) sgnT (P.D : ℚ) (tabOf I lam)) pI fK = _
    rw [hshift, matPow_toM _ pI fK hpI (hfitI lam hbox), hfK]
    rfl
  have hdiag : diagSum (List.range N)
      (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam)) =
      ((tau I P.D P.K lam : ℤ) : ℚ) := by
    rw [hpow]
    exact diagSum_toM _
  have hlap : lapDot (List.range N) (shiftT (List.range N) sgnT (P.D : ℚ) (tabOf I lam))
      (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam)) =
      ((rnum I P.D P.K lam : ℤ) : ℚ) := by
    rw [hpow, hshift]
    exact lapDot_toM _ _
  have hact : actT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) =
      active I P.D P.K lam := by
    show decide (((List.range N).length : ℚ) * (P.D : ℚ) *
        diagSum (List.range N) (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam)) <
      lapDot (List.range N) (shiftT (List.range N) sgnT (P.D : ℚ) (tabOf I lam))
        (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam))) = _
    rw [hdiag, hlap, List.length_range]
    unfold active
    have e : ((N : ℚ) * (P.D : ℚ) * ((tau I P.D P.K lam : ℤ) : ℚ) <
        ((rnum I P.D P.K lam : ℤ) : ℚ)) ↔
        ((N : ℤ) * P.D * tau I P.D P.K lam < rnum I P.D P.K lam) := by
      norm_cast
    exact decide_eq_decide.mpr e
  have hstep : ∀ i j : Fin N,
      stepT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) i j =
        stepv I P lam (I.cls i j) := by
    intro i j
    show P.eta * (gm gCT i j +
      (if actT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) then
        2 * gQT (List.range N) clsT sgnT
            (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam)) i j /
          diagSum (List.range N) (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam))
        else 0)) = _
    rw [hact, hdiag, hpow, gQT_tab I clsT sgnT hsgn hcls, hgC]
    rfl
  have hnext : nextT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) =
      tabOf I (next I P lam) := by
    show (List.range N).map (fun i => (List.range N).map (fun j =>
        if i = j then capQ pO (gm (tabOf I lam) i j)
        else capQ pO (clampQ (P.D : ℚ) (gm (tabOf I lam) i j +
          qrnd (stepT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) i j))))) =
      List.ofFn (fun i : Fin N => List.ofFn (fun j : Fin N =>
        ((next I P lam (I.cls i j) : ℤ) : ℚ)))
    apply map_range_congr
    intro i
    apply map_range_congr
    intro j
    rw [gm_tabOf, hstep, qrnd_eq]
    by_cases h : i = j
    · subst h
      have hc : I.cls i i = I.k0 := (hI.cls_diag i i).mpr rfl
      rw [if_pos rfl, hc, hk0, capQ_int pO _ hpO hfitD]
      simp [next, hk0]
    · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
      have hc : I.cls i j ≠ I.k0 := fun e => h ((hI.cls_diag i j).mp e)
      have hsum : (lam (I.cls i j) : ℚ) + ((rnd (stepv I P lam (I.cls i j)) : ℤ) : ℚ) =
          ((lam (I.cls i j) + rnd (stepv I P lam (I.cls i j)) : ℤ) : ℚ) := by
        push_cast
        rfl
      rw [if_neg h', hsum, clampQ_eq _ _ hD.le,
        capQ_int pO _ hpO (lt_of_le_of_lt (clampZ_natAbs _ _ hD.le) hfitD)]
      simp [next, hc]
  have haq : aqT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) = aq I P lam := by
    show maxQ 0 (lapDot (List.range N) (shiftT (List.range N) sgnT (P.D : ℚ) (tabOf I lam))
          (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam)) * ((P.dN : ℚ) + 1) /
        (diagSum (List.range N) (powT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam)) *
          ((P.dN : ℚ) - 1)) -
        ((List.range N).length : ℚ) * (P.D : ℚ)) / (P.D : ℚ) = _
    rw [hdiag, hlap, List.length_range, maxQ_eq]
    rfl
  have hobj : objT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) = objq I P lam := by
    show I.c0 + lapDot (List.range N) csT (tabOf I lam) / (P.D : ℚ) = objq I P lam
    unfold lapDot objq
    rw [sum_range_congr N
      (fun i => ((List.range N).map (fun j => gm csT i j * gm (tabOf I lam) i j)).sum)
      (fun i : Fin N => ∑ j : Fin N, I.Cs i j * (lam (I.cls i j) : ℚ))
      (fun i => sum_range_congr N (fun j => gm csT i j * gm (tabOf I lam) i j) _
        (fun j => by rw [hcs, gm_tabOf])), Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
  have hval : valT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) = valq I P lam := by
    show (objT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) +
        aqT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam) * I.c0) /
      (1 + aqT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam)) = _
    rw [hobj, haq]
    rfl
  apply Prod.ext
  · exact hnext
  · show capQ pO (maxQ (b : ℚ) (qfloor ((P.D2 : ℚ) *
        maxQ 0 (valT (stT I P clsT sgnT gCT csT fK pI pO) (tabOf I lam))))) =
      ((bestStep I P lam b : ℤ) : ℚ)
    have hnn : (0 : ℚ) ≤ (P.D2 : ℚ) * max 0 (valq I P lam) :=
      mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
    have hmax : max (b : ℚ) ((⌊(P.D2 : ℚ) * max 0 (valq I P lam)⌋ : ℤ) : ℚ) =
        ((bestStep I P lam b : ℤ) : ℚ) := by
      unfold bestStep
      push_cast
      rfl
    have hfit : (bestStep I P lam b).natAbs < 2 ^ pO.length := by
      have h3 : (bestStep I P lam b).natAbs ≤ 2 * P.D2 := by omega
      exact lt_of_le_of_lt h3 hfitB
    rw [hval, maxQ_eq, maxQ_eq, qfloor_eq_floor _ hnn, hmax, capQ_int pO _ hpO hfit]

/-- The outer loop of the table program is the integer iteration. -/
theorem runT_eq (I : Inst N κ) (hI : I.Good) (P : Par)
    (clsT sgnT gCT csT : Mat) (fK pI pO fT : List Unit)
    (hsgn : ∀ i j : Fin N, gm sgnT i j = (I.sgn i j : ℚ))
    (hcls : ∀ i j i' j' : Fin N, gm clsT i j = gm clsT i' j' ↔ I.cls i j = I.cls i' j')
    (hcs : ∀ i j : Fin N, gm csT i j = I.Cs i j)
    (hgC : ∀ i j : Fin N, gm gCT i j = gC I (I.cls i j))
    (hN : 2 ≤ N) (hD : 0 < P.D) (hdN : 2 ≤ P.dN)
    (hK : (N : ℝ) * (1 - 1 / (P.dN : ℝ)) ^ (2 * P.K) ≤ 1 / (P.dN : ℝ))
    (hfK : fK.length = 2 * P.K) (hpI : 1 ≤ pI.length) (hpO : 1 ≤ pO.length)
    (hfitI : ∀ lam : κ → ℤ, (∀ c, |lam c| ≤ P.D) → ∀ m, m ≤ fK.length → ∀ a b,
      ((Mz I P.D lam ^ m) a b).natAbs < 2 ^ pI.length)
    (hfitD : P.D.natAbs < 2 ^ pO.length) (hfitB : 2 * P.D2 < 2 ^ pO.length) :
    (gfold stepO fT
      ((List.range N, clsT, sgnT, gCT, csT, fK, pI, pO,
          [(P.D : ℚ), P.eta, (P.dN : ℚ), (P.D2 : ℚ), I.c0]),
        (initY (P.D : ℚ) (List.range N), (0 : ℚ)))).2 =
      (tabOf I (lamSeq I P fT.length), ((bestSeq I P fT.length : ℤ) : ℚ)) := by
  rw [gfold_snd]
  have hinit : (initY (P.D : ℚ) (List.range N), (0 : ℚ)) =
      (tabOf I (lamSeq I P 0), ((bestSeq I P 0 : ℤ) : ℚ)) := by
    apply Prod.ext
    · show (List.range N).map (fun i => (List.range N).map (fun j =>
          if i = j then (P.D : ℚ) else 0)) =
        List.ofFn (fun i : Fin N => List.ofFn (fun j : Fin N =>
          ((lam0 I P (I.cls i j) : ℤ) : ℚ)))
      apply map_range_congr
      intro i
      apply map_range_congr
      intro j
      unfold lam0
      by_cases h : i = j
      · subst h
        simp [(hI.cls_diag i i).mpr rfl]
      · have h' : ¬ i.val = j.val := fun e => h (Fin.ext e)
        have hc : I.cls i j ≠ I.k0 := fun e => h ((hI.cls_diag i j).mp e)
        simp [h', hc]
    · simp [bestSeq]
  rw [hinit]
  have key : ∀ k, (stepO (stT I P clsT sgnT gCT csT fK pI pO))^[k]
      (tabOf I (lamSeq I P 0), ((bestSeq I P 0 : ℤ) : ℚ)) =
      (tabOf I (lamSeq I P k), ((bestSeq I P k : ℤ) : ℚ)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        have hl : next I P (lamSeq I P k) = lamSeq I P (k + 1) := by
          unfold lamSeq
          rw [Function.iterate_succ_apply']
        have hbs : bestStep I P (lamSeq I P k) (bestSeq I P k) = bestSeq I P (k + 1) := rfl
        rw [Function.iterate_succ_apply', ih,
          stepO_tab I hI P clsT sgnT gCT csT fK pI pO hsgn hcls hcs hgC hD hfK hpI hpO hfitI
            hfitD hfitB (lamSeq I P k) (bestSeq I P k) (lamSeq_box I P hD.le k)
            (lamSeq_k0 I P k) (by rw [hbs]; exact bestSeq_nonneg I P (k + 1))
            (by rw [hbs]; exact bestSeq_le I hI P hN hD hdN hK (k + 1)),
          hl, hbs]
  exact key _

end QMCTied


