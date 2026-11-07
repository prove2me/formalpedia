-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
-- name    : QEC_Coding_ExpanderCodes_FourSquareTheta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:35:09.609602+00:00
-- url     : https://prove2.me/theorems/175bbed1-659b-4f11-8a94-9e1dbcf0d865
-- title:
--   Four Square Theta
-- statement:
--   Definitions and structural lemmas for Four Square Theta, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Finset
noncomputable def integerSquareRoots (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun z => z ^ 2 = n
theorem mem_integerSquareRoots_iff (n : ℕ) (z : ℤ) :
    z ∈ integerSquareRoots n ↔ z ^ 2 = n := by
  rw [integerSquareRoots, Finset.mem_filter]
  refine and_iff_right_of_imp fun hz => ?_
  simp only [Finset.mem_Icc]
  have hn : (0 : ℤ) ≤ n := by positivity
  constructor
  · by_cases h : 0 ≤ z
    · omega
    · have hle : -z ≤ (-z) ^ 2 := by
        nlinarith [sq_nonneg (-z - 1)]
      nlinarith
  · by_cases h : z ≤ 0
    · omega
    · have hle : z ≤ z ^ 2 := by
        nlinarith [sq_nonneg (z - 1)]
      nlinarith
@[simp] theorem integerSquareRoots_zero :
    integerSquareRoots 0 = {0} := by
  ext z
  rw [mem_integerSquareRoots_iff]
  simp
@[simp] theorem card_integerSquareRoots_zero :
    (integerSquareRoots 0).card = 1 := by
  simp
noncomputable def integerThetaSeries : PowerSeries ℕ :=
  PowerSeries.mk fun n => (integerSquareRoots n).card
@[simp] theorem coeff_integerThetaSeries (n : ℕ) :
    PowerSeries.coeff n integerThetaSeries = (integerSquareRoots n).card := by
  simp [integerThetaSeries]
@[simp] theorem coeff_integerThetaSeries_zero :
    PowerSeries.coeff 0 integerThetaSeries = 1 := by
  simp
abbrev IntegerThetaFourWitness (n : ℕ) :=
  Σ l : {l : Fin 4 →₀ ℕ // l ∈ Finset.finsuppAntidiag Finset.univ n},
    (i : Fin 4) → {z : ℤ // z ∈ integerSquareRoots (l.1 i)}
def lpsQuaternionEquivFinFour : LPSQuaternion ≃ (Fin 4 → ℤ) where
  toFun t := ![t.a, t.b, t.c, t.d]
  invFun f := ⟨f 0, f 1, f 2, f 3⟩
  left_inv t := by cases t; rfl
  right_inv f := by funext i; fin_cases i <;> rfl
@[simp] theorem lpsQuaternionEquivFinFour_norm (t : LPSQuaternion) :
    ∑ i, (lpsQuaternionEquivFinFour t i) ^ 2 = t.norm := by
  simp [lpsQuaternionEquivFinFour, LPSQuaternion.norm, Fin.sum_univ_four]
noncomputable def integerThetaFourWitnessToFullShell
    {n : ℕ} (hn : 0 < n) :
    IntegerThetaFourWitness n → {t // t ∈ lpsQuaternionFullShell n} :=
  fun w => ⟨lpsQuaternionEquivFinFour.symm (fun i => (w.2 i).1),
    (mem_lpsQuaternionFullShell_iff hn _).mpr <| by
      have hs := (Finset.mem_finsuppAntidiag.mp w.1.2).1
      have hi (i : Fin 4) : ((w.2 i).1 : ℤ) ^ 2 = w.1.1 i :=
        (mem_integerSquareRoots_iff _ _).mp (w.2 i).2
      rw [← lpsQuaternionEquivFinFour_norm]
      simp only [Equiv.apply_symm_apply]
      calc
        ∑ i, (w.2 i).1 ^ 2 = ∑ i, (w.1.1 i : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hi i
        _ = n := by
          exact_mod_cast hs⟩
noncomputable def integerThetaFourWitnessEquivFullShell
    {n : ℕ} (hn : 0 < n) :
    IntegerThetaFourWitness n ≃ {t // t ∈ lpsQuaternionFullShell n} :=
  Equiv.ofBijective (integerThetaFourWitnessToFullShell hn) <| by
    constructor
    · rintro ⟨l, z⟩ ⟨l', z'⟩ h
      have hz : (fun i => (z i).1) = fun i => (z' i).1 := by
        apply lpsQuaternionEquivFinFour.symm.injective
        exact congrArg Subtype.val h
      have hl : l = l' := by
        apply Subtype.ext
        apply Finsupp.ext
        intro i
        have hzi := congrFun hz i
        have hi := (mem_integerSquareRoots_iff _ _).mp (z i).2
        have hi' := (mem_integerSquareRoots_iff _ _).mp (z' i).2
        exact_mod_cast hi.symm.trans ((congrArg (fun x : ℤ => x ^ 2) hzi).trans hi')
      subst l'
      congr
      funext i
      apply Subtype.ext
      exact congrFun hz i
    · intro t
      let f : Fin 4 → ℤ := lpsQuaternionEquivFinFour t.1
      let l : Fin 4 →₀ ℕ :=
        Finsupp.equivFunOnFinite.symm fun i => (f i).natAbs ^ 2
      have hNorm : t.1.norm = n :=
        (mem_lpsQuaternionFullShell_iff hn t.1).mp t.2
      have hSum : ∑ i, l i = n := by
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        simp only [l, Finsupp.coe_equivFunOnFinite_symm]
        simpa [f, lpsQuaternionEquivFinFour_norm] using hNorm
      have hl : l ∈ Finset.finsuppAntidiag Finset.univ n := by
        rw [Finset.mem_finsuppAntidiag]
        exact ⟨by simpa using hSum, by simp⟩
      let z : (i : Fin 4) → {x : ℤ // x ∈ integerSquareRoots (l i)} :=
        fun i => ⟨f i, (mem_integerSquareRoots_iff _ _).mpr <| by
          simp [l]⟩
      refine ⟨⟨⟨l, hl⟩, z⟩, ?_⟩
      apply Subtype.ext
      exact lpsQuaternionEquivFinFour.symm_apply_apply t.1
noncomputable def jacobiFourSquareSeries : PowerSeries ℕ :=
  PowerSeries.mk fun n =>
    if n = 0 then 1
    else 8 * ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d
end QEC.Coding.TannerLiftedProduct


