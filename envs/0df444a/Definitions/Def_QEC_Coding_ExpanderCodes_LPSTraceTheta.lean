-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
-- name    : QEC_Coding_ExpanderCodes_LPSTraceTheta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:37:59.170756+00:00
-- url     : https://prove2.me/theorems/6f7d4ca9-ca54-4923-a13c-2991eef452f7
-- title:
--   LPSTrace Theta
-- statement:
--   Definitions and structural lemmas for LPSTrace Theta, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceTheta.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Finset
noncomputable def scaledIntegerSquareRoots (m n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun z =>
    ((m : ℤ) ^ 2) * z ^ 2 = n
theorem mem_scaledIntegerSquareRoots_iff
    {m : ℕ} (hm : 0 < m) (n : ℕ) (z : ℤ) :
    z ∈ scaledIntegerSquareRoots m n ↔
      ((m : ℤ) ^ 2) * z ^ 2 = n := by
  rw [scaledIntegerSquareRoots, Finset.mem_filter]
  refine and_iff_right_of_imp fun hz => ?_
  simp only [Finset.mem_Icc]
  have hmOne : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hmSq : (1 : ℤ) ≤ (m : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℤ) - 1)]
  have hzSq : z ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg z]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (z + n)]
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (z - n)]
noncomputable def scaledIntegerThetaSeries (m : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun n => (scaledIntegerSquareRoots m n).card
@[simp] theorem coeff_scaledIntegerThetaSeries (m n : ℕ) :
    PowerSeries.coeff n (scaledIntegerThetaSeries m) =
      (scaledIntegerSquareRoots m n).card := by
  simp [scaledIntegerThetaSeries]
noncomputable def lpsTraceCoordinateRoots
    (q : ℕ) (i : Fin 4) (n : ℕ) : Finset ℤ :=
  if i = 0 then integerSquareRoots n
  else scaledIntegerSquareRoots (2 * q) n
noncomputable def lpsTraceCoordinateThetaSeries
    (q : ℕ) (i : Fin 4) : PowerSeries ℕ :=
  PowerSeries.mk fun n => (lpsTraceCoordinateRoots q i n).card
@[simp] theorem coeff_lpsTraceCoordinateThetaSeries
    (q : ℕ) (i : Fin 4) (n : ℕ) :
    PowerSeries.coeff n (lpsTraceCoordinateThetaSeries q i) =
      (lpsTraceCoordinateRoots q i n).card := by
  simp [lpsTraceCoordinateThetaSeries]
def lpsTraceCoordinateValue (q : ℕ) (i : Fin 4) (z : ℤ) : ℤ :=
  if i = 0 then z ^ 2 else ((2 * q : ℕ) : ℤ) ^ 2 * z ^ 2
theorem mem_lpsTraceCoordinateRoots_iff
    {q : ℕ} (hq : 0 < q) (i : Fin 4) (n : ℕ) (z : ℤ) :
    z ∈ lpsTraceCoordinateRoots q i n ↔
      lpsTraceCoordinateValue q i z = n := by
  by_cases hi : i = 0
  · subst i
    simp [lpsTraceCoordinateRoots, lpsTraceCoordinateValue,
      mem_integerSquareRoots_iff]
  · simp [lpsTraceCoordinateRoots, lpsTraceCoordinateValue, hi,
      mem_scaledIntegerSquareRoots_iff (by omega : 0 < 2 * q)]
@[simp] theorem sum_lpsTraceCoordinateValue
    (q : ℕ) (t : LPSQuaternion) :
    ∑ i : Fin 4,
        lpsTraceCoordinateValue q i (lpsQuaternionEquivFinFour t i) =
      lpsTraceQuadraticForm q t := by
  simp [lpsTraceCoordinateValue, lpsQuaternionEquivFinFour,
    lpsTraceQuadraticForm, Fin.sum_univ_four]
abbrev LPSTraceThetaWitness (q n : ℕ) :=
  Σ l : {l : Fin 4 →₀ ℕ // l ∈ Finset.finsuppAntidiag Finset.univ n},
    (i : Fin 4) → {z : ℤ // z ∈ lpsTraceCoordinateRoots q i (l.1 i)}
noncomputable def lpsTraceThetaWitnessToShell
    {q n : ℕ} (hq : 0 < q) :
    LPSTraceThetaWitness q n → {t // t ∈ lpsTraceQuadraticShell q n} :=
  fun w => ⟨lpsQuaternionEquivFinFour.symm (fun i => (w.2 i).1),
    (mem_lpsTraceQuadraticShell_iff hq _).mpr <| by
      have hs := (Finset.mem_finsuppAntidiag.mp w.1.2).1
      have hi (i : Fin 4) :
          lpsTraceCoordinateValue q i (w.2 i).1 = w.1.1 i :=
        (mem_lpsTraceCoordinateRoots_iff hq i _ _).mp (w.2 i).2
      rw [← sum_lpsTraceCoordinateValue]
      simp only [Equiv.apply_symm_apply]
      calc
        ∑ i, lpsTraceCoordinateValue q i (w.2 i).1 =
            ∑ i, (w.1.1 i : ℤ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hi i
        _ = n := by exact_mod_cast hs⟩
noncomputable def lpsTraceThetaWitnessEquivShell
    {q n : ℕ} (hq : 0 < q) :
    LPSTraceThetaWitness q n ≃ {t // t ∈ lpsTraceQuadraticShell q n} :=
  Equiv.ofBijective (lpsTraceThetaWitnessToShell hq) <| by
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
        have hi := (mem_lpsTraceCoordinateRoots_iff hq i _ _).mp (z i).2
        have hi' := (mem_lpsTraceCoordinateRoots_iff hq i _ _).mp (z' i).2
        exact_mod_cast hi.symm.trans
          ((congrArg (lpsTraceCoordinateValue q i) hzi).trans hi')
      subst l'
      congr
      funext i
      apply Subtype.ext
      exact congrFun hz i
    · intro t
      let f : Fin 4 → ℤ := lpsQuaternionEquivFinFour t.1
      let l : Fin 4 →₀ ℕ :=
        Finsupp.equivFunOnFinite.symm fun i =>
          (lpsTraceCoordinateValue q i (f i)).natAbs
      have hForm : lpsTraceQuadraticForm q t.1 = n :=
        (mem_lpsTraceQuadraticShell_iff hq t.1).mp t.2
      have hNonneg (i : Fin 4) :
          0 ≤ lpsTraceCoordinateValue q i (f i) := by
        simp [lpsTraceCoordinateValue]
        positivity
      have hSum : ∑ i, l i = n := by
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        simp only [l, Finsupp.coe_equivFunOnFinite_symm,
          Int.natCast_natAbs, abs_of_nonneg (hNonneg _)]
        simpa [f, sum_lpsTraceCoordinateValue] using hForm
      have hl : l ∈ Finset.finsuppAntidiag Finset.univ n := by
        rw [Finset.mem_finsuppAntidiag]
        exact ⟨by simpa using hSum, by simp⟩
      let z : (i : Fin 4) →
          {x : ℤ // x ∈ lpsTraceCoordinateRoots q i (l i)} :=
        fun i => ⟨f i, (mem_lpsTraceCoordinateRoots_iff hq i _ _).mpr <| by
          change lpsTraceCoordinateValue q i (f i) =
            ((lpsTraceCoordinateValue q i (f i)).natAbs : ℤ)
          rw [Int.natCast_natAbs, abs_of_nonneg (hNonneg i)]⟩
      refine ⟨⟨⟨l, hl⟩, z⟩, ?_⟩
      apply Subtype.ext
      exact lpsQuaternionEquivFinFour.symm_apply_apply t.1
end QEC.Coding.TannerLiftedProduct


