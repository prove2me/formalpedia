-- Prove2me | Definitions.Def_OAIErdos3B196
-- name    : OAIErdos3B196
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T13:26:36.817094+00:00
-- url     : https://prove2.me/theorems/f1251ebf-3fae-4ffc-ac94-d951deb34643
-- title:
--   OpenAI Erdős-3 split, definitions bundle 197 of 207
-- statement:
--   Definitions bundle 197 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B195`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 197 available.
--
--   Modules: `OAI.Erdos3.NativeCorrelationStructure.HasCorrelatedAffineComparison`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_correlated_lower_factorization`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_invariant_native_comparison_model`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_lower_factored_family`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_shared_free_lower_factorization`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_uniform_lower_comparison_model`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.has_correlated_affine_comparison`, `OAI.Erdos3.NativeRankRelation.CommonData.CorrelatedAffineComparison`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_shared_free_common_polynomial_corrections`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_shared_free_full_orbit_factorization`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_sharedFreeFactorFreezing`, `OAI.Erdos3.VectorPolynomial.affine_refined_coefficient_mem`, `OAI.Erdos3.exists_native_correlated_affine_comparison`, `OAI.Erdos3.exists_native_correlated_comparison_budget`, `OAI.Erdos3.exists_sharedFreeCommonCorrectionBudget_bound`, `OAI.Erdos3.exists_sharedFreeCorrelationBudget_bound`, `OAI.Erdos3.exists_sharedFreeFullOrbitBudget_bound`, `OAI.Erdos3.exists_sharedFreePetalLiftBudget_bound`, `OAI.Erdos3.nativeSharedFreeRelationConstant`, `OAI.Erdos3.sharedFreeCorrelationBudget`, `OAI.Erdos3.sharedFreeCorrelationInput`, `OAI.Erdos3.sharedFreeCorrelationInput_bounds`, `OAI.Erdos3.sharedFreeCorrelationInput_le_budget`, `OAI.Erdos3.sharedFreeFactorFreezingConstant`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B197

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeFullOrbitBudget
namespace OAI

section

namespace Erdos3

theorem exists_sharedFreePetalLiftBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreePetalLiftBudget s q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := (4 * X + (X + V (4 * X)) + 3) ^ 7
  let Λ : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let A : Polynomial ℕ := 4 * Polynomial.X + F (Polynomial.X + H Polynomial.X) + Λ
  let T₀ : Polynomial ℕ := (A + 2) ^ 4 + 1
  let T : Polynomial ℕ := (T₀ + 2) ^ 3 + (T₀ + 2) ^ 36 + Λ
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hheight : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hF : fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) ≤
      fourRefinementAnnihilatorBudget (p + coefficientFourHeightBudget p) := by
    unfold fourRefinementAnnihilatorBudget fourRefinementBasisBudget preimageBasisBudget
      sparseGeneratorBudget
    gcongr
  have hA : sharedFreePetalLiftInput s q p ≤ sharedFreePetalLiftInput s p p := by
    unfold sharedFreePetalLiftInput
    linarith
  have hA0 : 0 ≤ sharedFreePetalLiftInput s q p := by
    have h := fourRefinementAnnihilatorBudget_nonneg (add_nonneg hq hheight)
    unfold sharedFreePetalLiftInput
    positivity
  have hupper : sharedFreePetalLiftBudget s q p ≤ sharedFreePetalLiftBudget s p p := by
    dsimp only [sharedFreePetalLiftBudget]
    gcongr
  apply hupper.trans
  simpa [T, T₀, A, Λ, F, V, G, H, R, sharedFreePetalLiftBudget, sharedFreePetalLiftInput,
    coefficientFourHeightBudget, refiltrationCoordinateBudget, fourRefinementAnnihilatorBudget,
    fourRefinementBasisBudget, preimageBasisBudget, sparseGeneratorBudget, Polynomial.eval₂_pow]
      using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem exists_sharedFreeCommonCorrectionBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C := by
  let Λ : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let T₀ : Polynomial ℕ := 2 * Polynomial.X + Λ + 1
  let T : Polynomial ℕ := (T₀ + 2) ^ 3 + (T₀ + 2) ^ 36 + Λ
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hupper : sharedFreeCommonCorrectionBudget s q p ≤
      sharedFreeCommonCorrectionBudget s p p := by
    dsimp only [sharedFreeCommonCorrectionBudget]
    gcongr
  apply hupper.trans
  simpa [T, T₀, Λ, sharedFreeCommonCorrectionBudget, two_mul, Polynomial.eval₂_pow]
    using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem exists_sharedFreeFullOrbitBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ≤ (p + C) ^ C ∧
      sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C ∧
      sharedFreePetalLiftBudget s q p ≤ (p + C) ^ C ∧
      (s : ℝ) * (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p) ≤
        (p + C) ^ C ∧
      Real.exp (sharedFreeCommonCorrectionBudget s q p) + Real.exp (sharedFreePetalLiftBudget s q p) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨c, _hc, hcommon⟩ := exists_sharedFreeCommonCorrectionBudget_bound s
  obtain ⟨v, _hv, hpetal⟩ := exists_sharedFreePetalLiftBudget_bound s
  let Pc : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let Pv : Polynomial ℕ := (Polynomial.X + Polynomial.C v) ^ v
  let Pa : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let T : Polynomial ℕ := Polynomial.C s * (Pc + Pv) + (Pc + Pv + 2) + Pa
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  let Bc := (p + c) ^ c
  let Bv := (p + v) ^ v
  let Λ := (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  have hBc : 0 ≤ Bc := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c)) _
  have hBv : 0 ≤ Bv := pow_nonneg (add_nonneg hp (Nat.cast_nonneg v)) _
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have htotal : (s : ℝ) * (Bc + Bv) + (Bc + Bv + 2) + Λ ≤ (p + C) ^ C := by
    simpa [T, Pc, Pv, Pa, Bc, Bv, Λ, Polynomial.eval₂_pow] using hbound p hp
  have hprod : 0 ≤ (s : ℝ) * (Bc + Bv) := mul_nonneg hs0 (add_nonneg hBc hBv)
  have hplain : Bc + Bv + 2 ≤ (p + C) ^ C := by linarith only [htotal, hprod, hΛ]
  have hc := hcommon q p hq hqp hp
  have hv := hpetal q p hq hqp hp
  change sharedFreeCommonCorrectionBudget s q p ≤ Bc at hc
  change sharedFreePetalLiftBudget s q p ≤ Bv at hv
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hc hv) hs0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Λ ≤ _
    linarith only [htotal, hprod, hBc, hBv]
  · linarith only [hc, hplain, hBv]
  · linarith only [hv, hplain, hBc]
  · linarith only [hscaled, htotal, hBc, hBv, hΛ]
  · calc
      _ ≤ Real.exp Bc + Real.exp Bv :=
        add_le_add (Real.exp_le_exp.mpr hc) (Real.exp_le_exp.mpr hv)
      _ ≤ Real.exp Bc + Real.exp Bc + Real.exp Bv := by linarith only [Real.exp_pos Bc]
      _ ≤ Real.exp (Bc + Bv + 2) := exp_repeated_add_le hBc hBv
      _ ≤ _ := Real.exp_le_exp.mpr hplain

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineRefinedCoefficients
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem affine_refined_coefficient_mem {L ι : Type*} [AddCommGroup L] [Module ℚ L]
    [Fintype ι] {s : ℕ} (C D : Fin s → Submodule ℚ L)
    (K : Fin s → Submodule ℚ (Fin 4 → L))
    (G : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] L))
    (α : Fin s → ℝ ⊗[ℚ] L) (β : ι → Fin s → ℝ ⊗[ℚ] L) (x : ι → ℝ)
    (hG : ∀ d : Fin s, coefficients G (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (C d) (D d) (K d)).map (LinearMap.proj 0)).baseChange ℝ)
    (hα : ∀ d, α d ∈ (D d).baseChange ℝ)
    (hβ : ∀ j d, β j d ∈ (D d).baseChange ℝ) (d : Fin s) :
    coefficients (G + positiveUnivariate (fun d => α d + ∑ j, x j • β j d))
        (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (C d) (D d) (K d)).map (LinearMap.proj 0)).baseChange ℝ := by
  rw [map_add, Finsupp.add_apply, positiveUnivariate_coefficient]
  apply Submodule.add_mem _ (hG d)
  apply Submodule.baseChange_mono ℝ (dependent_le_refined_firstProjection (C d) (D d) (K d))
  exact Submodule.add_mem _ (hα d)
    (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SharedFreeCommonPolynomialCorrections
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_common_polynomial_corrections
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let L := sharedFreeCommonCorrectionBudget s Q P'
    ∃ (m : ℕ) (Γ ε ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
      CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ)) (Real.exp L) ε.log ∧
      CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
      ∀ d : Fin s,
        coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) =
          coefficients Γ.log (Finsupp.single () (d.val + 1)) +
          coefficients ε.log (Finsupp.single () (d.val + 1)) +
          coefficients ρ.log (Finsupp.single () (d.val + 1)) := by
  intro L
  obtain ⟨l, γ, e, q, hdata⟩ := D.exists_shared_free_filtered_common E T hbQ hT F V g hg D'
    hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  obtain ⟨m, hm, hmb, _hdiv, Γ, ε, ρ, hΓ, hε, hρ, hΓ0, hε0, hρ0, hbound, hgrid⟩ :=
    D.exists_native_freeCoefficient_corrections E T hTfil γ e q
      (fun d => (hdata d).2.2.2.1)
      (fun d => (hdata d).2.2.2.2.1)
      (fun d => (hdata d).2.2.2.2.2.1)
      l (fun d => (hdata d).1) (fun d => (hdata d).2.1)
      (fun d => (hdata d).2.2.2.2.2.2.2.1)
      (fun d => (hdata d).2.2.2.2.2.2.2.2)
  refine ⟨m, Γ, ε, ρ, hm, hmb, hΓ0, hε0, hρ0, hbound, hgrid, ?_⟩
  intro d
  rw [hΓ, hε, hρ, positiveUnivariate_coefficient, positiveUnivariate_coefficient,
    positiveUnivariate_coefficient]
  exact ⟨(hdata d).2.2.1, (hdata d).2.2.2.2.2.2.1⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeLowerFactorization
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_full_orbit_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let Lc := sharedFreeCommonCorrectionBudget s Q P'
    let Lv := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) ∧
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
          (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
            ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∃ ε A K U ρ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
              A.log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 K = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                (Real.exp Lc + Real.exp Lv) ε.log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
              ε * A * K * U * ρ = g h ∧
              ∀ d : Fin s,
                coefficients K.log (Finsupp.single () (d.val + 1)) ∈
                  (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
                coefficients U.log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ := by
  intro B Λ Lc Lv
  classical
  obtain ⟨mc, Γ, εc, ρc, hmc, hmcb, hΓ0, hεc0, hρc0, hεc, hρc, hcommon⟩ :=
    D.exists_shared_free_common_polynomial_corrections E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, mv, α, β,
      hrank, hproper, hmv, hmvb, hα, hβ, hfamily⟩ :=
    D.exists_shared_free_affine_orbit_family E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let m := mc * mv
  have hm : 0 < m := Nat.mul_pos hmc hmv
  have hmcdiv : mc ∣ m := ⟨mv, rfl⟩
  have hmvdiv : mv ∣ m := ⟨mc, Nat.mul_comm _ _⟩
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) := by
    change ((mc * mv : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((s : ℝ) * Lc) * Real.exp ((s : ℝ) * Lv) :=
        mul_le_mul hmcb hmvb (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hρcM : CoefficientGrid (E.basis.baseChange ℝ) m ρc.log :=
    fun a => realDenominatorGrid_subset_of_dvd hmc hmcdiv (hρc a)
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
    hrank, hproper, hm, hmb, hΓ0, (fun d => (hcommon d).1), hα, hβ, ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, Av, εv, ρv, U, hAv, hAv0, hεv0, hρv0, hU0,
      hεv, hρv, hdependent⟩ := hfamily h hh
  let ε := εc.logSum εv
  let ρ := ρc.logSum ρv
  let A := Γ.logSum Av
  have hε0 := εc.logSum_normalized εv hεc0 hεv0
  have hρ0 := ρc.logSum_normalized ρv hρc0 hρv0
  have hA0 := Γ.logSum_normalized Av hΓ0 hAv0
  have hρvM : CoefficientGrid (E.basis.baseChange ℝ) m ρv.log :=
    fun a => realDenominatorGrid_subset_of_dvd hmv hmvdiv (hρv a)
  have hcoeff (d : Fin s) : coefficients (g h).log (Finsupp.single () (d.val + 1)) -
      (coefficients ε.log (Finsupp.single () (d.val + 1)) +
        coefficients A.log (Finsupp.single () (d.val + 1)) +
        coefficients U.log (Finsupp.single () (d.val + 1)) +
        coefficients ρ.log (Finsupp.single () (d.val + 1))) ∈
      (T.filtration.layer (Finsupp.weight (fun _ : Unit => 1)
        (Finsupp.single () (d.val + 1))) 2).baseChange ℝ := by
    have hp := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two (by omega)
      (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) ξ (v h)
    rw [← hsplit h, (hcommon d).2, (hdependent d).2] at hp
    convert hp using 1
    simp only [ε, ρ, A, NilpotentLieFiltration.PolynomialOrbit.logSum_log,
      map_add, Finsupp.add_apply]
    abel
  obtain ⟨K, hK0, hprod, hK⟩ := T.exists_polynomialOrbit_factorization_rank_two (by omega)
    (fun _ : Unit => 1) (fun d : Fin s => Finsupp.single () (d.val + 1))
    (g h) ε A U ρ (hg h) hε0 hA0 hU0 hρ0 hcoeff
  refine ⟨x, hx, hspace, ε, A, K, U, ρ, ?_, hε0, hA0, hK0, hU0, hρ0,
    CoefficientBound.add _ _ hεc hεv, CoefficientGrid.add _ _ hρcM hρvM, hprod, ?_⟩
  · exact congrArg (fun z => Γ.log + z) hAv
  · intro d
    exact ⟨by simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hK d,
      (hdependent d).1⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct NNReal

theorem exists_sharedFreeFactorFreezing (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) {q p : ℝ},
      0 ≤ q → q ≤ p → 0 ≤ p → D.GeometryComplexityLE q →
      ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ Real.exp ((s : ℝ) *
        (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p)) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ ρ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          CoefficientGrid (D.basis.baseChange ℝ) m ρ.log →
          ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) x ρ) : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                (fun _ : Unit => 1) y ρ)) ∧
            ((QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) x ρ)⁻¹ : D.Space) =
              QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                (fun _ : Unit => 1) y ρ)⁻¹)) ∧
        ∀ (Φ : D.Space → ℂ) (K : ℝ≥0), (∀ z, ‖Φ z‖ ≤ 1) →
          (letI := D.metricSpace; LipschitzWith K Φ) → (K : ℝ) ≤ Real.exp q →
          ∀ ε a ρ g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
            ε * a * ρ = g → ∀ T : ℝ, 0 < T →
            CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => T)
              (Real.exp (sharedFreeCommonCorrectionBudget s q p) +
                Real.exp (sharedFreePetalLiftBudget s q p)) ε.log →
            CoefficientGrid (D.basis.baseChange ℝ) m ρ.log →
            ∀ (x y : Unit → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ j, |(x j : ℝ)| ≤ T) → (∀ j, |(y j : ℝ)| ≤ T) →
              (∀ j, |(x j : ℝ) - y j| ≤ T * δ) →
              (∀ j, (M : ℤ) ∣ x j - y j) →
              ‖Φ (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) x g)) -
                Φ (QuotientGroup.mk
                  (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y ε *
                   D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x a *
                   D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y ρ))‖ ≤
                Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨a, _, hfull⟩ := exists_sharedFreeFullOrbitBudget_bound s
  obtain ⟨b, _, hperiod⟩ := exists_native_orbit_rational_period s
  obtain ⟨c, _, hfreeze⟩ := exists_orbit_factor_freezing s 1
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((B + Polynomial.C b) ^ b + (B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D q p hq hqp hp hD m hm hmb
  let t := (p + a) ^ a + p + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hqt : q ≤ t := by dsimp only [t]; linarith
  have hbt : (p + a) ^ a ≤ t := by dsimp only [t]; linarith
  have ht1 : (1 : ℝ) ≤ t := by dsimp only [t]; linarith
  have hsum : (t + b) ^ b + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, t, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : (t + b) ^ b ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + c) ^ c by positivity]
  have hcC : (t + c) ^ c ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (t + b) ^ b by positivity]
  obtain ⟨_, _, _, hden, hslow⟩ := hfull q p hq hqp hp
  obtain ⟨M, hM, hMb, hsolve⟩ := hperiod D (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) t ht (hD.mono D hqt)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using ht1) m hm
    (hmb.trans (Real.exp_le_exp.mpr (hden.trans hbt)))
  refine ⟨M, hM, hMb.trans (Real.exp_le_exp.mpr hbC), hsolve, ?_⟩
  intro Φ K hΦ hLip hK ε a₀ ρ g hprod T hT hε hρ x y δ hδ hx hy hxy hres
  have hε' : CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => T)
      (Real.exp ((t + 2) ^ 1)) ε.log :=
    CoefficientBound.mono _ _ (fun _ => hT) hε
      (hslow.trans (Real.exp_le_exp.mpr (by simpa only [pow_one] using
        (hbt.trans (show t ≤ t + 2 by linarith)))))
  exact (hfreeze D (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) t ht
    (hD.mono D hqt) (by simpa only [Fintype.card_unit, Nat.cast_one] using ht1)
    Φ K hΦ hLip (hK.trans (Real.exp_le_exp.mpr hqt)) ε a₀ ρ g hprod
    (fun _ : Unit => T) (fun _ => hT) hε' x y δ hδ hx hy hxy
    (hsolve ρ hρ x y hres).1).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcC) hδ)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3

noncomputable def sharedFreeFactorFreezingConstant (s : ℕ) : ℕ :=
  (RationalFilteredNilmanifold.exists_sharedFreeFactorFreezing.{0} s).choose

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_invariant_native_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
          (finrank ℚ (SubspaceFreeLift.Algebra S r)),
        ∃ U : M.DegreeRankStructure r,
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧ IsCentralLieBasis M.basis ∧
          Nonempty (FreeCoordinateFrame M.basis (sharedFreeComparisonModelBudget s Q P')) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => E)).basis.repr
            (φ (M.basis j)) i) ≤ sharedFreeComparisonModelBudget s Q P') ∧
          M.lattice ≤ (pi (fun _ : Fin 2 => E)).lattice.comap (mapOfSteps
            (hL := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s r)
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             Z.frequency = (pairDifferenceFunctional V.frequency).comp φ.toLinearMap ∧
             (∀ x ∈ U.filtration.layer s r, Z.frequency x = 0) ∧
             (∀ i z, z ∈ U.realSubgroup s r → ∀ x, Z.observable i (z • x) = Z.observable i x) ∧
             ∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  intro S hS
  obtain ⟨J, hJ, M, U, hU, hUc, hcentral, hframe, hmatrix, hlattice, hZ⟩ :=
    D.exists_native_comparison_model E T hbQ hT F V g hg D' hTfil hs hP' hQP'
  refine ⟨J, hJ, M, U, hU, hUc, hcentral, hframe, hmatrix, hlattice, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hfreqZ, hobs⟩ := hZ
  have hzero := B₀.native_comparison_frequency_zero D E T hbQ hT V g hg D'
    hTfil hfreq J M U hU Z.frequency hfreqZ
  exact ⟨Z, hfreqZ, hzero,
    (fun i z hz x => Z.rank_invariant_of_frequency_zero U hzero z hz i x), hobs⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_uniform_lower_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
          (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
        ∃ U : M.DegreeRankStructure (r + 1),
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1))
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             (∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
             M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
               (sharedFreeLowerComparisonBudget s Q P')) := by
  intro S hS
  obtain ⟨J, hJ, M, U, hU, hUc, _, _, _, _, hZ⟩ :=
    B₀.exists_invariant_native_comparison_model D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP'
  refine ⟨J, hJ, M, U, hU, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, _, hzero, _, hobs⟩ := hZ
  refine ⟨Z, hobs, ?_⟩
  have hpM : 0 ≤ sharedFreeComparisonModelBudget s Q P' :=
    (Nat.cast_nonneg _).trans hUc.1.1
  exact UnitVerticalObservable.hasUniformLowerRankUnitFamily M U Z
    (fun _ : Unit => 1) hpM hUc hzero

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_lower_factored_family {τ : Type*}
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (A K U : τ → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A t) = 1)
    (hK0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K t) = 1)
    (hU0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U t) = 1)
    (hA : ∀ t (d : Fin s), coefficients (A t).log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ t (d : Fin s), coefficients (K t).log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ t (d : Fin s), coefficients (U t).log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
        (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
      ∃ Tm : M.DegreeRankStructure (r + 1),
        Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
        Tm.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
        M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
          (fun t (i : Fin W.family.outputDim × Fin W.family.outputDim) x =>
            V.observable i.1 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t * K t * U t))) *
            star (V.observable i.2 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t)))))
          (sharedFreeLowerComparisonBudget s Q P') := by
  intro S
  obtain ⟨J, _, M, Tm, hTm, hTmc, hZ⟩ :=
    B₀.exists_uniform_lower_comparison_model D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP'
  refine ⟨M, Tm, hTm, hTmc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hobs, huniform⟩ := hZ
  apply huniform.realizeFamily
  intro t
  obtain ⟨u, hu0, _, hu⟩ := D.exists_native_factored_comparison_orbit E T hbQ hT V g hg D'
    hTfil (by omega) (A t) (K t) (U t) (hA0 t) (hK0 t) (hU0 t) (hA t) (hK t) (hU t)
    J M Tm hTm
  refine ⟨u, hu0, ?_⟩
  intro i x
  exact SubspaceFreeLift.native_pair_observable_eval E T S J
    (D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil)
    M Tm V Z hobs ![A t * K t * U t, A t] u hu i x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_shared_free_lower_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let Lc := sharedFreeCommonCorrectionBudget s Q P'
    let Lv := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * (Lc + Lv)) ∧
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
          (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
            ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
          ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
            (ε A K U ρ : {h // h ∈ J} →
              E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ h : {h // h ∈ J},
              (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
              (A h).log = Γ.log + positiveUnivariate
                (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (ε h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (ρ h) = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                (Real.exp Lc + Real.exp Lv) (ε h).log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m (ρ h).log ∧
              ε h * A h * K h * U h * ρ h = g h.val ∧
              ∀ d : Fin s,
                coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                  (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
                coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
            (∃ M₀ : ℕ, 0 < M₀ ∧
              (M₀ : ℝ) ≤ Real.exp ((P' + sharedFreeFactorFreezingConstant s) ^
                sharedFreeFactorFreezingConstant s) ∧
              (∀ (h : {h // h ∈ J}) (y z : Unit → ℤ),
                (∀ j, (M₀ : ℤ) ∣ y j - z j) →
                ((QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) y (ρ h)) : E.Space) =
                  QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) z (ρ h))) ∧
                ((QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) y (ρ h))⁻¹ : E.Space) =
                  QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) z (ρ h))⁻¹)) ∧
              ∀ (h : {h // h ∈ J}) i (y z : Unit → ℤ) (δ : ℝ), 0 ≤ δ →
                (∀ j, |(y j : ℝ)| ≤ N) → (∀ j, |(z j : ℝ)| ≤ N) →
                (∀ j, |(y j : ℝ) - z j| ≤ (N : ℝ) * δ) →
                (∀ j, (M₀ : ℤ) ∣ y j - z j) →
                ‖V.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y (g h.val))) -
                  V.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (ε h) *
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y
                       (A h * K h * U h) *
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (ρ h)))‖ ≤
                  Real.exp ((P' + sharedFreeFactorFreezingConstant s) ^
                    sharedFreeFactorFreezingConstant s) * δ) ∧
            let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
            ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
              ∃ Tm : M.DegreeRankStructure (r + 1),
                Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                Tm.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧
                M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                  (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) y =>
                    V.observable i.1 (QuotientGroup.mk
                      (E.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) y (A h * K h * U h))) *
                    star (V.observable i.2 (QuotientGroup.mk
                      (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) y (A h)))))
                  (sharedFreeLowerComparisonBudget s Q P') := by
  intro B Λ Lc Lv
  classical
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
      hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, hfamily⟩ :=
    D.exists_shared_free_full_orbit_factorization E T hbQ hT F V g hg D'
      hTfil hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  choose x hx hspace ε A K U ρ hAl hε0 hA0 hK0 hU0 hρ0 hε hρ hprod hKU using
    (fun h : {h // h ∈ J} => hfamily h.val h.property)
  have hAc : ∀ (h : {h // h ∈ J}) (d : Fin s),
      coefficients (A h).log (Finsupp.single () (d.val + 1)) ∈
        ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ := by
    intro h d
    rw [hAl h]
    exact affine_refined_coefficient_mem D.coefficientFreeSpan D.dependentFreeSpan
      (fun d : Fin s => D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
      Γ.log α β (fun j => (x h j : ℝ)) hΓ (fun d => (hα d).1) (fun j d => (hβ j d).1) d
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
    hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, x, ε, A, K, U, ρ, ?_, ?_, ?_⟩
  · intro h
    exact ⟨hx h, hspace h, hAl h, hε0 h, hA0 h, hK0 h, hU0 h, hρ0 h,
      hε h, hρ h, hprod h, hKU h⟩
  · have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
    obtain ⟨M₀, hM₀, hM₀b, hperiod, hfreeze⟩ :=
      (RationalFilteredNilmanifold.exists_sharedFreeFactorFreezing.{0} s).choose_spec.2
        E hQ hQP' hP' hT.1 m hm hmb
    refine ⟨M₀, hM₀, hM₀b, (fun h y z hres => hperiod (ρ h) (hρ h) y z hres), ?_⟩
    intro h i y z δ hδ hy hz hyz hres
    exact hfreeze (V.observable i) V.lipBound (V.norm i) (V.lipschitz i) V.lip_bound
      (ε h) (A h * K h * U h) (ρ h) (g h.val)
      (by simpa only [mul_assoc] using hprod h) (N : ℝ)
      (by exact_mod_cast NeZero.pos N) (hε h) (hρ h) y z δ hδ hy hz hyz hres
  · exact B₀.exists_lower_factored_family D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' A K U hA0 hK0 hU0 hAc
      (fun h d => (hKU h d).1) (fun h d => (hKU h d).2)

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeCorrelationBudget
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeCorrelationInput (s : ℕ) (p : ℝ) : ℝ :=
  p + (p + (exists_sharedFreeFullOrbitBudget_bound s).choose) ^
      (exists_sharedFreeFullOrbitBudget_bound s).choose +
    (p + sharedFreeFactorFreezingConstant s) ^ sharedFreeFactorFreezingConstant s + 2

noncomputable def sharedFreeCorrelationBudget (s : ℕ) (hs : 2 ≤ s) (p : ℝ) : ℝ :=
  (sharedFreeCorrelationInput s p + sharedFactorCorrelationConstant s hs) ^
    sharedFactorCorrelationConstant s hs

theorem sharedFreeCorrelationInput_bounds (s : ℕ) {q p : ℝ}
    (hq : 0 ≤ q) (hqp : q ≤ p) (hp : 0 ≤ p) :
    2 ≤ sharedFreeCorrelationInput s p ∧ q ≤ sharedFreeCorrelationInput s p ∧
    (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ≤ sharedFreeCorrelationInput s p ∧
    (s : ℝ) * (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p) ≤
      sharedFreeCorrelationInput s p ∧
    Real.exp (sharedFreeCommonCorrectionBudget s q p) + Real.exp (sharedFreePetalLiftBudget s q p) ≤
      Real.exp ((sharedFreeCorrelationInput s p + 2) ^ 1) ∧
    (p + sharedFreeFactorFreezingConstant s) ^ sharedFreeFactorFreezingConstant s ≤
      sharedFreeCorrelationInput s p := by
  let a := (exists_sharedFreeFullOrbitBudget_bound s).choose
  let b := sharedFreeFactorFreezingConstant s
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ (p + b) ^ b := by positivity
  have h2 : 2 ≤ sharedFreeCorrelationInput s p := by
    change 2 ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hpa : (p + a) ^ a ≤ sharedFreeCorrelationInput s p := by
    change (p + a) ^ a ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hpb : (p + b) ^ b ≤ sharedFreeCorrelationInput s p := by
    change (p + b) ^ b ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hqT : q ≤ sharedFreeCorrelationInput s p := by
    change q ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  obtain ⟨hΛ, _, _, hden, hslow⟩ := (exists_sharedFreeFullOrbitBudget_bound s).choose_spec.2 q p hq hqp hp
  refine ⟨h2, hqT, hΛ.trans hpa, hden.trans hpa, ?_, hpb⟩
  exact hslow.trans (Real.exp_le_exp.mpr (by simpa only [pow_one] using
    (hpa.trans (show sharedFreeCorrelationInput s p ≤ sharedFreeCorrelationInput s p + 2 by linarith))))

theorem sharedFreeCorrelationInput_le_budget (s : ℕ) (hs : 2 ≤ s) {p : ℝ} (hp : 0 ≤ p) :
    sharedFreeCorrelationInput s p ≤ sharedFreeCorrelationBudget s hs p := by
  let T := sharedFreeCorrelationInput s p
  let C := sharedFactorCorrelationConstant s hs
  have hT : 2 ≤ T := (sharedFreeCorrelationInput_bounds s hp le_rfl hp).1
  have hC : 2 ≤ C := (exists_shared_factor_correlations s hs).choose_spec.1
  have hbase : 1 ≤ T + C := by linarith [Nat.cast_nonneg (α := ℝ) C]
  change T ≤ (T + C) ^ C
  exact (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) C)).trans
    ((pow_one (T + C)).symm.le.trans (pow_le_pow_right₀ hbase (by omega : 1 ≤ C)))

theorem exists_sharedFreeCorrelationBudget_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      let B := sharedFreeCorrelationBudget s hs p
      let Q := B + sharedFreeComparisonBasisBudget q p + 2
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s + B ≤ (p + C) ^ C ∧
      (Q + nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
      nativeLowerPairModelBudget s Q ≤ (p + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_sharedFreeComparisonBasisBudget_bound
  obtain ⟨c, _, hc⟩ := exists_nativeLowerPairModelBudget_bound s
  let a := (exists_sharedFreeFullOrbitBudget_bound s).choose
  let d := sharedFreeFactorFreezingConstant s
  let e := sharedFactorCorrelationConstant s hs
  let f := sharedFreeAffineConstant s
  let T : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + Polynomial.C d) ^ d + 2
  let B : Polynomial ℕ := (T + Polynomial.C e) ^ e
  let Q : Polynomial ℕ := B + (Polynomial.X + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C f) ^ f + B + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp B₀ Q₀
  have hB₀ : 0 ≤ B₀ := by
    apply le_trans (show 0 ≤ sharedFreeCorrelationInput s p from
      (by linarith [(sharedFreeCorrelationInput_bounds s hq hqp hp).1]))
    exact sharedFreeCorrelationInput_le_budget s hs hp
  have hQ₀ : 0 ≤ Q₀ := by
    have := sharedFreeComparisonBasisBudget_nonneg hq hp
    dsimp only [Q₀]
    positivity
  let v := B₀ + (p + b) ^ b + 2
  have hQv : Q₀ ≤ v := by
    dsimp only [Q₀, v]
    linarith [hb q p hq hqp hp]
  have hv : 0 ≤ v := hQ₀.trans hQv
  have hΛ : 0 ≤ (p + f) ^ f := by positivity
  have hsum : (p + f) ^ f + B₀ + (v + c) ^ c ≤ (p + C) ^ C := by
    change (p + f) ^ f + (p + (p + a) ^ a + (p + d) ^ d + 2 + e) ^ e +
      ((p + (p + a) ^ a + (p + d) ^ d + 2 + e) ^ e + (p + b) ^ b + 2 + c) ^ c ≤ _
    simpa [T, B, Q, Polynomial.eval₂_pow] using hbudget p hp
  have htail : (v + c) ^ c ≤ (p + C) ^ C := by linarith
  have hfirst : (p + f) ^ f + B₀ ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (v + c) ^ c by positivity]
  have hpow : (Q₀ + c) ^ c ≤ (v + c) ^ c :=
    pow_le_pow_left₀ (by positivity) (by linarith) c
  exact ⟨hfirst, (hc Q₀ hQ₀).1.trans (hpow.trans htail),
    (hc Q₀ hQ₀).2.trans (hpow.trans htail)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeCorrelatedFactorization
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_correlated_lower_factorization
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (Hsource : Finset (ZMod N)) (hsource : Hsource.Nonempty)
    (hsourceDense : Real.exp (-Q) * Fintype.card (ZMod N) ≤ (Hsource.card : ℝ))
    (hHsource : H' ⊆ Hsource)
    (hcorr : ∀ h ∈ Hsource, Nonempty (NativeVectorCorrelation (s - 1) N Q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h)))))))
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (sharedFreeCorrelationBudget s hs P') ≤ (N : ℝ)) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let Lv := sharedFreePetalLiftBudget s Q P'
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-(Λ + C)) * H'.card ≤ (J.card : ℝ) ∧
      ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
        (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
        (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
        (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
        (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
        (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
        ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
          (A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
          (∀ h : {h // h ∈ J},
            (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
            (A h).log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            ∀ d : Fin s,
              coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan d)
                  (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                    (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc) := by
  intro Λ C Qc Lv S
  classical
  let P₀ := sharedFreeCorrelationInput s P'
  have hQ0 : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  obtain ⟨hP₀, hQP₀, hΛP₀, hdenP₀, hslowP₀, hperiodP₀⟩ :=
    sharedFreeCorrelationInput_bounds s hQ0 hQP' hP'
  have hP₀C : P₀ ≤ C := sharedFreeCorrelationInput_le_budget s hs hP'
  have hC0 : 0 ≤ C := (show 0 ≤ P₀ by linarith).trans hP₀C
  obtain ⟨D₁, _, _, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, Γ, α, β,
      hrank, hproper, hm, hmb, hΓ0, hΓ, hα, hβ, x, ε, A, K, U, ρ, hdata, hperiod, _⟩ :=
    B₀.exists_shared_free_lower_factorization D E T hbQ hT F V g hg D'
      hTfil hfreq hs hp' hP' hQP' hpp' ξ v hsplit hξ hv
      ((Real.exp_le_exp.mpr (hΛP₀.trans hP₀C)).trans hN)
  obtain ⟨M₀, hM₀, hM₀b, hperiod, _⟩ := hperiod
  let X := W.replaceRank E T hbQ hT V g hg Hsource hsource hsourceDense hcorr
  let ε' (h : ZMod N) := if hh : h ∈ J then ε ⟨h, hh⟩ else 1
  let a' (h : ZMod N) := if hh : h ∈ J then A ⟨h, hh⟩ * K ⟨h, hh⟩ * U ⟨h, hh⟩ else 1
  let ρ' (h : ZMod N) := if hh : h ∈ J then ρ ⟨h, hh⟩ else 1
  have hprod' (h : ZMod N) (hh : h ∈ J) : ε' h * a' h * ρ' h = X.family.orbit h := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, _, _, hprod, _⟩
    change ε' h * a' h * ρ' h = g h
    simp only [ε', a', ρ', dif_pos hh]
    simpa only [mul_assoc] using hprod
  have hε' (h : ZMod N) (hh : h ∈ J) :
      CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P₀ + 2) ^ 1)) (ε' h).log := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, hε, _, _, _⟩
    simp only [ε', dif_pos hh]
    exact CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) hε hslowP₀
  have hρ' (h : ZMod N) (hh : h ∈ J) : CoefficientGrid (E.basis.baseChange ℝ) m (ρ' h).log := by
    rcases hdata ⟨h, hh⟩ with ⟨_, _, _, _, _, _, _, _, _, hρ, _, _⟩
    simpa only [ρ', dif_pos hh] using hρ
  have hperiod' (h : ZMod N) (hh : h ∈ J) (z z' : Unit → ℤ)
      (hres : ∀ j, (M₀ : ℤ) ∣ z j - z' j) :
      (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z (ρ' h)) : E.Space) =
      QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z' (ρ' h)) := by
    simpa only [ρ', dif_pos hh] using (hperiod ⟨h, hh⟩ z z' hres).1
  obtain ⟨Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
      hRank, J₂, hsub, hJ₂, hdense, V₁, hfreq₁, hcorr₁⟩ :=
    (exists_shared_factor_correlations s hs).choose_spec.2 X hf hP₀ hQP₀ m M₀ hm
      (hmb.trans (Real.exp_le_exp.mpr hdenP₀)) hM₀
      (hM₀b.trans (Real.exp_le_exp.mpr hperiodP₀)) J
      (fun h hh => hHsource (hJH hh)) hJ ε' a' ρ' hprod' hε' hρ' hperiod' hN
  let lift (h : {h // h ∈ J₂}) : {h // h ∈ J} := ⟨h.val, hsub h.property⟩
  refine ⟨J₂, (fun h hh => hJH (hsub hh)), hJ₂, ?_, r₀, R₀, η, h₀, Γ, α, β,
    hrank, hproper, hΓ0, hΓ, hα, hβ, (fun h => x (lift h)), (fun h => A (lift h)),
    (fun h => K (lift h)), (fun h => U (lift h)), ?_, Δ, hΔ, hchar, hnormal, hfinite,
    hindex, l, hl, hin, hout, hRank, V₁, hfreq₁, ?_, ?_⟩
  · calc
      _ = Real.exp (-C) * (Real.exp (-Λ) * H'.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-C) * J.card := mul_le_mul_of_nonneg_left hcard (Real.exp_pos _).le
      _ ≤ _ := hdense
  · intro h
    rcases hdata (lift h) with ⟨hx, hs, hA, _, hA0, hK0, hU0, _, _, _, _, hKU⟩
    exact ⟨hx, hs, hA, hA0, hK0, hU0, hKU⟩
  · intro h
    have hc := hcorr₁ h.val h.property
    change Nonempty (NativeVectorCorrelation (s - 1) N C
      (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (z.val : ℤ)) (a' h.val)))))) at hc
    have ha : a' h.val = A (lift h) * K (lift h) * U (lift h) := by
      simp only [a', dif_pos (hsub h.property), lift]
    rw [ha] at hc
    exact hc
  · apply B₀.exists_covered_factored_family D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' Δ l hl hin hout hC0 hRank V₁ hfreq₁
      (fun h => A (lift h)) (fun h => K (lift h)) (fun h => U (lift h))
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, hA0, _, _, _, _, _, _, _⟩
      exact hA0
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, _, hK0, _, _, _, _, _, _⟩
      exact hK0
    · intro h
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, hU0, _, _, _, _, _⟩
      exact hU0
    · intro h d
      rcases hdata (lift h) with ⟨_, _, hA, _, _, _, _, _, _, _, _, _⟩
      rw [hA]
      exact affine_refined_coefficient_mem D.coefficientFreeSpan D.dependentFreeSpan
        (fun d : Fin s => D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
        Γ.log α β (fun j => (x (lift h) j : ℝ)) hΓ (fun d => (hα d).1) (fun j d => (hβ j d).1) d
    · intro h d
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, _, _, _, _, _, hKU⟩
      exact (hKU d).1
    · intro h d
      rcases hdata (lift h) with ⟨_, _, _, _, _, _, _, _, _, _, _, hKU⟩
      exact (hKU d).2

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeCorrelatedAffineExistence
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

def CorrelatedAffineComparison (hs : 2 ≤ s) : Prop :=
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    let Lv := sharedFreePetalLiftBudget s Q P'
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-(Λ + C)) * H'.card ≤ (J.card : ℝ) ∧
      ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
        (Γ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
        (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
        (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 Γ = 1 ∧
        (∀ d : Fin s, coefficients Γ.log (Finsupp.single () (d.val + 1)) ∈
          ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ) ∧
        (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp Lv) ∧
        (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
          ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp Lv) ∧
        ∃ (x : {h // h ∈ J} → Fin r₀ → ℤ)
          (A K U : {h // h ∈ J} → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
          (∀ h : {h // h ∈ J},
            (∀ j, |x h j| ≤ (R₀ j : ℤ)) ∧ h.val = h₀ + η (x h) ∧
            (A h).log = Γ.log + positiveUnivariate (fun d => α d + ∑ j, (x h j : ℝ) • β j d) ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K h) = 1 ∧
            E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U h) = 1 ∧
            ∀ d : Fin s,
              coefficients (K h).log (Finsupp.single () (d.val + 1)) ∈
                (T.filtration.layer (d.val + 1) 2).baseChange ℝ ∧
              coefficients (U h).log (Finsupp.single () (d.val + 1)) ∈
                (fourPetalSpace (D.dependentFreeSpan d)
                  (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                    (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) ∧
          ∃ Δ : Subgroup E.filtration.Group, Δ ≤ E.lattice ∧
            (Δ.subgroupOf E.lattice).Characteristic ∧ (Δ.subgroupOf E.lattice).Normal ∧
            (Δ.subgroupOf E.lattice).FiniteIndex ∧ (Δ.relIndex E.lattice : ℝ) ≤ Real.exp C ∧
            ∃ (l : ℕ) (hl : 0 < l)
              (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates E.basis Δ)
              (hout : bchSubgroupCoordinates E.basis Δ ⊆ denominatorGrid l),
              (T.withLattice Δ l hl hin hout).ComplexityLE C ∧
              ∃ V₁ : (E.withLattice Δ l hl hin hout).UnitVerticalObservable
                  ((T.withLattice Δ l hl hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) C,
                V₁.frequency = V.frequency ∧
                (∀ h : {h // h ∈ J}, Nonempty (NativeVectorCorrelation (s - 1) N C
                  (W.replacedRankResidual h.val (fun i z => V₁.observable i (QuotientGroup.mk
                    (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                      (fun _ => (z.val : ℤ)) (A h * K h * U h))))))) ∧
                ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
                    (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
                  ∃ Tm : M.DegreeRankStructure (r + 1),
                    Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
                    Tm.ComplexityLE ((Qc + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
                    M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
                      (fun h (i : Fin W.family.outputDim × Fin W.family.outputDim) z =>
                        V₁.observable i.1 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval
                            (fun _ : Unit => 1) z (A h * K h * U h))) *
                        star (V₁.observable i.2 (QuotientGroup.mk
                          (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) z (A h)))))
                      (nativeLowerPairModelBudget s Qc)

include F

theorem CoefficientBases.has_correlated_affine_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (Hsource : Finset (ZMod N)) (hsource : Hsource.Nonempty)
    (hsourceDense : Real.exp (-Q) * Fintype.card (ZMod N) ≤ (Hsource.card : ℝ))
    (hHsource : H' ⊆ Hsource)
    (hcorr : ∀ h ∈ Hsource, Nonempty (NativeVectorCorrelation (s - 1) N Q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h)))))))
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (sharedFreeCorrelationBudget s hs P') ≤ (N : ℝ)) :
    D.CorrelatedAffineComparison E T hbQ hT V g hg D' hs := by
  exact B₀.exists_correlated_lower_factorization D E T hbQ hT F V g hg D'
    hTfil hfreq hs hp' hP' hQP' hpp' hf Hsource hsource hsourceDense hHsource hcorr
    ξ v hsplit hξ hv hN

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def nativeSharedFreeRelationConstant (s : ℕ) (hs : 2 ≤ s) : ℕ :=
  (exists_native_shared_free_rank_relation s hs).choose

theorem exists_native_correlated_comparison_budget (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
      Z ≤ (p + C) ^ C ∧ ∀ A : ℝ, 0 ≤ A → A ≤ Z →
        sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
        Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
          sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
        ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
          nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
        nativeLowerPairModelBudget s
          (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
          (p + C) ^ C := by
  let a := nativeSharedFreeRelationConstant s hs
  obtain ⟨b, _, hbound⟩ := exists_sharedFreeCorrelationBudget_bound s hs
  let Z₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z₀ + (Z₀ + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp Z
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hsum : Z + (Z + b) ^ b ≤ (p + C) ^ C := by
    change (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C
    simpa [Z₀, Polynomial.eval₂_pow] using hbudget p hp
  have hZC : Z ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hZ (Nat.cast_nonneg b)) b)).trans hsum
  have hbC : (Z + b) ^ b ≤ (p + C) ^ C := (le_add_of_nonneg_left hZ).trans hsum
  refine ⟨hZC, ?_⟩
  intro A hA hAZ
  obtain ⟨hmain, hpair, hlower⟩ := hbound A Z hA hAZ hZ
  have hΛ : 0 ≤ (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s :=
    pow_nonneg (add_nonneg hZ (Nat.cast_nonneg _)) _
  have hcorrCost : sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hΛ).trans (hmain.trans hbC)
  have htotal : Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C := by
    linarith only [hmain, hsum]
  exact ⟨hcorrCost, htotal, hpair.trans hbC, hlower.trans hbC⟩

def NativeCorrelationStructure.HasCorrelatedAffineComparison
    {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s (r + 1) N p f) (hs : 2 ≤ s) (C : ℕ) : Prop :=
  let Z := (p + nativeSharedFreeRelationConstant s hs) ^ nativeSharedFreeRelationConstant s hs
  ∃ (A : ℝ) (hpA : p ≤ A), A ≤ Z ∧
  ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
    H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧ p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
    ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
      (B : D.CoefficientBases A)
      (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
        (finrank ℚ D.CoefficientFreeLieAlgebra))
      (T : E.DegreeRankStructure (r + 1)) (hT : T.ComplexityLE A),
      T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
      Nonempty (FreeCoordinateFrame E.basis A) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 E.basis
       ∃ V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) A,
         V.frequency = B.freeFrequency D ∧
         ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
           (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
           (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
             (D.commonFreeSpan d).baseChange ℝ) ∧
           ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
             (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
               (fun _ : Unit => 1) 0 (v h) = 1),
             (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
               (D.dependentFreeSpan d).baseChange ℝ) ∧
             (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                (fun h => by rw [map_mul, hξ, hv h, one_mul])
              ∃ (out' : Fin U.outputDim) (H' : Finset (ZMod N)) (q' : ℝ),
                H' ⊆ W.shifts ∧ H'.Nonempty ∧ CyclicShortShiftSet H' ∧
                Real.exp (-Z) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                A ≤ q' ∧ q' ≤ Z ∧
                ∃ (R' : NativeRankRelation U out' H' q' q') (D' : R'.CommonData Z),
                  D.CorrelatedAffineComparison E T hpA hT V (fun h => ξ * v h)
                    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D' hs ∧
                  Z + (Z + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
                    sharedFreeCorrelationBudget s hs Z ≤ (p + C) ^ C ∧
                  ((sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) +
                    nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
                  nativeLowerPairModelBudget s
                    (sharedFreeCorrelationBudget s hs Z + sharedFreeComparisonBasisBudget A Z + 2) ≤
                    (p + C) ^ C))

theorem exists_native_correlated_affine_comparison (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s (r + 1) N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → W.HasCorrelatedAffineComparison hs C := by
  obtain ⟨C, hC, hbudget⟩ := exists_native_correlated_comparison_budget s hs
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  unfold NativeCorrelationStructure.HasCorrelatedAffineComparison
  intro Z
  have hp : 0 ≤ p := (Nat.cast_nonneg _).trans W.family.complexity.1.1
  obtain ⟨hZC, hcost⟩ := hbudget p hp
  have hZ : 0 ≤ Z := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  obtain ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
      R, D, B, E, T, hT, hTfil, hcentral, hframe, hdata⟩ :=
    (exists_native_shared_free_rank_relation s hs).choose_spec.2 W hf
      ((Real.exp_le_exp.mpr hZC).trans hN)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, Hsource, _, hsourceW, hsource, _, hsourceDense,
      v, hv, hdep, hcorr, hnext⟩ := hdata
  obtain ⟨out', H', q', hsub, hH', hshort', hdense, hAq', hq'Z, R', ⟨D'⟩⟩ := hnext
  obtain ⟨F⟩ := hframe
  have hA : 0 ≤ A := hp.trans hpA
  obtain ⟨hcorrCost, htotal, hpair, hlower⟩ := hcost A hA hAZ
  have hmodel := B.has_correlated_affine_comparison D E T hpA hT F V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) D'
    hTfil hfreq hs (hA.trans hAq') hZ hAZ hq'Z hf
    Hsource hsource hsourceDense hsub hcorr ξ v (fun _ => rfl) hcommon hdep
    ((Real.exp_le_exp.mpr hcorrCost).trans hN)
  refine ⟨A, hpA, hAZ, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hTfil, hcentral, ⟨F⟩, V, hfreq, ξ, hξ, hcommon,
    v, hv, hdep, out', H', q', (fun h hh => hsourceW (hsub hh)), hH', hshort',
    hdense, hAq', hq'Z, R', D', hmodel, htotal, hpair, hlower⟩

end Erdos3

end

end OAI

end


