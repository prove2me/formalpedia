-- Prove2me | Definitions.Def_OAIQ071C005
-- name    : OAIQ071C005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T05:04:59.321155+00:00
-- url     : https://prove2.me/theorems/72e3519b-6522-4372-8b89-0efb91f7c4a4
-- title:
--   Definitions bundle OAIQ071C005 of the split of OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 153 declarations of OpenAI's Lean: 60 definitions, 2 inductive types or structures, 2 instances and 89 theorems. The definitions and types are `OAI.CoulombAtom.admissibleGraph`, `OAI.CoulombAtom.blockTensorCross`, `OAI.CoulombAtom.coherentOverlap`, `OAI.CoulombAtom.compactEigenspaceBasis`, `OAI.CoulombAtom.compactSpectralBasis`, `OAI.CoulombAtom.compactSpectralVector`, `OAI.CoulombAtom.diffuseOrbital`, `OAI.CoulombAtom.diffuseRaw`, `OAI.CoulombAtom.diffuseSeed`, `OAI.CoulombAtom.exteriorGradientConstant`, `OAI.CoulombAtom.finiteOccupationEnergy`, `OAI.CoulombAtom.finiteOrbitalEnergy`, `OAI.CoulombAtom.finiteOrbitalKinetic`, `OAI.CoulombAtom.instMeasurableSpacePatchLocalObservableTFLp`, `OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_3`, `OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_4`, `OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_5`, `OAI.CoulombAtom.orbitalCoreInteraction`, `OAI.CoulombAtom.orbitalPole`, `OAI.CoulombAtom.packetSynthesis`, `OAI.CoulombAtom.patchCenterMeasurableSpace`, `OAI.CoulombAtom.rawStripCount`, `OAI.CoulombAtom.scaledPrice`, `OAI.CoulombAtom.shellGraphConstant`, `OAI.CoulombAtom.slaterForm`, `OAI.CoulombAtom.slaterParticleMeasure`, `OAI.CoulombAtom.spatialFiniteDensity`, `OAI.CoulombAtom.spatialSmearing`, `OAI.CoulombAtom.spinLift`, `OAI.CoulombAtom.weakGraphChangeAmbient`, `OAI.CoulombBarrier.DeterministicLocalBound`, `OAI.CoulombBarrier.DeterministicLocalLipschitz`, `OAI.CoulombBarrier.IsNuclearBarrier`, `OAI.CoulombBarrier.WeakLaplacianLowerOn`, `OAI.CoulombBarrier.WeakNuclearLowerOn`, `OAI.CoulombBarrier.addedError`, `OAI.CoulombBarrier.barrierErrorExponent`, `OAI.CoulombBarrier.clippedNuclearField`, `OAI.CoulombBarrier.clippedOuterBarrier`, `OAI.CoulombBarrier.conditionalField` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombIonization_Fermionic_Slater`, `CoulombIonization_Fermionic_SlaterBody`, `CoulombIonization_Fermionic_SlaterMeasure`, `CoulombIonization_Fermionic_SlaterOccupation`, `CoulombIonization_Fermionic_SlaterPairAlgebra`, `CoulombIonization_Fermionic_SlaterPairTrace`, `CoulombIonization_Fermionic_SlaterPole`, `CoulombIonization_Fermionic_SlaterRepulsion`, `CoulombIonization_Fermionic_SlaterSymmetry`, `CoulombIonization_Fermionic_SlaterTwoBody`, `CoulombIonization_FieldAnalysis_BarrierInitialPoissonBarrier`, `CoulombIonization_FieldAnalysis_BarrierNuclearBarrier`, `CoulombIonization_FieldAnalysis_BarrierWeakMaxBarrier`, `CoulombIonization_FieldAnalysis_BoundedL1PoissonBarrier`, `CoulombIonization_FieldAnalysis_Conditional`, `CoulombIonization_FieldAnalysis_LaplacianCompDilation`, `CoulombIonization_FormDomain_CoherentHilbert`, `CoulombIonization_FormDomain_CoherentSchwartz`, `CoulombIonization_FormDomain_CompactEigenbasis`, `CoulombIonization_FormDomain_CoulombCoercivity`, `CoulombIonization_FormDomain_FermionicDensity`, `CoulombIonization_FormDomain_FiniteFermionEnsemble`, `CoulombIonization_FormDomain_Slater`, `CoulombIonization_FormDomain_WeakChangeVariables`, `CoulombIonization_Ionization_IntegratedStability`, `CoulombIonization_Localization_CoherentPackets`, `CoulombIonization_Localization_CoherentRealKinetic`, `CoulombIonization_Localization_FermiDensity`, `CoulombIonization_Localization_FormRawLaw`, `CoulombIonization_Localization_ObservationIntegral`, `CoulombIonization_Localization_PatchCenterObservable`, `CoulombIonization_Localization_PatchLocalObservable`, `CoulombIonization_Localization_PosteriorFreshTestBarrier`, `CoulombIonization_RadialBounds_BarrierInitialBoundsBarrier`, `CoulombIonization_RadialBounds_BarrierInitialInvariantBarrier`, `CoulombIonization_RadialBounds_BarrierInitialLipschitzBarrier`, `CoulombIonization_RadialBounds_BarrierInitializationBarrier`, `CoulombIonization_RadialBounds_BarrierOriginalForgettingBarrier`, `CoulombIonization_RadialBounds_BarrierOuterWeakBarrier`, `CoulombIonization_RadialBounds_BarrierRetainedFiniteBarrier`, `CoulombIonization_RadialBounds_BarrierSmoothMaxBarrier`, `CoulombIonization_RadialBounds_BarrierStepBarrier`, `CoulombIonization_RadialBounds_BarrierStepGeometryBarrier`, `CoulombIonization_RadialBounds_BarrierTowerBarrier`, `CoulombIonization_RadialBounds_BarrierTruncationBarrier`, `CoulombIonization_RadialBounds_ExteriorScreenNumerics`, `CoulombIonization_RadialBounds_RotationShellBarrier`, `CoulombIonization_RadialBounds_ShellResidualControl`, `CoulombIonization_RadialBounds_StripAveraging`, `CoulombIonization_ThomasFermi_SommerfeldCoefficient`, `CoulombIonization_Variational_BlockEnergy`, `CoulombIonization_Variational_BlockPermutations`, `CoulombIonization_Variational_CompactPotential`, `CoulombIonization_Variational_CorrelatedFiniteInsertion`, `CoulombIonization_Variational_DiffuseSeed`, `CoulombIonization_Variational_ExpectedTruncatedControl`, `CoulombIonization_Variational_IntegratedTruncatedControl`, `CoulombIonization_Variational_OrbitalPole`, `CoulombIonization_Variational_SmearingPotential`, `CoulombIonization_Variational_SmoothCompactIntegral`, `CoulombIonization_Variational_SpinEnergy`, `CoulombIonization_Variational_SpinFinite`, `CoulombIonization_Variational_SpinSpaceIntegrable`.
--
--   **Imports.** It imports the published bundle `Def_CoulombIonization`; the bundles `OAIQ071C000`, `OAIQ071C001` and `OAIQ071C002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ071C007`, `OAIQ071C011` and `OAIQ071C012`; the statement `OAI.CoulombBarrier.selected_barriers_limit_positive`; the proof of `OAI.CoulombBarrier.selected_barriers_limit_positive`.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C000
import Definitions.Def_OAIQ071C001
import Definitions.Def_OAIQ071C002

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_Slater
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace CoulombAtom

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

lemma slaterTensor_orthonormal (φ : Fin n → α → ℂ)
    (hφ : ∀ i j, (∫ t, conj (φ i t) * φ j t ∂μ) = if i=j then 1 else 0)
    (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterTensor φ σ x) * slaterTensor φ τ x
      ∂Measure.pi (fun _ : Fin n => μ)) = if σ=τ then 1 else 0 := by
  rw [slaterTensor_inner]
  simp_rw [hφ]
  by_cases he : σ=τ
  · subst τ; simp
  · rw [ite_eq_right he]
    have hh : ∃ i, σ i ≠ τ i := by
      by_contra! hh
      exact he (Equiv.ext hh)
    obtain ⟨i,hi⟩ := hh
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma slaterRaw_norm_sq_integral {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (φ i t) * φ j t ∂μ) = if i=j then 1 else 0) :
    (∫ x, ‖slaterRaw φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) = n.factorial := by
  apply Complex.ofReal_injective
  change RCLike.ofReal (∫ x, ‖slaterRaw φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) =
    (RCLike.ofReal (n.factorial : ℝ) : ℂ)
  rw [← integral_ofReal (𝕜 := ℂ)]
  change (∫ x, (Complex.ofReal (‖slaterRaw φ x‖^2))
    ∂Measure.pi (fun _ : Fin n => μ)) = (n.factorial : ℂ)
  simp_rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  have hi (σ τ : Equiv.Perm (Fin n)) : Integrable (fun x =>
      conj ((σ.sign : ℤ) : ℂ) * ((τ.sign : ℤ) : ℂ) *
        (conj (slaterTensor φ σ x) * slaterTensor φ τ x))
      (Measure.pi fun _ : Fin n => μ) :=
    ((memLp_slaterTensor hφ σ).star.integrable_mul (memLp_slaterTensor hφ τ)).const_mul _
  have he (x : Fin n → α) : conj (slaterRaw φ x) * slaterRaw φ x =
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        conj ((σ.sign : ℤ) : ℂ) * ((τ.sign : ℤ) : ℂ) *
          (conj (slaterTensor φ σ x) * slaterTensor φ τ x) := by
    simp only [slaterRaw, map_sum, map_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => hi σ τ))]
  simp_rw [integral_finsetSum _ (fun τ _ => hi _ τ), integral_const_mul,
    slaterTensor_orthonormal φ ho]
  have hs (σ : Equiv.Perm (Fin n)) :
      (∑ τ : Equiv.Perm (Fin n), conj ((σ.sign : ℤ) : ℂ) * ((τ.sign : ℤ) : ℂ) *
        (if σ=τ then 1 else 0)) = 1 := by
    rw [Finset.sum_eq_single σ]
    · simp only [ite_true, mul_one, map_intCast]
      exact (pow_two _).symm.trans (complex_sign_sq σ)
    · intro τ _ ht
      rw [ite_eq_right (Ne.symm ht), mul_zero]
    · simp
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_perm, Fintype.card_fin]

lemma slater_norm_sq_integral {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (φ i t) * φ j t ∂μ) = if i=j then 1 else 0) :
    (∫ x, ‖slater φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) = 1 := by
  simp only [slater, norm_mul, mul_pow, integral_const_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity), slaterRaw_norm_sq_integral hφ ho]
  exact inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterBody
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

namespace CoulombAtom

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

lemma slaterCoordinateTensor_inner (φ ψ : Fin n → α → ℂ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (j : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterCoordinateTensor φ ψ j σ x) * slaterCoordinateTensor φ ψ j τ x
      ∂Measure.pi (fun _ : Fin n => μ)) =
      if σ=τ then (∫ t, ‖ψ (σ j) t‖^2 ∂μ : ℝ) else 0 := by
  simp only [slaterCoordinateTensor, map_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin n => μ)
    (fun i t => conj ((if i=j then ψ else φ) (σ i) t) *
      (if i=j then ψ else φ) (τ i) t)]
  by_cases he : σ=τ
  · subst τ
    rw [ite_eq_left rfl, Finset.prod_eq_single j]
    · simpa only [ite_eq_left (show j=j from rfl), ite_true] using
        complex_integral_norm_sq (μ := μ) (ψ (σ j))
    · intro i _ hij
      rw [ite_eq_right hij, ho, ite_eq_left rfl]
    · simp
  · rw [ite_eq_right he]
    have hh : ∃ i, i ≠ j ∧ σ i ≠ τ i := by
      by_contra! hh
      exact he (permutations_eq_of_agree_except σ τ j hh)
    obtain ⟨i,hij,hi⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [ite_eq_right hij, ho, ite_eq_right hi]

lemma slaterCoordinateRaw_norm_sq_integral {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (j : Fin n) :
    (∫ x, ‖slaterCoordinateRaw φ ψ j x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ σ : Equiv.Perm (Fin n), ∫ t, ‖ψ (σ j) t‖^2 ∂μ := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  change (Complex.ofReal (∫ x, ‖∑ σ : Equiv.Perm (Fin n),
    ((σ.sign : ℤ) : ℂ) * slaterCoordinateTensor φ ψ j σ x‖^2
      ∂Measure.pi (fun _ : Fin n => μ))) = _
  rw [integral_norm_sq_weighted_sum _ _ (memLp_slaterCoordinateTensor hφ hψ j)]
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [slaterCoordinateTensor_inner φ ψ ho]
  rw [Finset.sum_eq_single σ]
  · simp only [ite_true, map_intCast]
    rw [← pow_two, complex_sign_sq, one_mul]
  · intro τ _ ht
    simp only [ite_eq_right (Ne.symm ht), Complex.ofReal_zero, mul_zero]
  · simp

lemma slaterCoordinateRaw_sum_norm_sq_integral {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0) :
    (∑ j : Fin n, ∫ x, ‖slaterCoordinateRaw φ ψ j x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      (n.factorial : ℝ) * ∑ i, ∫ t, ‖ψ i t‖^2 ∂μ := by
  simp_rw [slaterCoordinateRaw_norm_sq_integral hφ hψ ho]
  rw [Finset.sum_comm]
  have he (σ : Equiv.Perm (Fin n)) :
      (∑ j, ∫ t, ‖ψ (σ j) t‖^2 ∂μ) = ∑ i, ∫ t, ‖ψ i t‖^2 ∂μ :=
    Equiv.sum_comp σ (fun i => ∫ t, ‖ψ i t‖^2 ∂μ)
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterPairAlgebra
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterPairAlgebra_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

lemma slaterRestTensor_inner (φ : Fin n → α → ℂ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (j k : Fin n) (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, conj (slaterRestTensor φ j k σ x) * slaterRestTensor φ j k τ x
      ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) =
      if τ=σ ∨ τ=σ * Equiv.swap j k then 1 else 0 := by
  classical
  simp only [slaterRestTensor, map_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : SlaterPairRest j k => μ)
    (fun (i : SlaterPairRest j k) t => conj (φ (σ i) t) * φ (τ i) t)]
  simp_rw [ho]
  split_ifs with he
  · apply Finset.prod_eq_one
    intro i _
    apply ite_eq_left
    rcases he with rfl | rfl
    · rfl
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne i.2.1 i.2.2]
  · have hh : ∃ i, i ≠ j ∧ i ≠ k ∧ σ i ≠ τ i := by
      by_contra! hh
      exact he (permutations_eq_or_swap_of_agree_except_two σ τ j k hh)
    obtain ⟨i,hij,hik,hi⟩ := hh
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hij,hik⟩ : SlaterPairRest j k))
    exact ite_eq_right hi

lemma slaterPairSliceRaw_norm_sq_integral {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    {j k : Fin n} (hjk : j ≠ k) (u v : α) :
    (Complex.ofReal (∫ x, ‖slaterPairSliceRaw φ j k u v x‖^2
      ∂Measure.pi (fun _ : SlaterPairRest j k => μ))) =
      ∑ σ : Equiv.Perm (Fin n),
        (conj (slaterPairAmplitude φ j k σ u v) * slaterPairAmplitude φ j k σ u v -
        conj (slaterPairAmplitude φ j k σ u v) *
          slaterPairAmplitude φ j k (σ * Equiv.swap j k) u v) := by
  classical
  rw [show slaterPairSliceRaw φ j k u v = fun x => ∑ σ : Equiv.Perm (Fin n),
    ((σ.sign : ℤ) : ℂ) * slaterPairAmplitude φ j k σ u v *
      slaterRestTensor φ j k σ x from rfl,
    integral_norm_sq_weighted_sum _ _ (memLp_slaterRestTensor hφ j k)]
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [slaterRestTensor_inner φ ho j k]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ)]
  rw [ite_eq_left (show σ=σ ∨ σ=σ * Equiv.swap j k from Or.inl rfl), mul_one]
  simp only [map_mul, map_intCast]
  have hne := perm_mul_swap_ne_self σ hjk
  rw [Finset.sum_eq_single (σ * Equiv.swap j k)]
  · rw [ite_eq_left (Or.inr rfl), mul_one, complex_sign_mul_swap σ hjk]
    have hs := complex_sign_sq σ
    ring_nf at hs ⊢
    simp only [hs, one_mul]
  · intro τ ht htne
    have htσ : τ ≠ σ := (Finset.mem_erase.mp ht).1
    rw [ite_eq_right (not_or.mpr ⟨htσ,htne⟩), mul_zero]
  · intro ht
    apply (ht ?_).elim
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩

end Work_SlaterPairAlgebra_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterPairTrace
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterPairTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

omit [MeasurableSpace α] in
lemma slaterPairContraction_sum_of_perm (φ : Fin n → α → ℂ) (σ : Equiv.Perm (Fin n))
    (u v : α) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ k then
      slaterPairContraction φ (σ j) (σ k) u v else 0) =
      ∑ i : Fin n, ∑ l : Fin n, slaterPairContraction φ i l u v := by
  have he (j k : Fin n) : (if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0) =
      slaterPairContraction φ (σ j) (σ k) u v := by
    by_cases h : j=k
    · subst k; simp only [ne_eq, not_true_eq_false, ite_false, slaterPairContraction_self]
    · rw [ite_eq_left h]
  simp_rw [he]
  calc
    _ = ∑ j : Fin n, ∑ l : Fin n, slaterPairContraction φ (σ j) l u v := by
      apply Finset.sum_congr rfl
      intro j _
      exact Equiv.sum_comp σ (fun l => slaterPairContraction φ (σ j) l u v)
    _ = _ := Equiv.sum_comp σ (fun i => ∑ l : Fin n, slaterPairContraction φ i l u v)

lemma slaterPairSliceRaw_sum_integral {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (u v : α) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ k then
      (∫ x, ‖slaterPairSliceRaw φ j k u v x‖^2
        ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) else 0) =
      (n.factorial : ℝ) *
        ((∑ i : Fin n, ‖φ i u‖^2) * (∑ i : Fin n, ‖φ i v‖^2) -
          ‖∑ i : Fin n, φ i u * conj (φ i v)‖^2) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  have he (j k : Fin n) :
      Complex.ofReal (if j ≠ k then (∫ x, ‖slaterPairSliceRaw φ j k u v x‖^2
        ∂Measure.pi (fun _ : SlaterPairRest j k => μ)) else 0) =
      ∑ σ : Equiv.Perm (Fin n), if j ≠ k then
        slaterPairContraction φ (σ j) (σ k) u v else 0 := by
    by_cases hjk : j ≠ k
    · simp only [ite_eq_left hjk]
      rw [slaterPairSliceRaw_norm_sq_integral hφ ho hjk]
      simp_rw [slaterPairAmplitude_contraction]
    · simp only [ite_eq_right hjk, Complex.ofReal_zero, Finset.sum_const_zero]
  calc
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ σ : Equiv.Perm (Fin n),
        if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact he j k
    _ = ∑ j : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ k : Fin n,
        if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ j : Fin n, ∑ k : Fin n,
        if j ≠ k then slaterPairContraction φ (σ j) (σ k) u v else 0 := Finset.sum_comm
    _ = _ := by
      simp_rw [slaterPairContraction_sum_of_perm, slaterPairContraction_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end Work_SlaterPairTrace_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterTwoBody
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SlaterTwoBody_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

lemma slaterPairMarginal_sum {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (z : α × α) :
    (∑ j : Fin n, ∑ k : Fin n, slaterPairMarginal (μ := μ) φ j k z) =
      (∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2) -
        ‖∑ i : Fin n, φ i z.1 * conj (φ i z.2)‖^2 := by
  have he (j k : Fin n) : slaterPairMarginal (μ := μ) φ j k z =
      (n.factorial : ℝ)⁻¹ * (if j ≠ k then
        ∫ y, ‖slaterPairSliceRaw φ j k z.1 z.2 y‖^2
          ∂Measure.pi (fun _ : SlaterPairRest j k => μ) else 0) := by
    unfold slaterPairMarginal
    split_ifs <;> simp only [mul_zero]
  simp_rw [he, ← Finset.mul_sum]
  rw [slaterPairSliceRaw_sum_integral hφ ho, ← mul_assoc,
    inv_mul_cancel₀ (show (n.factorial:ℝ) ≠ 0 by exact_mod_cast n.factorial_ne_zero), one_mul]

lemma slaterPairMarginal_observable_integrable {φ : Fin n → α → ℂ}
    {j k : Fin n} (hjk : j ≠ k) (w : α × α → ℝ)
    (hi : Integrable (fun x => w (x j,x k) * ‖slater φ x‖^2)
      (Measure.pi fun _ : Fin n => μ)) :
    Integrable (fun z => w z * slaterPairMarginal (μ := μ) φ j k z) (μ.prod μ) := by
  have mp := (slaterPairSplit_preserving (μ := μ) hjk).symm
  have h := (mp.integrable_comp_of_integrable hi).integral_prod_left
  apply h.congr
  filter_upwards [] with z
  rcases z with ⟨u,v⟩
  simp only [Function.comp_def, slaterPairSplit_symm_apply_left,
    slaterPairSplit_symm_apply_right, slater_pair_split_norm_sq, integral_const_mul,
    slaterPairMarginal, ite_eq_left hjk]

theorem slater_two_body {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i l, (∫ t, conj (φ i t) * φ l t ∂μ) = if i=l then 1 else 0)
    (w : α × α → ℝ)
    (hi : ∀ j k : Fin n, j ≠ k →
      Integrable (fun x => w (x j,x k) * ‖slater φ x‖^2)
        (Measure.pi fun _ : Fin n => μ)) :
    (∑ j : Fin n, ∑ k : Fin n, if j ≠ k then
      (∫ x, w (x j,x k) * ‖slater φ x‖^2 ∂Measure.pi (fun _ : Fin n => μ)) else 0) =
      ∫ z, w z * ((∑ i : Fin n, ‖φ i z.1‖^2) * (∑ i : Fin n, ‖φ i z.2‖^2) -
        ‖∑ i : Fin n, φ i z.1 * conj (φ i z.2)‖^2) ∂μ.prod μ := by
  have hm (j k : Fin n) :
      Integrable (fun z => w z * slaterPairMarginal (μ := μ) φ j k z) (μ.prod μ) := by
    by_cases hjk : j ≠ k
    · exact slaterPairMarginal_observable_integrable hjk w (hi j k hjk)
    · simp [slaterPairMarginal, hjk]
  have he (j k : Fin n) :
      (if j ≠ k then (∫ x, w (x j,x k) * ‖slater φ x‖^2
        ∂Measure.pi (fun _ : Fin n => μ)) else 0) =
      ∫ z, w z * slaterPairMarginal (μ := μ) φ j k z ∂μ.prod μ := by
    by_cases hjk : j ≠ k
    · simp only [ite_eq_left hjk, slaterPairMarginal]
      exact slater_pair_observable hjk w (hi j k hjk)
    · simp only [ite_eq_right hjk, slaterPairMarginal, mul_zero, integral_zero]
  simp_rw [he]
  simp_rw [← integral_finsetSum _ (fun k _ => hm _ k)]
  rw [← integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hm j k))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp_rw [← Finset.mul_sum]
  rw [slaterPairMarginal_sum hφ ho]

end Work_SlaterTwoBody_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {n : ℕ}

lemma slaterCoordinate_sum_norm_sq_integral {φ ψ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0) :
    (∑ j : Fin n, ∫ x, ‖slaterCoordinate φ ψ j x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) = ∑ i, ∫ t, ‖ψ i t‖^2 ∂μ := by
  simp only [slaterCoordinate, norm_mul, mul_pow, integral_const_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt (show (0:ℝ) ≤ n.factorial by positivity)]
  rw [← Finset.mul_sum, slaterCoordinateRaw_sum_norm_sq_integral hφ hψ ho,
    ← mul_assoc, inv_mul_cancel₀ (show (n.factorial:ℝ) ≠ 0 by exact_mod_cast n.factorial_ne_zero),
    one_mul]

omit [MeasurableSpace α] in
lemma slaterCoordinateTensor_mul (φ : Fin n → α → ℂ) (b : α → ℂ)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slaterCoordinateTensor φ (fun i t => b t * φ i t) j σ x =
      b (x j) * slaterTensor φ σ x := by
  unfold slaterCoordinateTensor slaterTensor
  have he (i : Fin n) :
      (if i=j then (fun k t => b t * φ k t) else φ) (σ i) (x i) =
      (if i=j then b (x j) else 1) * φ (σ i) (x i) := by
    by_cases hij : i=j
    · subst i; simp
    · simp only [ite_eq_right hij, one_mul]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp

omit [MeasurableSpace α] in
lemma slaterCoordinateRaw_mul (φ : Fin n → α → ℂ) (b : α → ℂ)
    (j : Fin n) (x : Fin n → α) :
    slaterCoordinateRaw φ (fun i t => b t * φ i t) j x = b (x j) * slaterRaw φ x := by
  simp only [slaterCoordinateRaw, slaterCoordinateTensor_mul, slaterRaw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

omit [MeasurableSpace α] in
lemma slaterCoordinate_mul (φ : Fin n → α → ℂ) (b : α → ℂ)
    (j : Fin n) (x : Fin n → α) :
    slaterCoordinate φ (fun i t => b t * φ i t) j x = b (x j) * slater φ x := by
  rw [slaterCoordinate, slaterCoordinateRaw_mul, slater]
  ring

lemma slater_local_squares {φ : Fin n → α → ℂ} (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (b : α → ℂ) (hb : ∀ i, MemLp (fun t => b t * φ i t) 2 μ) :
    (∫ x, (∑ j : Fin n, ‖b (x j)‖^2) * ‖slater φ x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ i, ∫ t, ‖b t‖^2 * ‖φ i t‖^2 ∂μ := by
  have hi (j : Fin n) : Integrable (fun x => ‖b (x j)‖^2 * ‖slater φ x‖^2)
      (Measure.pi fun _ : Fin n => μ) := by
    simpa only [slaterCoordinate_mul, norm_mul, mul_pow] using
      (memLp_slaterCoordinate hφ hb j).norm.integrable_sq
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simpa only [slaterCoordinate_mul, norm_mul, mul_pow] using
    slaterCoordinate_sum_norm_sq_integral hφ hb ho

lemma slater_nonnegative_potential {φ : Fin n → α → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (ho : ∀ i k, (∫ t, conj (φ i t) * φ k t ∂μ) = if i=k then 1 else 0)
    (V : α → ℝ) (hV : ∀ t, 0 ≤ V t)
    (hv : ∀ i, MemLp (fun t => (Real.sqrt (V t) : ℂ) * φ i t) 2 μ) :
    (∫ x, (∑ j : Fin n, V (x j)) * ‖slater φ x‖^2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ i, ∫ t, V t * ‖φ i t‖^2 ∂μ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hV _)] using
    slater_local_squares hφ ho (fun t => (Real.sqrt (V t) : ℂ)) hv

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterSymmetry
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

lemma slaterCoordinateTensor_eq {α : Type*} {n : ℕ} (φ ψ : Fin n → α → ℂ)
    (j : Fin n) (σ : Equiv.Perm (Fin n)) (x : Fin n → α) :
    slaterCoordinateTensor φ ψ j σ x =
      ψ (σ j) (x j) * ∏ i ∈ Finset.univ.erase j, φ (σ i) (x i) := by
  rw [slaterCoordinateTensor, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [ite_eq_right (Finset.mem_erase.mp hi).1]

lemma slater_spatial_tensor_derivative {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (s : Spins n) (σ : Equiv.Perm (Fin n)) (x : Configuration n) (j : Fin n) (a : Fin 3) :
    fderiv ℝ (fun y : Configuration n => slaterTensor φ σ (slaterParticles s y)) x
        (direction j a) =
      slaterCoordinateTensor φ (spatialOrbitalDerivative φ a) j σ (slaterParticles s x) := by
  have hd (i : Fin n) : DifferentiableAt ℝ
      (fun y : Configuration n => φ (σ i) (s i,y i)) x :=
    ((hφ (σ i) (s i)).comp (f := fun y : Configuration n => y i)
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space).contDiff).differentiable
        (by simp) x
  have he (i : Fin n) : fderiv ℝ (fun y : Configuration n => φ (σ i) (s i,y i)) x
      (direction j a) = if i=j then spatialOrbitalDerivative φ a (σ j) (s j,x j) else 0 := by
    rw [show (fun y : Configuration n => φ (σ i) (s i,y i)) =
      (fun z : Space => φ (σ i) (s i,z)) ∘ (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space) from rfl,
      fderiv_comp x ((hφ (σ i) (s i)).differentiable (by simp) (x i))
        (ContinuousLinearMap.proj i : Configuration n →L[ℝ] Space).differentiableAt,
      ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
    by_cases hij : i=j
    · subst i
      simp only [ContinuousLinearMap.proj_apply, direction, Pi.single_eq_same]
      rfl
    · simp only [ite_eq_right hij, ContinuousLinearMap.proj_apply, direction,
        Pi.single_eq_of_ne hij, map_zero]
  change fderiv ℝ (fun y : Configuration n => ∏ i, φ (σ i) (s i,y i)) x _ = _
  rw [fderiv_finsetProd (fun i _ => hd i), sum_apply]
  simp only [smul_apply, smul_eq_mul, he]
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl, slaterCoordinateTensor_eq, mul_comm]
    rfl
  · intro i _ hij
    rw [ite_eq_right hij, mul_zero]
  · simp

lemma slater_spatial_derivative {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (s : Spins n) (x : Configuration n) (j : Fin n) (a : Fin 3) :
    fderiv ℝ (fun y : Configuration n => slater φ (slaterParticles s y)) x (direction j a) =
      slaterCoordinate φ (spatialOrbitalDerivative φ a) j (slaterParticles s x) := by
  change fderiv ℝ (fun y : Configuration n => (Real.sqrt (n.factorial : ℝ) : ℂ)⁻¹ *
    slaterRaw φ (slaterParticles s y)) x _ = _
  rw [fderiv_const_mul ((slater_spatial_raw_smooth hφ s).differentiable (by simp) x),
    smul_apply, smul_eq_mul]
  unfold slaterRaw
  rw [fderiv_fun_sum (fun σ _ => ((slater_spatial_tensor_smooth hφ s σ).differentiable
    (by simp) x).const_mul _), sum_apply]
  simp_rw [fderiv_const_mul ((slater_spatial_tensor_smooth hφ s _).differentiable
    (by simp) x), smul_apply, smul_eq_mul, slater_spatial_tensor_derivative hφ]
  rfl

def slaterForm {n : ℕ} (φ : Fin n → SlaterParticle → ℂ) : FormVector n where
  value s x := slater φ (slaterParticles s x)
  gradient s j a x := slaterCoordinate φ (spatialOrbitalDerivative φ a) j (slaterParticles s x)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_WeakChangeVariables
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

section WeakGraphChange
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι]

def weakGraphChangeAmbient (v : ι → E) (e : E ≃L[ℝ] E) (he : MeasurePreserving e)
    (κ : ι → ι) : weakGraph v →L[ℂ] WeakGraphAmbient E ι :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Option ι => Lp ℂ 2 (volume : Measure E))
    ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j =>
      (Lp.compMeasurePreservingₗᵢ ℂ e he).toContinuousLinearMap.comp
        ((PiLp.proj 2 (fun _ : Option ι => Lp ℂ 2 (volume : Measure E)) (j.map κ)).comp
          (weakGraph v).subtypeL))

end WeakGraphChange

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FermionicDensity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma sectorDirections_permute {N : ℕ} (π : Equiv.Perm (Fin N)) (k : Fin N × Fin 3) :
    permuteConfiguration π (sectorDirections N k) = sectorDirections N (π.symm k.1, k.2) := by
  classical
  ext i a
  simp only [permuteConfiguration_apply, Function.comp_apply, sectorDirections, direction]
  by_cases h : i = π.symm k.1
  · subst i
    simp
  · have h' : π i ≠ k.1 := by
      intro hh
      apply h
      exact π.injective (by simpa using hh)
    simp [h, h']

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

def admissibleGraph {N : ℕ} (ψ : FormVector N) (hψ : FormAdmissible ψ) : fermionGraph N := by
  let F : SectorGraph N := WithLp.toLp 2 (admissibleWeakGraph ψ hψ)
  refine ⟨F, (mem_fermionSpace_ae (sectorGraphValue N F)).mpr ?_⟩
  intro π s
  have hp := (permuteConfiguration_preserving π).quasiMeasurePreserving.ae
    ((hψ.1 (s ∘ π)).coeFn_toLp)
  simp only [permuteConfiguration_apply] at hp
  filter_upwards [hp, (hψ.1 s).coeFn_toLp, hψ.2.2.2.1 π s] with x hx hy hz
  change (hψ.1 (s ∘ π)).toLp _ (x ∘ π) = _
  change (hψ.1 (s ∘ π)).toLp _ (x ∘ π) = _ at hx
  change _ = (((Equiv.Perm.sign π : ℤ) : ℂ)) * (hψ.1 s).toLp _ x
  rw [hx, hy, hz]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_IntegratedStability
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

def scaledPrice (E : ℕ → ℝ) (Z : ℕ) (m t : ℝ) : ℝ :=
  (priceEnergy E (t * m ^ (4 / 3 : ℝ)) - t * m ^ (4 / 3 : ℝ) * Z - E Z) /
    m ^ (7 / 3 : ℝ)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterMeasure
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

lemma spinSpace_measurePreserving (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n))
      (Measure.pi fun _ : Fin n => (Measure.count : Measure (Fin 2)).prod volume)
      ((Measure.count : Measure (Spins n)).prod volume) := by
  simpa only [pi_count_eq_count, ← volume_pi] using
    measurePreserving_arrowProdEquivProdArrow (Fin 2) Space (Fin n)
      (fun _ => (Measure.count : Measure (Fin 2))) (fun _ => (volume : Measure Space))

lemma spinSpace_integral {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : (Fin n → Fin 2 × Space) → E)
    (hF : Integrable F (Measure.pi fun _ : Fin n =>
      (Measure.count : Measure (Fin 2)).prod volume)) :
    (∫ z, F z ∂Measure.pi (fun _ : Fin n => (Measure.count : Measure (Fin 2)).prod volume)) =
      ∑ s : Spins n, ∫ x : Configuration n, F (fun i => (s i,x i)) := by
  have hp := (spinSpace_measurePreserving n).symm
  have hi := (hp.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n)).symm.measurableEmbedding).2 hF
  rw [← hp.integral_comp' F]
  change Integrable (fun z : Spins n × Configuration n =>
    F (fun i => (z.1 i,z.2 i))) (Measure.count.prod volume) at hi
  change (∫ z : Spins n × Configuration n, F (fun i => (z.1 i,z.2 i))
    ∂Measure.count.prod volume) = _
  rw [integral_prod _ hi, integral_count]

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

abbrev slaterParticleMeasure : Measure SlaterParticle :=
  (Measure.count : Measure (Fin 2)).prod volume

lemma compact_spinSpace {f : SlaterParticle → ℂ}
    (hc : ∀ s, HasCompactSupport (fun x : Space => f (s,x))) : HasCompactSupport f := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_univ.prod (isCompact_iUnion hc))
  intro z hz
  exact ⟨Set.mem_univ _, Set.mem_iUnion.mpr ⟨z.1, subset_tsupport _ hz⟩⟩

lemma memLp_spinSpace {f : SlaterParticle → ℂ}
    (hf : ∀ s, Continuous (fun x : Space => f (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => f (s,x))) :
    MemLp f 2 slaterParticleMeasure :=
  (continuous_prod_of_discrete_left.mpr hf).memLp_of_hasCompactSupport (compact_spinSpace hc)

lemma memLp_spatialOrbitalDerivative {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (a : Fin 3) (i : Fin n) :
    MemLp (spatialOrbitalDerivative φ a i) 2 slaterParticleMeasure :=
  memLp_spinSpace (fun s => smooth_derivative_continuous (hφ i s) _)
    (fun s => compact_derivative (hc i s) _)

lemma slaterForm_mass {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i, MemLp (φ i) 2 slaterParticleMeasure)
    (ho : ∀ i k, (∫ z, conj (φ i z) * φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0) :
    formMass (slaterForm φ) = 1 := by
  have he := spinSpace_integral (fun z => ‖slater φ z‖^2)
    (memLp_slater hφ).norm.integrable_sq
  have hn := slater_norm_sq_integral hφ ho
  rw [he] at hn
  exact hn

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockPermutations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

namespace CoulombAtom

lemma leftList_blockPerm {α : Type*} {N M : ℕ} (x : Fin (N+M) → α)
    (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    leftList (x ∘ blockPerm π ρ) = leftList x ∘ π := by
  funext i
  simp only [leftList, Function.comp_apply, blockPerm_apply_left]

lemma rightList_blockPerm {α : Type*} {N M : ℕ} (x : Fin (N+M) → α)
    (π : Equiv.Perm (Fin N)) (ρ : Equiv.Perm (Fin M)) :
    rightList (x ∘ blockPerm π ρ) = rightList x ∘ ρ := by
  funext i
  simp only [rightList, Function.comp_apply, blockPerm_apply_right]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_BlockEnergy
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators

def blockTensorCross {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) : ℝ :=
  ∑ s : Spins N, ∑ t : Spins M, ∑ i : Fin N, ∑ j : Fin M,
    ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖

open MeasureTheory
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinSpaceIntegrable
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SpinSpaceIntegrable_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma spinSpace_integrable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {F : (Fin n → SlaterParticle) → E} (hm : Measurable F)
    (hi : ∀ s : Spins n, Integrable (fun x : Configuration n => F (slaterParticles s x))) :
    Integrable F (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  have mp := (spinSpace_measurePreserving n).symm
  apply (mp.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n)).symm.measurableEmbedding).mp
  apply (integrable_prod_iff (hm.comp
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n)).symm.measurable).aestronglyMeasurable).mpr
  exact ⟨Eventually.of_forall hi, Integrable.of_finite⟩

end Work_SpinSpaceIntegrable_scope

open MeasureTheory
open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterRepulsion
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma smooth_nuclear_integrable {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun x => ‖f x‖^2 / ‖x‖) :=
  linear_coulomb_integrable (ContinuousLinearMap.id ℝ Space)
    (fun a => EuclideanSpace.single a 1) (fun _ => rfl)
    (hf.continuous.memLp_of_hasCompactSupport hc)
    (fun _a => (smooth_derivative_continuous hf _).memLp_of_hasCompactSupport (compact_derivative hc _))
    (fun a _g hg hgc => smooth_weak_gradient hf hc hg hgc (EuclideanSpace.single a 1))

lemma orbital_nuclear_integrable {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) :
    Integrable (fun z => ‖φ z‖^2 / ‖z.2‖) slaterParticleMeasure := by
  have hm : Measurable (fun z : SlaterParticle => ‖φ z‖^2 / ‖z.2‖) :=
    (((continuous_prod_of_discrete_left.mpr (fun s => (hφ s).continuous)).measurable.norm).pow_const 2).div
      measurable_snd.norm
  exact (integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨Eventually.of_forall (fun s => smooth_nuclear_integrable (hφ s) (hc s)),Integrable.of_finite⟩

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SommerfeldCoefficient
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

structure SingularProfile (d : ℝ) (F : Space → ℝ) : Prop where
  regular : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 F x
  equation : ∀ x, x ≠ 0 → Δ F x = reaction d (F x)
  decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |F x| < ε
  bounds : ∃ c > 0, ∃ C > 0, ∃ R > 0,
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x) ∧
    (∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x)

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterPole
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma orbital_pole_integrable {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) (a : Space) :
    Integrable (fun z => ‖φ z‖^2 / ‖a-z.2‖) slaterParticleMeasure := by
  have hm : Measurable (fun z : SlaterParticle => ‖φ z‖^2 / ‖a-z.2‖) :=
    (((continuous_prod_of_discrete_left.mpr (fun s => (hφ s).continuous)).measurable.norm).pow_const 2).div
      ((measurable_const.sub measurable_snd).norm)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun s => ?_),Integrable.of_finite⟩
  have hs : HasCompactSupport (fun x : Space => ‖φ (s,x)‖^2) := compact_norm_sq (hc s)
  have hd : Continuous (fun x : Space => ‖φ (s,x)‖^2) := (hφ s).continuous.norm.pow 2
  exact CoulombAnalysis.tfPotential_integrable (hd.integrable_of_hasCompactSupport hs)
    (hd.memLp_of_hasCompactSupport hs) a

lemma slater_pole_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (a : Space) (j : Fin n) :
    Integrable (fun z : Fin n → SlaterParticle => ‖slater φ z‖^2 / ‖a-(z j).2‖)
      (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (i : Fin n) : Integrable (fun z => ‖a-z.2‖⁻¹*‖φ i z‖^2) slaterParticleMeasure := by
    simpa only [div_eq_mul_inv,mul_comm] using orbital_pole_integrable (hφ i) (hc i) a
  have hv (i : Fin n) : MemLp (fun z : SlaterParticle =>
      (Real.sqrt (‖a-z.2‖⁻¹) : ℂ)*φ i z) 2 slaterParticleMeasure := memLp_potential_mul
    (continuous_prod_of_discrete_left.mpr (fun s => (hφ i s).continuous)).measurable
    (measurable_const.sub measurable_snd).norm.inv
    (fun z : SlaterParticle => inv_nonneg.mpr (norm_nonneg (a-z.2))) (hi i)
  have ht := (memLp_slaterCoordinate hl hv j).norm.integrable_sq
  simp only [slaterCoordinate_mul] at ht
  simpa only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (inv_nonneg.mpr (norm_nonneg _)),
    div_eq_mul_inv,mul_comm] using ht

lemma slaterForm_pole_trace {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (ho : ∀ i k, (∫ z, conj (φ i z)*φ k z ∂slaterParticleMeasure) = if i=k then 1 else 0)
    (a : Space) :
    (∑ s : Spins n, ∑ j : Fin n, ∫ x : Configuration n,
      ‖(slaterForm φ).value s x‖^2 / ‖a-x j‖) =
      ∑ i : Fin n, ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖a-z.2‖ ∂slaterParticleMeasure := by
  have hl (i : Fin n) := memLp_spinSpace (fun s => (hφ i s).continuous) (hc i)
  have hi (i : Fin n) : Integrable (fun z => ‖a-z.2‖⁻¹*‖φ i z‖^2) slaterParticleMeasure := by
    simpa only [div_eq_mul_inv,mul_comm] using orbital_pole_integrable (hφ i) (hc i) a
  have hv (i : Fin n) : MemLp (fun z : SlaterParticle =>
      (Real.sqrt (‖a-z.2‖⁻¹) : ℂ)*φ i z) 2 slaterParticleMeasure := memLp_potential_mul
    (continuous_prod_of_discrete_left.mpr (fun s => (hφ i s).continuous)).measurable
    (measurable_const.sub measurable_snd).norm.inv
    (fun z : SlaterParticle => inv_nonneg.mpr (norm_nonneg (a-z.2))) (hi i)
  have ht := slater_nonnegative_potential hl ho (fun z : SlaterParticle => ‖a-z.2‖⁻¹)
    (fun z => inv_nonneg.mpr (norm_nonneg _)) hv
  have his (j : Fin n) := slater_pole_integrable hφ hc a j
  have he : (∫ z : Fin n → SlaterParticle, (∑ j, ‖a-(z j).2‖⁻¹)*‖slater φ z‖^2
      ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure)) =
      ∑ s : Spins n, ∑ j : Fin n, ∫ x : Configuration n,
        ‖(slaterForm φ).value s x‖^2 / ‖a-x j‖ := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun j _ => by
      simpa only [div_eq_mul_inv,mul_comm] using his j), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∫ z : Fin n → SlaterParticle, ‖slater φ z‖^2 / ‖a-(z j).2‖
          ∂Measure.pi (fun _ : Fin n => slaterParticleMeasure) := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [div_eq_mul_inv,mul_comm]
      _ = _ := spinSpace_integral _ (his j)
  rw [he] at ht
  simpa only [div_eq_mul_inv,mul_comm] using ht

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OrbitalPole
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OrbitalPole_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

def orbitalPole (φ : SlaterParticle → ℂ) (a : Space) : ℝ :=
  ∫ z : SlaterParticle, ‖φ z‖^2 / ‖a-z.2‖ ∂slaterParticleMeasure

lemma orbitalPole_nonneg (φ : SlaterParticle → ℂ) (a : Space) : 0 ≤ orbitalPole φ a :=
  integral_nonneg (fun _z => div_nonneg (sq_nonneg _) (norm_nonneg _))

lemma orbitalPole_spins {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) (a : Space) :
    orbitalPole φ a = ∑ s : Fin 2, ∫ y : Space, ‖φ (s,y)‖^2 / ‖a-y‖ := by
  rw [orbitalPole,integral_prod _ (orbital_pole_integrable hφ hc a),integral_count]

lemma orbitalPole_continuous {φ : SlaterParticle → ℂ}
    (hφ : ∀ s, ContDiff ℝ ∞ (fun x : Space => φ (s,x)))
    (hc : ∀ s, HasCompactSupport (fun x : Space => φ (s,x))) : Continuous (orbitalPole φ) := by
  have he : orbitalPole φ = fun a => ∑ s : Fin 2, ∫ y : Space, ‖φ (s,y)‖^2 / ‖a-y‖ :=
    funext (orbitalPole_spins hφ hc)
  rw [he]
  apply continuous_finsetSum
  intro s _
  have hs := compact_norm_sq (hc s)
  have hd : Continuous (fun x : Space => ‖φ (s,x)‖^2) := (hφ s).continuous.norm.pow 2
  exact CoulombAnalysis.tfPotential_continuous (hd.integrable_of_hasCompactSupport hs)
    (hd.memLp_of_hasCompactSupport hs)

end Work_OrbitalPole_scope

open scoped BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Fermionic_SlaterOccupation
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

lemma occupationOrbitals_smooth {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x))) (m : Fin n → Bool) :
    ∀ j s, ContDiff ℝ ∞ (fun x : Space => occupationOrbitals φ m j (s,x)) :=
  fun j s => hφ (occupationIndex m j) s

lemma occupationOrbitals_compact {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x))) (m : Fin n → Bool) :
    ∀ j s, HasCompactSupport (fun x : Space => occupationOrbitals φ m j (s,x)) :=
  fun j s => hc (occupationIndex m j) s

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

def orbitalCoreInteraction {N : ℕ} (ψ : FormVector N) (φ : SlaterParticle → ℂ) : ℝ :=
  ∑ s : Spins N, ∑ j : Fin N, ∫ x : Configuration N,
    ‖ψ.value s x‖^2 * orbitalPole φ (x j)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSmoothMaxBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter Laplacian InnerProductSpace MeasureTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE

def smoothMaximum (ε : ℝ) (u v : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  v x+smoothPositive ε (u x-v x)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentPackets
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

namespace CoulombAtom

def coherentOverlap (g u : Space → ℂ) (z p : Space) : ℂ :=
  ∫ x : Space, conj (coherentPacket g z p x) * u x

lemma coherentOverlap_fourier (g u : Space → ℂ) (z ξ : Space) :
    coherentOverlap g u z ((2*Real.pi) • ξ) =
      𝓕 (fun x : Space => conj (g (x-z))*u x) ξ := by
  rw [Real.fourier_eq']
  unfold coherentOverlap coherentPacket
  apply integral_congr_ae
  filter_upwards [] with x
  have he : conj ((inner ℝ ((2*Real.pi) • ξ) x : ℂ)*Complex.I) =
      ((-2*Real.pi*inner ℝ x ξ : ℝ) : ℂ)*Complex.I := by
    simp only [inner_smul_left,conj_trivial,map_mul,Complex.conj_ofReal,Complex.conj_I,
      Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,map_ofNat,real_inner_comm ξ x]
    ring
  rw [map_mul,← Complex.exp_conj,he]
  simp only [smul_eq_mul]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FiniteFermionEnsemble
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

def finiteOccupationEnergy {n : ℕ} (Z lam : ℝ) (p : Fin n → ℝ)
    (φ : Fin n → SlaterParticle → ℂ) : ℝ :=
  (1/2:ℝ) * ∑ a : Fin 3, ∑ i : Fin n,
    p i * ∫ z, ‖spatialOrbitalDerivative φ a i z‖^2 ∂slaterParticleMeasure -
    Z * ∑ i : Fin n, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure +
    (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
      (weightedSlaterDensity p φ z.1 * weightedSlaterDensity p φ z.2) / ‖z.1.2-z.2.2‖
        ∂slaterParticleMeasure.prod slaterParticleMeasure + lam * ∑ i : Fin n, p i

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_Slater
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma slaterForm_zeroAt {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (x : Configuration n) (j : Fin n)
    (hz : ∀ i s, x j ∉ tsupport (fun y : Space => φ i (s,y))) :
    FormZeroAt (slaterForm φ) x := by
  have hv (i : Fin n) (s : Fin 2) : φ i (s,x j) = 0 := image_eq_zero_of_notMem_tsupport (f := fun y : Space => φ i (s,y)) (hz i s)
  have hd (a : Fin 3) (i : Fin n) (s : Fin 2) : spatialOrbitalDerivative φ a i (s,x j) = 0 := by
    rw [spatialOrbitalDerivative, fderiv_of_notMem_tsupport ℝ (hz i s)]
    rfl
  intro s
  constructor
  · change _ * slaterRaw φ (slaterParticles s x) = 0
    suffices hs : slaterRaw φ (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.sum_eq_zero
    intro σ _
    suffices hs : slaterTensor φ σ (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact hv (σ j) (s j)
  · intro k a
    change _ * slaterCoordinateRaw φ (spatialOrbitalDerivative φ a) k (slaterParticles s x) = 0
    suffices hs : slaterCoordinateRaw φ (spatialOrbitalDerivative φ a) k (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.sum_eq_zero
    intro σ _
    suffices hs : slaterCoordinateTensor φ (spatialOrbitalDerivative φ a) k σ (slaterParticles s x) = 0 by rw [hs,mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    by_cases hjk : j = k
    · simp only [ite_eq_left hjk,slaterParticles]
      exact hd a (σ j) (s j)
    · simp only [ite_eq_right hjk,slaterParticles]
      exact hv (σ j) (s j)

lemma occupationSlater_outside {n : ℕ} (φ : Fin n → SlaterParticle → ℂ)
    (A : Set Space) (hs : ∀ i s, Disjoint A (tsupport (fun y : Space => φ i (s,y))))
    (m : Fin n → Bool) :
    ∀ x j, x j ∈ A → FormZeroAt (slaterForm (occupationOrbitals φ m)) x := by
  intro x j hx
  apply slaterForm_zeroAt _ x j
  intro i s hi
  exact Set.disjoint_left.mp (hs (occupationIndex m i) s) hx hi

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CorrelatedFiniteInsertion
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

def spinLift (u : Space → ℂ) (σ : Fin 2) (z : SlaterParticle) : ℂ := if z.1=σ then u z.2 else 0

lemma spinLift_smooth {u : Space → ℂ} (hu : ContDiff ℝ ∞ u) (σ s : Fin 2) :
    ContDiff ℝ ∞ (fun x : Space => spinLift u σ (s,x)) := by
  by_cases h : s=σ <;> simp only [spinLift,h,ite_true,ite_false]
  · exact hu
  · exact contDiff_const

lemma spinLift_compact {u : Space → ℂ} (hu : HasCompactSupport u) (σ s : Fin 2) :
    HasCompactSupport (fun x : Space => spinLift u σ (s,x)) := by
  by_cases h : s=σ <;> simp only [spinLift,h,ite_true,ite_false]
  · exact hu
  · exact HasCompactSupport.zero

lemma spinLift_separated {u : Space → ℂ} {A : Set Space}
    (hu : Disjoint A (tsupport u)) (σ s : Fin 2) :
    Disjoint A (tsupport (fun x : Space => spinLift u σ (s,x))) := by
  by_cases h : s=σ <;> simp only [spinLift,h,ite_true,ite_false]
  · exact hu
  · simp

lemma spinLift_fderiv (u : Space → ℂ) (σ s : Fin 2) (x v : Space) :
    fderiv ℝ (fun y : Space => spinLift u σ (s,y)) x v =
      spinLift (fun y => fderiv ℝ u y v) σ (s,x) := by
  by_cases h : s=σ <;> simp [spinLift,h]

lemma spinLift_inner (u v : Space → ℂ) (σ τ : Fin 2) :
    (∫ z : SlaterParticle, conj (spinLift u σ z) * spinLift v τ z ∂slaterParticleMeasure) =
      if σ=τ then ∫ x : Space, conj (u x)*v x else 0 := by
  have he (z : SlaterParticle) : conj (spinLift u σ z) * spinLift v τ z =
      (if z.1=σ ∧ z.1=τ then (1:ℂ) else 0) * (conj (u z.2)*v z.2) := by
    simp only [spinLift]
    (split_ifs <;> simp_all); aesop
  simp_rw [he]
  rw [show slaterParticleMeasure = Measure.count.prod volume from rfl,
    integral_prod_mul (fun s : Fin 2 => if s=σ ∧ s=τ then (1:ℂ) else 0)
      (fun x : Space => conj (u x)*v x),integral_count]
  by_cases h : σ=τ
  · subst τ
    simp
  · have hz : (fun s : Fin 2 => if s=σ ∧ s=τ then (1:ℂ) else 0) = 0 := by
      funext s
      simp only [Pi.zero_apply,ite_eq_right_iff,one_ne_zero,imp_false]
      exact fun hs => h (hs.1.symm.trans hs.2)
    simp only [hz,Pi.zero_apply,Finset.sum_const_zero,zero_mul,ite_eq_right h]

lemma spinLift_weight (u : Space → ℂ) (σ : Fin 2) (W : Space → ℝ) :
    (∫ z : SlaterParticle, W z.2 * ‖spinLift u σ z‖^2 ∂slaterParticleMeasure) =
      ∫ x : Space, W x * ‖u x‖^2 := by
  have he (z : SlaterParticle) : W z.2 * ‖spinLift u σ z‖^2 =
      (if z.1=σ then (1:ℝ) else 0) * (W z.2 * ‖u z.2‖^2) := by
    by_cases h : z.1=σ <;> simp [spinLift,h]
  simp_rw [he]
  rw [show slaterParticleMeasure = Measure.count.prod volume from rfl,
    integral_prod_mul (fun s : Fin 2 => if s=σ then (1:ℝ) else 0)
      (fun x : Space => W x*‖u x‖^2),integral_count]
  simp

lemma spinLift_mass (u : Space → ℂ) (σ : Fin 2) :
    (∫ z : SlaterParticle, ‖spinLift u σ z‖^2 ∂slaterParticleMeasure) = ∫ x : Space, ‖u x‖^2 := by
  simpa only [one_mul] using spinLift_weight u σ (fun _ => 1)

lemma spinLift_derivative_mass (u : Space → ℂ) (σ : Fin 2) (v : Space) :
    (∫ z : SlaterParticle, ‖fderiv ℝ (fun y : Space => spinLift u σ (z.1,y)) z.2 v‖^2
      ∂slaterParticleMeasure) = ∫ x : Space, ‖fderiv ℝ u x v‖^2 := by
  simp_rw [spinLift_fderiv]
  exact spinLift_mass _ σ

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

universe u

def finiteOrbitalKinetic {ι : Type u} [Fintype ι] (p : ι → ℝ)
    (φ : ι → SlaterParticle → ℂ) : ℝ :=
  (1/2:ℝ) * ∑ a : Fin 3, ∑ i, p i * ∫ z : SlaterParticle,
    ‖fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure

def finiteOrbitalEnergy {ι : Type u} [Fintype ι] (Z lam : ℝ) (p : ι → ℝ)
    (φ : ι → SlaterParticle → ℂ) : ℝ :=
  finiteOrbitalKinetic p φ -
    Z * ∑ i, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure +
    (1/2:ℝ) * ∫ z : SlaterParticle × SlaterParticle,
      (finiteOrbitalDensity p φ z.1 * finiteOrbitalDensity p φ z.2) / ‖z.1.2-z.2.2‖
        ∂slaterParticleMeasure.prod slaterParticleMeasure + lam * ∑ i, p i

lemma finiteOrbitalEnergy_reindex {ι : Type u} [Fintype ι] {n : ℕ}
    (e : Fin n ≃ ι) (Z lam : ℝ) (p : ι → ℝ) (φ : ι → SlaterParticle → ℂ) :
    finiteOccupationEnergy Z lam (p ∘ e) (φ ∘ e) = finiteOrbitalEnergy Z lam p φ := by
  unfold finiteOccupationEnergy finiteOrbitalEnergy finiteOrbitalKinetic spatialOrbitalDerivative
  simp only [Function.comp_apply]
  have hd (z : SlaterParticle) : weightedSlaterDensity (p ∘ e) (φ ∘ e) z = finiteOrbitalDensity p φ z :=
    e.sum_comp (fun i => p i * ‖φ i z‖^2)
  simp only [hd]
  have hk (a : Fin 3) :
      (∑ j : Fin n, p (e j) * ∫ z : SlaterParticle,
        ‖fderiv ℝ (fun x : Space => φ (e j) (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure) =
      ∑ i, p i * ∫ z : SlaterParticle,
        ‖fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure :=
    e.sum_comp (fun i => p i * ∫ z : SlaterParticle,
      ‖fderiv ℝ (fun x : Space => φ i (z.1,x)) z.2 (EuclideanSpace.single a 1)‖^2 ∂slaterParticleMeasure)
  have hn : (∑ j : Fin n, p (e j) * ∫ z : SlaterParticle, ‖φ (e j) z‖^2 / ‖z.2‖ ∂slaterParticleMeasure) =
      ∑ i, p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure :=
    e.sum_comp (fun i => p i * ∫ z : SlaterParticle, ‖φ i z‖^2 / ‖z.2‖ ∂slaterParticleMeasure)
  simp only [hk,hn,e.sum_comp p]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinFinite
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff

namespace CoulombAtom

lemma spinSpace_map_spatial : Measure.map Prod.snd slaterParticleMeasure = (2:ENNReal) • (volume : Measure Space) := by
  rw [show slaterParticleMeasure = Measure.count.prod volume from rfl,Measure.map_snd_prod]
  simp

lemma spinPair_map_spatial :
    Measure.map (Prod.map Prod.snd Prod.snd) (slaterParticleMeasure.prod slaterParticleMeasure) =
      (4:ENNReal) • (volume : Measure (Space × Space)) := by
  rw [← Measure.map_prod_map _ _ measurable_snd measurable_snd,spinSpace_map_spatial]
  norm_num [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.volume_eq_prod]

lemma spinPair_integral_spatial {F : Space × Space → ℝ} (hF : Measurable F) :
    (∫ z : SlaterParticle × SlaterParticle, F (z.1.2,z.2.2)
      ∂slaterParticleMeasure.prod slaterParticleMeasure) = 4 * ∫ x : Space × Space, F x := by
  have h := integral_map (μ := slaterParticleMeasure.prod slaterParticleMeasure)
    ((measurable_snd.prodMap measurable_snd).aemeasurable) hF.aestronglyMeasurable
  rw [spinPair_map_spatial,integral_smul_measure] at h
  simpa only [ENNReal.toReal_ofNat,smul_eq_mul,Prod.map_apply'] using h.symm

def spatialFiniteDensity {ι : Type*} [Fintype ι] (p : ι → ℝ) (u : ι → Space → ℂ) (x : Space) : ℝ :=
  ∑ i, p i * ‖u i x‖^2

lemma spinFinite_density {ι : Type*} [Fintype ι] (p : ι → ℝ) (u : ι → Space → ℂ) (z : SlaterParticle) :
    finiteOrbitalDensity (fun i : Fin 2 × ι => p i.2) (fun i => spinLift (u i.2) i.1) z =
      spatialFiniteDensity p u z.2 := by
  classical
  rcases z with ⟨σ,x⟩
  simp only [finiteOrbitalDensity,Fintype.sum_prod_type,spinLift]
  rw [Finset.sum_comm]
  fin_cases σ <;> simp [spatialFiniteDensity]

lemma spinFinite_kinetic {ι : Type*} [Fintype ι] (p : ι → ℝ) (u : ι → Space → ℂ) :
    finiteOrbitalKinetic (fun i : Fin 2 × ι => p i.2) (fun i => spinLift (u i.2) i.1) =
      ∑ a : Fin 3, ∑ i, p i * ∫ x : Space, ‖fderiv ℝ (u i) x (EuclideanSpace.single a 1)‖^2 := by
  simp only [finiteOrbitalKinetic,Fintype.sum_prod_type,spinLift_derivative_mass,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma spinFinite_orthonormal {ι : Type*} [DecidableEq ι] {u : ι → Space → ℂ}
    (hu : ∀ i j, (∫ x : Space, conj (u i x) * u j x) = if i=j then 1 else 0)
    (i j : Fin 2 × ι) :
    (∫ z, conj (spinLift (u i.2) i.1 z)*spinLift (u j.2) j.1 z ∂slaterParticleMeasure) =
      if i=j then 1 else 0 := by
  rw [spinLift_inner,hu]
  by_cases h : i.1=j.1 <;> by_cases k : i.2=j.2 <;> simp [h,k,Prod.ext_iff]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_CompactPotential
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ContDiff

lemma compact_potential_bounded {d : Space → ℝ} (hd : Continuous d) (hcd : HasCompactSupport d) :
    ∃ C : ℝ, ∀ x : Space, |CoulombAnalysis.tfPotential d x| ≤ C := by
  have h1 : Integrable d := hd.integrable_of_hasCompactSupport hcd
  have hp : MemLp d (5/3 : ENNReal) := hd.memLp_of_hasCompactSupport hcd
  obtain ⟨R,_,hR⟩ := hcd.isBounded.exists_pos_norm_le
  have hs (y : Space) (hy : d y ≠ 0) : ‖y‖ ≤ R := hR y (subset_tsupport d hy)
  obtain ⟨S,_,hS⟩ := CoulombAnalysis.tfPotential_compact_decay h1 hp hs 1 zero_lt_one
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Space) S).exists_bound_of_continuousOn
    (CoulombAnalysis.tfPotential_continuous h1 hp).continuousOn
  refine ⟨max C 1,fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ S
  · exact (hC x (by simpa using hx)).trans (le_max_left _ _)
  · exact (hS x (le_of_not_ge hx)).trans (le_max_right _ _)

lemma spinLift_pole (u : Space → ℂ) (σ : Fin 2) (a : Space) :
    orbitalPole (spinLift u σ) a = CoulombAnalysis.tfPotential (fun y => ‖u y‖^2) a := by
  unfold orbitalPole CoulombAnalysis.tfPotential
  simpa only [div_eq_mul_inv,mul_comm] using spinLift_weight u σ (fun x => ‖a-x‖⁻¹)

section Work_CompactDirect_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

lemma continuous_compact_coulomb_integrable {f g : Space → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    Integrable (fun r : Space × Space => f r.1 * g r.2 / ‖r.1-r.2‖) := by
  have hm : Measurable (fun r : Space × Space => f r.1 * g r.2 / ‖r.1-r.2‖) :=
    ((hf.measurable.comp measurable_fst).mul (hg.measurable.comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm)
  have hg1 : Integrable g := hg.integrable_of_hasCompactSupport hcg
  have hgp : MemLp g (5/3 : ENNReal) := hg.memLp_of_hasCompactSupport hcg (p := (5/3 : ENNReal))
  have hgn1 : Integrable (fun x => ‖g x‖) := hg.norm.integrable_of_hasCompactSupport hcg.norm
  have hgnp : MemLp (fun x => ‖g x‖) (5/3 : ENNReal) := hg.norm.memLp_of_hasCompactSupport hcg.norm (p := (5/3 : ENNReal))
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  refine ⟨Eventually.of_forall (fun x => ?_),?_⟩
  · simpa only [mul_div_assoc] using (CoulombAnalysis.tfPotential_integrable hg1 hgp x).const_mul (f x)
  · have hi : Integrable (fun x => ‖f x‖ * CoulombAnalysis.tfPotential (fun y => ‖g y‖) x) := (hf.norm.mul (CoulombAnalysis.tfPotential_continuous hgn1 hgnp)).integrable_of_hasCompactSupport
      hcf.norm.mul_right
    apply hi.congr
    filter_upwards [] with x
    simp only [norm_div,norm_mul,norm_norm,CoulombAnalysis.tfPotential,← integral_const_mul]
    congr 1
    funext y
    ring

lemma spatialFiniteDensity_continuous {ι : Type*} [Fintype ι] (p : ι → ℝ) {u : ι → Space → ℂ}
    (hu : ∀ i, Continuous (u i)) : Continuous (spatialFiniteDensity p u) := by
  unfold spatialFiniteDensity
  fun_prop

lemma spatialFiniteDensity_compact {ι : Type*} [Fintype ι] (p : ι → ℝ) {u : ι → Space → ℂ}
    (hu : ∀ i, HasCompactSupport (u i)) : HasCompactSupport (spatialFiniteDensity p u) := by
  unfold spatialFiniteDensity
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ((compact_norm_sq (hu a)).mul_left).add ih

lemma spatialFiniteDensity_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ} {u : ι → Space → ℂ}
    (hp : ∀ i, 0 ≤ p i) (x : Space) : 0 ≤ spatialFiniteDensity p u x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _))

lemma compact_direct_mono {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g)
    (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ g x) :
    (∫ r : Space × Space, f r.1 * f r.2 / ‖r.1-r.2‖) ≤
      ∫ r : Space × Space, g r.1 * g r.2 / ‖r.1-r.2‖ := by
  apply integral_mono (continuous_compact_coulomb_integrable hf hf hcf hcf)
    (continuous_compact_coulomb_integrable hg hg hcg hcg)
  intro r
  exact div_le_div_of_nonneg_right (mul_le_mul (hb r.1) (hb r.2) (hn r.2)
    ((hn r.1).trans (hb r.1))) (norm_nonneg _)

end Work_CompactDirect_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmearingPotential
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

def spatialSmearing (η ρ : Space → ℝ) (x : Space) : ℝ := ∫ z : Space, ρ z*η (x-z)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DiffuseSeed
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

def diffuseSeed (R : ℝ) (x : Configuration 1) : ℂ := trialSeed 1 (R⁻¹ • x)

def diffuseRaw (R : ℝ) : FormVector 1 := smoothForm (diffuseSeed R)

def diffuseOrbital (R : ℝ) : FormVector 1 :=
  scaleForm (Real.sqrt (formMass (diffuseRaw R)))⁻¹ (diffuseRaw R)


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


open MeasureTheory Filter
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierWeakMaxBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

def WeakLaplacianLowerOn (U : Set TFSpace) (u h : TFSpace → ℝ) : Prop :=
  ∀ φ : TFSpace → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
    tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) →
    (∫ x, h x*φ x) ≤ ∫ x, u x*Δ φ x

def maxKernel (n : ℕ) : TFSpace → ℝ := (shrinkingBump n).normed volume

def maxMollify (n : ℕ) (u : TFSpace → ℝ) : TFSpace → ℝ :=
  maxKernel n ⋆[newtonMul] u

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNuclearBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

def nuclearField (Z : ℝ) (x : TFSpace) : ℝ := Z/‖x‖

def clippedNuclearField (Z R : ℝ) (x : TFSpace) : ℝ := Z/max R ‖x‖

def WeakNuclearLowerOn (U : Set TFSpace) (Z : ℝ) (u h : TFSpace → ℝ) : Prop :=
  ∀ φ : TFSpace → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
    tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) →
    -(4*Real.pi*Z)*φ 0+(∫ x, h x*φ x) ≤ ∫ x, u x*Δ φ x

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentHilbert
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoherentHilbert_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff FourierTransform Topology

lemma coherentVector_coe {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q : Space × Space) : coherentVector hg hcg q =ᵐ[volume] coherentPacket g q.1 q.2 :=
  MemLp.coeFn_toLp _

lemma coherentVector_inner {g : Space → ℂ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (q r : Space × Space) :
    inner ℂ (coherentVector hg hcg q) (coherentVector hg hcg r) =
      coherentOverlap g (coherentPacket g r.1 r.2) q.1 q.2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coherentVector_coe hg hcg q,coherentVector_coe hg hcg r] with x hq hr
  rw [hq,hr]
  simp only [RCLike.inner_apply,mul_comm]

end Work_CoherentHilbert_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoherentSchwartz
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoherentSchwartz_scope

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

lemma coherentOverlap_momentum_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) (z : Space) :
    ((2*Real.pi)^3)⁻¹ * (∫ p : Space, ‖coherentOverlap g u z p‖^2) =
      ∫ x : Space, ‖g (x-z)‖^2 * ‖u x‖^2 := by
  have hc := coherentWindow_compact (u := u) hcg z
  have hd : ContDiff ℝ ∞ (fun x : Space => conj (g (x-z))*u x) :=
    (Complex.conjCLE.contDiff.comp (hg.comp (contDiff_id.sub contDiff_const))).mul (u.smooth ⊤)
  have hp := SchwartzMap.integral_norm_sq_fourier (hc.toSchwartzMap hd)
  change (∫ ξ : Space, ‖𝓕 (fun x : Space => conj (g (x-z))*u x) ξ‖^2) =
    ∫ x : Space, ‖conj (g (x-z))*u x‖^2 at hp
  simp_rw [← coherentOverlap_fourier,norm_mul,Complex.norm_conj,mul_pow] at hp
  rw [Measure.integral_comp_smul_of_nonneg volume (fun p : Space => ‖coherentOverlap g u z p‖^2)
    (2*Real.pi) (hR := by positivity),space_finrank] at hp
  simpa only [zpow_neg,zpow_natCast,smul_eq_mul] using hp

lemma coherentOverlap_momentum_integrable_schwartz {g : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (u : SchwartzMap Space ℂ) (z : Space) :
    Integrable (fun p : Space => ‖coherentOverlap g u z p‖^2) := by
  rw [← integrable_comp_smul_iff volume (fun p : Space => ‖coherentOverlap g u z p‖^2)
    (show 2*Real.pi ≠ 0 by positivity)]
  simp_rw [coherentOverlap_fourier]
  have hc := coherentWindow_compact (u := u) hcg z
  have hd : ContDiff ℝ ∞ (fun x : Space => conj (g (x-z))*u x) :=
    (Complex.conjCLE.contDiff.comp (hg.comp (contDiff_id.sub contDiff_const))).mul (u.smooth ⊤)
  have hi := ((𝓕 (hc.toSchwartzMap hd)).memLp 2 volume).norm.integrable_sq
  change Integrable (fun x : Space => ‖𝓕 (fun x : Space => conj (g (x-z))*u x) x‖^2) at hi
  exact hi

end Work_CoherentSchwartz_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

lemma coherentVector_inner_schwartz {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (q : Space × Space) (u : SchwartzMap Space ℂ) :
    inner ℂ (coherentVector hg hcg q) (u.toLp 2) = coherentOverlap g u q.1 q.2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coherentVector_coe hg hcg q,u.coeFn_toLp 2 volume] with x hq hu
  rw [hq,hu]
  simp only [RCLike.inner_apply,mul_comm]

lemma schwartz_toLp_norm_sq (u : SchwartzMap Space ℂ) :
    ‖u.toLp 2‖^2 = ∫ x : Space, ‖u x‖^2 := by
  rw [lp_norm_sq]
  exact integral_congr_ae ((u.coeFn_toLp 2 volume).fun_comp (fun t : ℂ => ‖t‖^2))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CompactEigenbasis
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CompactEigenbasis_scope

open MeasureTheory Filter Module
open scoped BigOperators ComplexConjugate Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compactEigenspaceBasis (T : H →L[ℂ] H) (μ : ℂ) :
    HilbertBasis (compactEigenspaceIndex T μ) ℂ (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap μ)).choose_spec.choose

def compactSpectralVector (T : H →L[ℂ] H) (i : CompactSpectralIndex T) : H :=
  compactEigenspaceBasis T i.1 i.2

lemma compactSpectralVector_eigen (T : H →L[ℂ] H) (i : CompactSpectralIndex T) :
    T (compactSpectralVector T i) = i.1 • compactSpectralVector T i :=
  Module.End.mem_eigenspace_iff.mp (compactEigenspaceBasis T i.1 i.2).property

lemma compactSpectralVector_orthonormal (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric) :
    Orthonormal ℂ (compactSpectralVector T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun μ => (compactEigenspaceBasis T μ).orthonormal)

lemma compactSpectralVector_orthogonal_eq_bot (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    (Submodule.span ℂ (Set.range (compactSpectralVector T)))ᗮ = ⊥ := by
  let S := Submodule.span ℂ (Set.range (compactSpectralVector T))
  have hs : (⨆ μ, Module.End.eigenspace T.toLinearMap μ) ≤ S.topologicalClosure := by
    apply iSup_le
    intro μ y hy
    let v : Module.End.eigenspace T.toLinearMap μ := ⟨y,hy⟩
    have hh := ((compactEigenspaceBasis T μ).hasSum_repr v).mapL
      (Module.End.eigenspace T.toLinearMap μ).subtypeL
    apply mem_closure_of_tendsto hh
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    change ((compactEigenspaceBasis T μ).repr v i) • (compactSpectralVector T ⟨μ,i⟩) ∈ S
    exact S.smul_mem _ (Submodule.subset_span ⟨⟨μ,i⟩,rfl⟩)
  apply le_antisymm _ bot_le
  rw [← S.orthogonal_closure]
  exact (Submodule.orthogonal_le hs).trans
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs).le

def compactSpectralBasis (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    HilbertBasis (CompactSpectralIndex T) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (compactSpectralVector_orthonormal T hTs)
    (compactSpectralVector_orthogonal_eq_bot T hTc hTs)

lemma compactSpectralBasis_apply (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) : compactSpectralBasis T hTc hTs i = compactSpectralVector T i := by
  rw [compactSpectralBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma compactSpectralBasis_eigen (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) :
    T (compactSpectralBasis T hTc hTs i) = i.1 • compactSpectralBasis T hTc hTs i := by
  simp only [compactSpectralBasis_apply,compactSpectralVector_eigen]

end Work_CompactEigenbasis_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

instance orbitalHilbert_secondCountable : SecondCountableTopology OrbitalHilbert := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SmoothCompactIntegral
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff Topology

def packetSynthesis (g : Space → ℂ) (μ : Measure (Space × Space))
    (w : Space × Space → ℂ) (x : Space) : ℂ :=
  ∫ q, w q * coherentPacket g q.1 q.2 x ∂μ

lemma coherentVector_inner_schwartz_left {g : Space → ℂ} (hg : Continuous g)
    (hcg : HasCompactSupport g) (q : Space × Space) (v : SchwartzMap Space ℂ) :
    inner ℂ (v.toLp 2) (coherentVector hg hcg q) =
      ∫ x : Space, conj (v x) * coherentPacket g q.1 q.2 x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [v.coeFn_toLp 2 volume,coherentVector_coe hg hcg q] with x hv hq
  rw [hv,hq]
  simp only [RCLike.inner_apply,mul_comm]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FermiDensity
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma coulomb_potential_pair_comm {f g : Space → ℝ}
    (hi : Integrable (fun r : Space × Space => f r.1*g r.2/‖r.1-r.2‖)) :
    (∫ x : Space, f x*CoulombAnalysis.tfPotential g x) =
      ∫ x : Space, g x*CoulombAnalysis.tfPotential f x := by
  simp only [CoulombAnalysis.tfPotential,← integral_const_mul]
  have hi' : Integrable (fun r : Space × Space => f r.1*(g r.2/‖r.1-r.2‖)) (volume.prod volume) := by
    simpa only [mul_div_assoc,Measure.volume_eq_prod] using hi
  rw [integral_integral_swap hi']
  apply integral_congr_ae
  filter_upwards [] with x
  apply integral_congr_ae
  filter_upwards [] with y
  rw [norm_sub_rev x y]
  ring

lemma square_compact {g : Space → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (fun x => (g x)^2) := hg.comp_left (g := fun t : ℝ => t^2) (by simp)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierInitialPoissonBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped BigOperators ContDiff Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

def initialOffset (Z r a : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  -tfPotential ρ x-(7/10)*Z/r+a*‖x‖^2

def initialBranch (Z r a : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  nuclearField Z x+initialOffset Z r a ρ x

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BoundedL1PoissonBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

def meanFieldOffset (lam : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ := -tfPotential ρ x-lam

end CoulombBarrier

end Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_StripAveraging
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombRadialAveraging

lemma slidingCount_eq_sum_upper {N : ℕ} (d : Fin N → ℝ) (l r hi t : ℝ) (ht : t ≤ hi) :
    slidingCount d l r t = ∑ i ∈ Finset.univ.filter (fun i => d i ≤ hi+r),
      slidingBit l r (d i) t := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi'
  have hh : ¬ d i ≤ hi+r := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi'
  unfold slidingBit
  rw [ite_eq_right]
  intro h
  exact hh (by linarith [h.1])

theorem slidingCount_square_integral {N : ℕ} (d : Fin N → ℝ) (lo hi : ℝ)
    {l r : ℝ} (h : 0 ≤ l+r) :
    (∫ t in Icc lo hi, slidingCount d l r t^2) ≤
      (l+r)*upperCount d (hi+r)^2 := by
  classical
  let S := Finset.univ.filter (fun i => d i ≤ hi+r)
  have he (t : ℝ) (ht : t ∈ Icc lo hi) := slidingCount_eq_sum_upper d l r hi t ht.2
  have hs (t : ℝ) : (∑ i ∈ S, slidingBit l r (d i) t) ≤ (S.card:ℝ) := by
    simpa only [nsmul_eq_mul,mul_one] using
      Finset.sum_le_card_nsmul S (fun i => slidingBit l r (d i) t) 1
        (fun _ _ => slidingBit_le_one _ _ _ _)
  have hint : Integrable (fun t => (S.card:ℝ)*∑ i ∈ S, slidingBit l r (d i) t)
      (volume.restrict (Icc lo hi)) :=
    (integrable_finsetSum _ (fun i _ => (slidingBit_integrable l r (d i)).restrict)).const_mul _
  calc
    _ ≤ ∫ t in Icc lo hi, (S.card:ℝ)*∑ i ∈ S, slidingBit l r (d i) t := by
      apply integral_mono_ae
        (slidingCount_sq_integrable (d := fun _ : ℝ => d) (fun _ => measurable_const) measurable_id l r) hint
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      change slidingCount d l r t^2 ≤ _
      rw [he t ht]
      have hn := Finset.sum_nonneg (s := S) (fun i _ => slidingBit_nonneg l r (d i) t)
      have hh := mul_le_mul_of_nonneg_right (hs t) hn
      nlinarith
    _ = (S.card:ℝ)*∑ i ∈ S, ∫ t in Icc lo hi, slidingBit l r (d i) t := by
      rw [integral_const_mul,integral_finsetSum _
        (fun i _ => (slidingBit_integrable l r (d i)).restrict)]
    _ ≤ (S.card:ℝ)*∑ _i ∈ S, (l+r) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun i _ => slidingBit_setIntegral_le h (d i) lo hi)) (Nat.cast_nonneg _)
    _ = (l+r)*upperCount d (hi+r)^2 := by
      rw [upperCount_eq_card]
      simp only [Finset.sum_const,nsmul_eq_mul]
      dsimp only [S]
      ring

theorem expected_slidingCount_square_integral {α : Type*} [MeasurableSpace α]
    {N : ℕ} {d : α → Fin N → ℝ} (hd : ∀ i, Measurable (fun x => d x i))
    (μ : Measure α) [IsFiniteMeasure μ] (lo hi : ℝ) {l r : ℝ} (h : 0 ≤ l+r) :
    (∫ t in Icc lo hi, ∫ x, slidingCount (d x) l r t^2 ∂μ) ≤
      (l+r)*(∫ x, upperCount (d x) (hi+r)^2 ∂μ) := by
  have hp : Integrable (fun p : ℝ × α => slidingCount (d p.2) l r p.1^2)
      ((volume.restrict (Icc lo hi)).prod μ) :=
    slidingCount_sq_integrable (fun i => (hd i).comp measurable_snd) measurable_fst l r
  rw [integral_integral_swap hp,←integral_const_mul]
  apply integral_mono hp.integral_prod_right ((upperCount_sq_integrable hd (hi+r)).const_mul _)
  intro x
  exact slidingCount_square_integral (d x) lo hi h

theorem exists_radius_expected_square {α : Type*} [MeasurableSpace α]
    {N : ℕ} {d : α → Fin N → ℝ} (hd : ∀ i, Measurable (fun x => d x i))
    (μ : Measure α) [IsFiniteMeasure μ] {lo hi l r : ℝ}
    (hab : lo < hi) (h : 0 ≤ l+r) :
    ∃ t ∈ Icc lo hi, (∫ x, slidingCount (d x) l r t^2 ∂μ) ≤
      ((l+r)/(hi-lo))*(∫ x, upperCount (d x) (hi+r)^2 ∂μ) := by
  let ν := volume.restrict (Icc lo hi)
  have hνreal : ν.real univ = hi-lo := by
    simp only [ν,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_pos.mpr hab).le]
  have hν : ν ≠ 0 := by
    intro hh
    have hz : ν.real univ = 0 := by rw [hh]; simp
    rw [hνreal] at hz
    linarith
  have hp : Integrable (fun p : ℝ × α => slidingCount (d p.2) l r p.1^2) (ν.prod μ) :=
    slidingCount_sq_integrable (fun i => (hd i).comp measurable_snd) measurable_fst l r
  have hn : ν (Icc lo hi)ᶜ = 0 := by
    simp only [ν,Measure.restrict_apply measurableSet_Icc.compl,compl_inter_self,measure_empty]
  obtain ⟨t,ht,havg⟩ := exists_notMem_null_le_average hν hp.integral_prod_left hn
  refine ⟨t,not_not.mp ht,?_⟩
  rw [average_eq,hνreal,smul_eq_mul] at havg
  have hb := expected_slidingCount_square_integral hd μ lo hi h
  calc
    _ ≤ (hi-lo)⁻¹*(∫ t in Icc lo hi, ∫ x, slidingCount (d x) l r t^2 ∂μ) := havg
    _ ≤ (hi-lo)⁻¹*((l+r)*(∫ x, upperCount (d x) (hi+r)^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (sub_pos.mpr hab).le)
    _ = _ := by ring

end CoulombRadialAveraging

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FormRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombRadialAveraging

def rawStripCount {N : ℕ} (y : Space) (t b : ℝ) (x : Configuration N) : ℝ :=
  slidingCount (fun i => ‖x i-y‖) (7*b) b t

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpinEnergy
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SpinEnergy_scope

open MeasureTheory
open scoped BigOperators ContDiff

lemma spinFinite_energy {ι : Type*} [Fintype ι] (p : ι → ℝ) {u : ι → Space → ℂ}
    (hu : ∀ i, Continuous (u i)) (Z lam : ℝ) :
    finiteOrbitalEnergy Z lam (fun i : Fin 2 × ι => p i.2) (fun i => spinLift (u i.2) i.1) =
      (∑ a : Fin 3, ∑ i, p i * ∫ x : Space, ‖fderiv ℝ (u i) x (EuclideanSpace.single a 1)‖^2) -
      2*Z*(∑ i, p i * CoulombAnalysis.tfPotential (fun y => ‖u i y‖^2) 0) +
      2 * (∫ r : Space × Space, spatialFiniteDensity p u r.1 * spatialFiniteDensity p u r.2 / ‖r.1-r.2‖) +
      2*lam*(∑ i, p i) := by
  have ht (i : Fin 2 × ι) :
      (∫ z : SlaterParticle, ‖spinLift (u i.2) i.1 z‖^2 / ‖z.2‖ ∂slaterParticleMeasure) =
      CoulombAnalysis.tfPotential (fun y => ‖u i.2 y‖^2) 0 := by
    simpa only [orbitalPole,zero_sub,norm_neg] using spinLift_pole (u i.2) i.1 0
  have hd := spatialFiniteDensity_continuous p hu
  have hm : Measurable (fun r : Space × Space =>
      spatialFiniteDensity p u r.1 * spatialFiniteDensity p u r.2 / ‖r.1-r.2‖) :=
    ((hd.measurable.comp measurable_fst).mul (hd.measurable.comp measurable_snd)).div
      ((measurable_fst.sub measurable_snd).norm)
  simp only [finiteOrbitalEnergy,spinFinite_kinetic,ht,spinFinite_density]
  rw [spinPair_integral_spatial hm]
  simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end Work_SpinEnergy_scope

open MeasureTheory Filter
open scoped BigOperators ContDiff

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_CoherentRealKinetic
attribute [-instance] _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma real_derivative_sq_integrable {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hcg : HasCompactSupport g) (v : Space) :
    Integrable (fun x : Space => (fderiv ℝ g x v)^2) := by
  have hc : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hc.memLp_of_hasCompactSupport (hcg.fderiv_apply ℝ v) (p := 2)).integrable_sq

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

lemma potential_const_mul (c : ℝ) (f : Space → ℝ) (a : Space) :
    CoulombAnalysis.tfPotential (fun x => c*f x) a = c*CoulombAnalysis.tfPotential f a := by
  simp only [CoulombAnalysis.tfPotential,mul_div_assoc,integral_const_mul]

lemma coulomb_double_const_mul (c : ℝ) (f : Space → ℝ) :
    (∫ r : Space × Space, (c*f r.1)*(c*f r.2)/‖r.1-r.2‖) =
      c^2*(∫ r : Space × Space, f r.1*f r.2/‖r.1-r.2‖) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with r
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

def arrayFisher {J I : Type*} [Fintype J] [Fintype I] [DecidableEq I]
    (b : J → ℝ) (s : Set (J × I → ℝ)) (x : I → ℝ) : ℝ :=
  ∑ i, (lineDeriv ℝ (fun y => Real.sqrt (arrayLikelihood b s y)) x (Pi.single i 1))^2

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegratedTruncatedControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_3 (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedTruncatedControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ExpectedTruncatedControl_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

open CoulombNeumann CoulombAnalysis
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_4 (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _

end Work_ExpectedTruncatedControl_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTruncationBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

def DeterministicLocalBound {Ω : Type*} (u : Ω → TFSpace → ℝ) : Prop :=
  ∀ K : Set TFSpace, IsCompact K → ∃ C : ℝ, ∀ sample x, x ∈ K → ‖u sample x‖ ≤ C

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_Conditional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators
namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom
variable {Ω D : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable [MeasurableSpace D] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Ω → D) (hX : Measurable X)

def conditionalField (u : Ω → TFSpace → ℝ) (d : D) (x : TFSpace) : ℝ :=
  ∫ sample, u sample x ∂condDistrib id X P d

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LaplacianCompDilation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombPDE

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

open Filter Set Metric Topology InnerProductSpace Laplacian

def shiftedDilation (a : ℝ) (F : Space → ℝ) (x : Space) : ℝ := a^4*F (a • x) + (1-a^4)

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchCenterObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
local instance patchCenterMeasurableSpace (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchLocalObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
local instance instMeasurableSpacePatchLocalObservableTFLp (R : ℝ) :
    MeasurableSpace (TFLp (ballMeasure R)) := borel _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PosteriorFreshTestBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal ENNReal

namespace CoulombAtom
open CoulombObservation CoulombNeumann CoulombAnalysis
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_5 (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTowerBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSourceTower_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] masterWidth 

def innerSource (R : ℝ) (μ p : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  4*Real.pi*((if ‖x‖ < R then μ x else 0)-p x)

def outerCoefficient (R : ℝ) (x : TFSpace) : ℝ := if R ≤ ‖x‖ then 1 else 0

end Work_BarrierSourceTower_barrier_scope

open Set Filter Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

def outerBarrier (B r : ℝ) (x : Space) : ℝ :=
  B / ‖x‖^4 * (1-r/(8*‖x‖))

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOuterWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis

def clippedOuterBarrier (B r : ℝ) (x : TFSpace) : ℝ :=
  B/(max r ‖x‖)^4*(1-r/(8*max r ‖x‖))

def outerOffset (Z B r : ℝ) (x : TFSpace) : ℝ :=
  clippedOuterBarrier B r x-clippedNuclearField Z r x

end Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

def cutMaximum (r R : ℝ) (u v : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  if ‖x‖ < r then u x else if ‖x‖ < R then max (u x) (v x) else v x

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialBoundsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped ContDiff Topology

open CoulombAnalysis

def initializedOffset (Z B r a : ℝ) (ρ : TFSpace → ℝ) : TFSpace → ℝ :=
  cutMaximum r (2*r) (initialOffset Z r a ρ) (outerOffset Z B r)

def initializedBarrier (Z B r a : ℝ) (ρ : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  nuclearField Z x+initializedOffset Z B r a ρ x

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitializationBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis
attribute [local instance] Classical.propDecidable

variable {Ω : Type*}

def initialCharge (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) (sample : Ω) (x : TFSpace) : ℝ :=
  if sample ∈ A then (ball (0 : TFSpace) r).indicator (μ sample) x else 0

def initialError (A : Set Ω) (r : ℝ) (μ : Ω → TFSpace → ℝ) : Ω → TFSpace → ℝ :=
  initialCharge Aᶜ r μ

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric Laplacian InnerProductSpace
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

def addedError (good : Prop) [Decidable good] (R : ℝ) (μ p : TFSpace → ℝ) (x : TFSpace) : ℝ :=
  p x+if good then 0 else if R/2 ≤ ‖x‖ ∧ ‖x‖ < R then μ x else 0

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialLipschitzBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric ProbabilityTheory
open scoped Topology

open CoulombAtom CoulombAnalysis

def DeterministicLocalLipschitz {Ω : Type*} (u : Ω → TFSpace → ℝ) : Prop :=
  ∀ x, ∃ K : NNReal, ∃ t ∈ 𝓝 x, ∀ sample, LipschitzOnWith K (u sample) t

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierStepGeometryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

def shiftedCandidates (good : Prop) [Decidable good] (a h : TFSpace → ℝ)
    (R lam1 lam2 : ℝ) (x : TFSpace) : ℝ :=
  if good then max (a x-lam1/R^4) (h x-lam2/R^4) else a x-lam1/R^4

def outwardOffset (good : Prop) [Decidable good] (a h : TFSpace → ℝ)
    (Z B R M lam1 lam2 : ℝ) : TFSpace → ℝ :=
  cutMaximum ((26/25)*R) (2*M*R) (shiftedCandidates good a h R lam1 lam2)
    (outerOffset Z B R)

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierRetainedFiniteBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

def outwardRegionOffset (good radial : Prop) [Decidable good] [Decidable radial]
    (a h : TFSpace → ℝ) (Z B R lam1 lam2 : ℝ) (x : TFSpace) : ℝ :=
  max (max (a x-lam1/R^4) (if good then h x-lam2/R^4 else a x-lam1/R^4))
    (if radial then outerOffset Z B R x else a x-lam1/R^4)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierInitialInvariantBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierInitialInvariant_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

structure IsNuclearBarrier {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → TFSpace → ℝ) (Z k B C r T η : ℝ)
    (a p : Ω → TFSpace → ℝ) : Prop where
  measurable_offset : Measurable (Function.uncurry a)
  uniform_lipschitz_offset : DeterministicLocalLipschitz a
  bound_offset : DeterministicLocalBound a
  measurable_error : Measurable (Function.uncurry p)
  nonneg_error : ∀ sample x, 0 ≤ p sample x
  bounded_error : ∃ L : ℝ, ∀ sample x, p sample x ≤ L
  support_error : ∀ sample x, r < ‖x‖ → p sample x = 0
  weak : ∀ᵐ sample ∂P, WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a sample x)
    (fun x => innerSource r (μ sample) (p sample) x+
      outerCoefficient r x*reaction k (nuclearField Z x+a sample x))
  lower : ∀ sample x, r ≤ ‖x‖ → outerBarrier B r x ≤ nuclearField Z x+a sample x
  upper : ∀ sample x, r ≤ ‖x‖ → nuclearField Z x+a sample x ≤ C/‖x‖^4
  tail : ∀ sample x, T*r < ‖x‖ → nuclearField Z x+a sample x = outerBarrier B r x
  mass : (∫ sample, (∫ x, p sample x) ∂P) ≤ η

end Work_BarrierInitialInvariant_barrier_scope

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOriginalForgettingBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis

def barrierErrorExponent : ℝ := 19/2-3*masterExponent

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RotationShellBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology

namespace CoulombAtom

instance rotationMeasureHaar : Measure.IsHaarMeasure rotationMeasure :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts SpatialRotation)).IsHaarMeasure

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellResidualControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply fermionGraphValue

def shellGraphConstant (N : ℕ) (r : ℝ) : ℝ :=
  4*(3*(N:ℝ)^2+6*(N:ℝ)*(2*(Real.pi*smoothTransitionBound)/r)^2)

end
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExteriorScreenNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

def exteriorGradientConstant : ℝ := 24*(Real.pi*smoothTransitionBound)^2

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology

end

end OAI
end


