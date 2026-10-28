-- Prove2me | Definitions.Def_OAIQ062C003
-- name    : OAIQ062C003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T23:57:52.800869+00:00
-- url     : https://prove2.me/theorems/84e9ab79-c96b-442c-843e-2dd58f893213
-- title:
--   Definitions bundle OAIQ062C003 of the split of OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NeutralAtom.generalized_outer_radii`, carved from OpenAI's openai/math development (OpenAI, *Generalized outer-electron radii of neutral Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 240 declarations of OpenAI's Lean: 33 definitions and 207 theorems. The definitions and types are `OAI.Coulomb.H1Vector.finiteSum`, `OAI.Coulomb.H1Vector.fullAntisymmetrize`, `OAI.Coulomb.H1Vector.ofSmoothCompact`, `OAI.Coulomb.H1Vector.tensor`, `OAI.Coulomb.H1Vector.wedge`, `OAI.Coulomb.blockRegion`, `OAI.Coulomb.configurationHomeomorph`, `OAI.Coulomb.coreInteractionDensity`, `OAI.Coulomb.crossEnergy`, `OAI.Coulomb.crossPotential`, `OAI.Coulomb.cubeGradient`, `OAI.Coulomb.cubeState`, `OAI.Coulomb.finiteFermiDensity`, `OAI.Coulomb.flatSpinOrbital`, `OAI.Coulomb.frameImageDensity`, `OAI.Coulomb.joinSpins`, `OAI.Coulomb.leftPotential`, `OAI.Coulomb.nearCoulombFiveHalves`, `OAI.Coulomb.packetBasis`, `OAI.Coulomb.packetFrame`, `OAI.Coulomb.packetIndex`, `OAI.Coulomb.positivePacketIndex`, `OAI.Coulomb.rightPotential`, `OAI.Coulomb.selectedSlater`, `OAI.Coulomb.slaterConfiguration`, `OAI.Coulomb.slaterDensity`, `OAI.Coulomb.slaterState`, `OAI.Coulomb.spaceFourierL2`, `OAI.Coulomb.spinCubeEquiv`, `OAI.Coulomb.spinOrbital`, `OAI.Coulomb.tensorGradient`, `OAI.Coulomb.tensorOrbital`, `OAI.Coulomb.tensorValue`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `CoulombRadii_FieldAnalysis_BlockIndex`, `CoulombRadii_FieldAnalysis_CoreCoulombPotential`, `CoulombRadii_FieldAnalysis_DeterminantBodyReal`, `CoulombRadii_FieldAnalysis_DeterminantWave`, `CoulombRadii_FieldAnalysis_FermionicCoefficients`, `CoulombRadii_FieldAnalysis_FiniteProdSum`, `CoulombRadii_FieldAnalysis_FrameDensity`, `CoulombRadii_FieldAnalysis_FrameImageDensity`, `CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto`, `CoulombRadii_FieldAnalysis_IntegrableTsumSummableNormIntegral`, `CoulombRadii_FieldAnalysis_JoinSpins`, `CoulombRadii_FieldAnalysis_LeftPotential`, `CoulombRadii_FieldAnalysis_ModulatedRealDerivativeNorm`, `CoulombRadii_FieldAnalysis_NearCoulombFiveHalves`, `CoulombRadii_FieldAnalysis_NormSqSumCosets`, `CoulombRadii_FieldAnalysis_Occupancy`, `CoulombRadii_FieldAnalysis_PermOrCompSwapOffTwo`, `CoulombRadii_FieldAnalysis_PermuteJoinBlock`, `CoulombRadii_FieldAnalysis_PhaseRegion`, `CoulombRadii_FieldAnalysis_SlotTensor`, `CoulombRadii_FieldAnalysis_SpinConfigurationIntegral`, `CoulombRadii_FieldAnalysis_SpinCubeEquiv`, `CoulombRadii_FieldAnalysis_SumSpinDuplicate`, `CoulombRadii_FieldAnalysis_SumSwapNonnegative`, `CoulombRadii_FieldAnalysis_TwoBodyTensorIntegrable`, `CoulombRadii_FieldAnalysis_UnitNucleus`, `CoulombRadii_FieldAnalysis_WedgeMultiplicity`, `CoulombRadii_FieldAnalysis_WeightedExchangeAlgebra`, `CoulombRadii_FormDomain_CubeGradient`, `CoulombRadii_FormDomain_HilbertBasisSumSqInner`, `CoulombRadii_FormDomain_L2MeasureInclusion`, `CoulombRadii_FormDomain_L2WeightedDensitySetIntegral`, `CoulombRadii_FormDomain_OrbitalHilbertBasis`, `CoulombRadii_FormDomain_PacketStateL2Norm`, `CoulombRadii_FormDomain_Pullback`, `CoulombRadii_FormDomain_SchwartzFourierDerivativeNorm`, `CoulombRadii_FormDomain_SmoothCompact`, `CoulombRadii_FormDomain_SpaceFourierL2`, `CoulombRadii_FormDomain_ThomasFermiKineticConstant`, `CoulombRadii_Localization_ConfigSupported`, `CoulombRadii_Localization_TruncatedCoulomb`, `CoulombRadii_Packets_ComplexWindow`, `CoulombRadii_Packets_CoreScreenedFieldPacketIntegral`, `CoulombRadii_Packets_PacketDensity`, `CoulombRadii_Packets_PacketIndex`, `CoulombRadii_Packets_PacketStateJointSquareIntegrable`, `CoulombRadii_Packets_PacketSynthesisIndicator`, `CoulombRadii_Packets_PacketWindowed`, `CoulombRadii_Packets_WindowCoulomb`, `CoulombRadii_Propagation_NuclearPotential`, `CoulombRadii_Screening_CoreScreenedField`, `CoulombRadii_SpectralTheory_FermiPacketSpectralTrace`, `CoulombRadii_ThomasFermi_PacketFrame`.
--
--   **Imports.** It imports the bundles `OAIQ062C000` and `OAIQ062C001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ062C006` and `OAIQ062C007`.
-- source:
--   OpenAI, Generalized outer-electron radii of neutral Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-outer-electron-radii-of-neutral-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ062C000
import Definitions.Def_OAIQ062C001

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

noncomputable def tensorOrbital {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ) (b : Fin n → α) (s : Spins n) (x : Configuration n) : ℂ :=
  ∏ i, v (b i) (position x i) (s i)

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_ConfigSupported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
lemma H1Vector.gradient_congr_ae {n : ℕ} (u v : H1Vector n)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) (s : Spins n) (a : Fin n × Fin 3) :
    u.gradient s a =ᵐ[volume] v.gradient s a := by
  apply weak_directional_unique (f := u.value s) (EuclideanSpace.single a 1)
    ((u.partial_L2 s a).locallyIntegrable (by norm_num))
    ((v.partial_L2 s a).locallyIntegrable (by norm_num))
  · intro φ hφ hc
    simpa only [mul_comm] using u.weak_partial s a φ hφ hc
  · intro φ hφ hc
    rw [show (∫ x, (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)*u.value s x) =
      (∫ x, (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)*v.value s x) from
      integral_congr_ae ((he s).mono (fun x hx => by dsimp only; rw [hx]))]
    simpa only [mul_comm] using v.weak_partial s a φ hφ hc

lemma ConfigSupported.gradient {n : ℕ} {u : H1Vector n} {A : Set (Configuration n)}
    (hu : ConfigSupported u A) (hA : IsClosed A) (s : Spins n) (a : Fin n × Fin 3) :
    ∀ᵐ x ∂volume, x ∉ A → u.gradient s a x = 0 := by
  apply weak_directional_zero_on_open (EuclideanSpace.single a 1)
    ((u.partial_L2 s a).locallyIntegrable (by norm_num))
    (fun φ hφ hc => by simpa only [mul_comm] using u.weak_partial s a φ hφ hc)
    Aᶜ hA.isOpen_compl (hu s)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace F] [BorelSpace F]
  [IsLocallyFiniteMeasure (volume : Measure F)] [SigmaFinite (volume : Measure F)]

lemma tensor_weak_right {u : E → ℂ} {v d : F → ℂ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) (hd : MemLp d 2 volume)
    (a : F)
    (hvd : ∀ φ : F → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, (fderiv ℝ φ y a : ℂ)*v y) = -(∫ y, (φ y : ℂ)*d y))
    (φ : E × F → ℝ) (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    (∫ z, (fderiv ℝ φ z (0,a) : ℂ)*(u z.1*v z.2) ∂(volume.prod volume)) =
      -(∫ z, (φ z : ℂ)*(u z.1*d z.2) ∂(volume.prod volume)) := by
  have hT : MemLp (fun z => (φ z : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hC.comp_left Complex.ofReal_zero)
  have hD : MemLp (fun z => (fderiv ℝ φ z (0,a) : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hC.fderiv_apply ℝ (0,a)).comp_left Complex.ofReal_zero)
  rw [integral_prod (fun z => (fderiv ℝ φ z (0,a) : ℂ)*(u z.1*v z.2))
      (hD.integrable_mul (tensorPair_memLp hu hv)),
    integral_prod (fun z => (φ z : ℂ)*(u z.1*d z.2))
      (hT.integrable_mul (tensorPair_memLp hu hd)), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  have hφx : ContDiff ℝ ∞ (fun y => φ (x,y)) := hφ.comp (contDiff_const.prodMk contDiff_id)
  have hdφ (y : F) : fderiv ℝ (fun y => φ (x,y)) y a = fderiv ℝ φ (x,y) (0,a) := by
    change fderiv ℝ (φ ∘ Prod.mk x) y a = _
    rw [(hφ.differentiable (by simp) (x,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)) |>.fderiv]
    simp
  have H := hvd (fun y => φ (x,y)) hφx (compactSupport_slice_right hC x)
  simp_rw [hdφ] at H
  simp_rw [mul_left_comm _ (u x), integral_const_mul]
  rw [H]
  ring

lemma tensor_weak_left {u d : E → ℂ} {v : F → ℂ}
    (hu : MemLp u 2 volume) (hd : MemLp d 2 volume) (hv : MemLp v 2 volume)
    (a : E)
    (hud : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, (fderiv ℝ φ x a : ℂ)*u x) = -(∫ x, (φ x : ℂ)*d x))
    (φ : E × F → ℝ) (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    (∫ z, (fderiv ℝ φ z (a,0) : ℂ)*(u z.1*v z.2) ∂(volume.prod volume)) =
      -(∫ z, (φ z : ℂ)*(d z.1*v z.2) ∂(volume.prod volume)) := by
  have hT : MemLp (fun z => (φ z : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hC.comp_left Complex.ofReal_zero)
  have hD : MemLp (fun z => (fderiv ℝ φ z (a,0) : ℂ)) 2 (volume.prod volume) :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hC.fderiv_apply ℝ (a,0)).comp_left Complex.ofReal_zero)
  rw [integral_prod_symm (fun z => (fderiv ℝ φ z (a,0) : ℂ)*(u z.1*v z.2))
      (hD.integrable_mul (tensorPair_memLp hu hv)),
    integral_prod_symm (fun z => (φ z : ℂ)*(d z.1*v z.2))
      (hT.integrable_mul (tensorPair_memLp hd hv)), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  have hφy : ContDiff ℝ ∞ (fun x => φ (x,y)) := hφ.comp (contDiff_id.prodMk contDiff_const)
  have hdφ (x : E) : fderiv ℝ (fun x => φ (x,y)) x a = fderiv ℝ φ (x,y) (a,0) := by
    exact congrArg (fun A : E →L[ℝ] ℝ => A a)
      (((hφ.differentiable (by simp) (x,y)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).prodMk (hasFDerivAt_const y x))).fderiv)
  have H := hud (fun x => φ (x,y)) hφy (compactSupport_slice_left hC y)
  simp_rw [hdφ] at H
  simp_rw [← mul_assoc, integral_mul_const]
  rw [H]
  ring
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BlockIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb

lemma joinConfiguration_left_single (m k : ℕ) (a : Fin m × Fin 3) :
    joinConfiguration m k (EuclideanSpace.single a 1, 0) =
      EuclideanSpace.single (Fin.castAdd k a.1, a.2) 1 := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [joinConfiguration_left]
    simp [PiLp.single_apply, Prod.ext_iff]
  · intro j
    rw [joinConfiguration_right]
    simp only [PiLp.single_apply, PiLp.zero_apply, Prod.mk.injEq]
    split_ifs with h
    · have := congrArg (fun z : Fin (m+k) => z.val) h.1
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl

lemma joinConfiguration_symm_measurePreserving (m k : ℕ) :
    MeasurePreserving (joinConfiguration m k).symm.toHomeomorph.toMeasurableEquiv
      volume (volume.prod volume) :=
  MeasurePreserving.symm _ (joinConfiguration_measurePreserving m k)

def tensorValue {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (x : Configuration (m+k)) : ℂ :=
  u.value (s ∘ Fin.castAdd k) ((joinConfiguration m k).symm x).1 *
    v.value (s ∘ Fin.natAdd m) ((joinConfiguration m k).symm x).2

def tensorGradient {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3) (x : Configuration (m+k)) : ℂ :=
  Fin.addCases
    (fun i => u.gradient (s ∘ Fin.castAdd k) (i,a.2) ((joinConfiguration m k).symm x).1 *
      v.value (s ∘ Fin.natAdd m) ((joinConfiguration m k).symm x).2)
    (fun i => u.value (s ∘ Fin.castAdd k) ((joinConfiguration m k).symm x).1 *
      v.gradient (s ∘ Fin.natAdd m) (i,a.2) ((joinConfiguration m k).symm x).2) a.1

lemma tensorValue_memLp {m k : ℕ} (u : H1Vector m) (v : H1Vector k) (s : Spins (m+k)) :
    MemLp (tensorValue u v s) 2 volume :=
  (tensorPair_memLp (u.value_L2 _) (v.value_L2 _)).comp_measurePreserving
    (joinConfiguration_symm_measurePreserving m k)

lemma tensorGradient_memLp {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3) :
    MemLp (tensorGradient u v s a) 2 volume := by
  rcases a with ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    unfold tensorGradient
    simp only [Fin.addCases_left]
    exact
      (tensorPair_memLp (u.partial_L2 (s ∘ Fin.castAdd k) (j,b)) (v.value_L2 (s ∘ Fin.natAdd m))).comp_measurePreserving
        (joinConfiguration_symm_measurePreserving m k)
  · intro j
    unfold tensorGradient
    simp only [Fin.addCases_right]
    exact
      (tensorPair_memLp (u.value_L2 (s ∘ Fin.castAdd k)) (v.partial_L2 (s ∘ Fin.natAdd m) (j,b))).comp_measurePreserving
        (joinConfiguration_symm_measurePreserving m k)

lemma tensorValue_join {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (z : Configuration m × Configuration k) :
    tensorValue u v s (joinConfiguration m k z) =
      u.value (s ∘ Fin.castAdd k) z.1*v.value (s ∘ Fin.natAdd m) z.2 := by
  simp only [tensorValue, ContinuousLinearEquiv.symm_apply_apply]

lemma tensorGradient_join_left {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin m × Fin 3) (z : Configuration m × Configuration k) :
    tensorGradient u v s (Fin.castAdd k a.1,a.2) (joinConfiguration m k z) =
      u.gradient (s ∘ Fin.castAdd k) a z.1*v.value (s ∘ Fin.natAdd m) z.2 := by
  simp only [tensorGradient, Fin.addCases_left, ContinuousLinearEquiv.symm_apply_apply]

lemma tensorGradient_join_right {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin k × Fin 3) (z : Configuration m × Configuration k) :
    tensorGradient u v s (Fin.natAdd m a.1,a.2) (joinConfiguration m k z) =
      u.value (s ∘ Fin.castAdd k) z.1*v.gradient (s ∘ Fin.natAdd m) a z.2 := by
  simp only [tensorGradient, Fin.addCases_right, ContinuousLinearEquiv.symm_apply_apply]

lemma tensor_weak_partial {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3)
    (φ : Configuration (m+k) → ℝ) (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    (∫ x, tensorValue u v s x*(fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
      -(∫ x, tensorGradient u v s a x*(φ x : ℂ)) := by
  let : ContinuousSMul ℝ (Configuration m × Configuration k) := Prod.continuousSMul
  let J := joinConfiguration m k
  have hJ := joinConfiguration_measurePreserving m k
  have htest : ContDiff ℝ ∞ (φ ∘ J) := hφ.comp J.contDiff
  have htestC : HasCompactSupport (φ ∘ J) := hC.comp_homeomorph J.toHomeomorph
  have hdtest (z : Configuration m × Configuration k) (b : Configuration m × Configuration k) :
      fderiv ℝ (φ ∘ J) z b = fderiv ℝ φ (J z) (J b) := by
    rw [((hφ.differentiable (by simp) (J z)).hasFDerivAt.comp z J.hasFDerivAt).fderiv]
    rfl
  rw [← hJ.integral_comp' (fun x => tensorValue u v s x*
      (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)),
    ← hJ.integral_comp' (fun x => tensorGradient u v s a x*(φ x : ℂ))]
  change (∫ z : Configuration m × Configuration k,
    tensorValue u v s (joinConfiguration m k z)*
      (fderiv ℝ φ (joinConfiguration m k z) (EuclideanSpace.single a 1) : ℂ)
        ∂(volume.prod volume)) =
    -(∫ z : Configuration m × Configuration k,
      tensorGradient u v s a (joinConfiguration m k z)*
        (φ (joinConfiguration m k z) : ℂ) ∂(volume.prod volume))
  rcases a with ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    have H := tensor_weak_left (u.value_L2 (s ∘ Fin.castAdd k))
      (u.partial_L2 (s ∘ Fin.castAdd k) (j,b)) (v.value_L2 (s ∘ Fin.natAdd m))
      (EuclideanSpace.single (j,b) 1)
      (fun t ht htC => by simpa only [mul_comm] using u.weak_partial _ (j,b) t ht htC)
      (φ ∘ J) htest htestC
    simp_rw [hdtest] at H
    simp only [J, joinConfiguration_left_single, Function.comp_apply] at H
    simp only [tensorValue_join, tensorGradient_join_left u v s (j,b)]
    simpa only [mul_comm] using H
  · intro j
    have H := tensor_weak_right (u.value_L2 (s ∘ Fin.castAdd k))
      (v.value_L2 (s ∘ Fin.natAdd m)) (v.partial_L2 (s ∘ Fin.natAdd m) (j,b))
      (EuclideanSpace.single (j,b) 1)
      (fun t ht htC => by simpa only [mul_comm] using v.weak_partial _ (j,b) t ht htC)
      (φ ∘ J) htest htestC
    simp_rw [hdtest] at H
    simp only [J, joinConfiguration_right_single, Function.comp_apply] at H
    simp only [tensorValue_join, tensorGradient_join_right u v s (j,b)]
    simpa only [mul_comm] using H

def H1Vector.tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) : H1Vector (m+k) where
  value := tensorValue u v
  gradient := tensorGradient u v
  value_L2 := tensorValue_memLp u v
  partial_L2 := tensorGradient_memLp u v
  weak_partial := tensor_weak_partial u v
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_OrbitalHilbertBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open scoped Classical
open scoped Classical

noncomputable def spinOrbital {ι : Type*} (v : ι → Space → ℂ)
    (is : ι × Fin 2) (x : Space) (s : Fin 2) : ℂ := if s = is.2 then v is.1 x else 0

section GeneralFermionSpace
variable {A ι : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma scalarTensor_orthonormal {n : ℕ} (v : ι → A → ℂ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0) :
    ∀ b c : Fin n → ι, (∫ x, star (∏ i, v (b i) (x i)) * (∏ i, v (c i) (x i))
      ∂(Measure.pi fun _ => μ)) = if b = c then (1 : ℂ) else 0 := by
  intro b c
  rw [scalarTensor_inner_integral]
  simp_rw [ho]
  by_cases h : b = c
  · subst c; simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by
      by_contra hh
      apply h
      funext i
      exact not_not.mp (not_exists.mp hh i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

end GeneralFermionSpace

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_DeterminantWave
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma permutation_minor_orthogonality {α : Type*} [Fintype α] [DecidableEq α]
    (p q : Equiv.Perm α) (i : α) :
    (∏ j ∈ Finset.univ.erase i, if p j = q j then (1 : ℂ) else 0) =
      if p = q then 1 else 0 := by
  classical
  by_cases h : p = q
  · subst q; simp
  · rw [ite_eq_right h]
    obtain ⟨j,hji,hj⟩ : ∃ j, j ≠ i ∧ p j ≠ q j := by
      by_contra he
      apply h
      apply perm_eq_of_eq_off p q i
      intro j hji
      by_contra hj
      exact he ⟨j,hji,hj⟩
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩) (ite_eq_right hj)

lemma slater_one_body_trace_algebra {n : ℕ} (K : Fin n → Fin n → ℂ) :
    (∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
      star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, K (p i) (q i) *
          ∏ j ∈ Finset.univ.erase i, if p j = q j then (1 : ℂ) else 0) =
      (n.factorial : ℂ) * ∑ i, K i i := by
  classical
  simp_rw [permutation_minor_orthogonality]
  have hp (p : Equiv.Perm (Fin n)) :
      (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, K (p i) (q i) * (if p = q then 1 else 0)) = ∑ i, K i i := by
    rw [Finset.sum_eq_single p]
    · simp only [sign_star_mul, one_mul]
      simpa only [ite_true, mul_one] using Equiv.sum_comp p (fun i => K i i)
    · intro q _ hq
      simp only [ite_eq_right hq.symm, mul_zero, Finset.sum_const_zero]
    · simp
  simp_rw [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

lemma tensor_weight_factor {A : Type*} {n : ℕ} (f : Fin n → A → ℂ)
    (w : A → ℂ) (i : Fin n) (x : Fin n → A) :
    w (x i) * ∏ j, f j (x j) =
      ∏ j, (if j = i then w (x j) * f j (x j) else f j (x j)) := by
  calc
    w (x i) * ∏ j, f j (x j) =
        (w (x i) * f i (x i)) * ∏ j ∈ Finset.univ.erase i, f j (x j) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)]
      ring
    _ = (if i = i then w (x i) * f i (x i) else f i (x i)) *
        ∏ j ∈ Finset.univ.erase i, if j = i then w (x j) * f j (x j) else f j (x j) := by
      simp only [ite_true]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      exact (ite_eq_right (Finset.mem_erase.mp hj).1).symm
    _ = _ := Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then w (x j) * f j (x j) else f j (x j)) (Finset.mem_univ i)

lemma weighted_tensor_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (f : Fin n → A → ℂ) (w : A → ℂ) (i : Fin n)
    (hf : ∀ j, Integrable (f j) μ) (hwi : Integrable (fun a => w a * f i a) μ) :
    Integrable (fun x : Fin n → A => w (x i) * ∏ j, f j (x j))
      (Measure.pi fun _ => μ) := by
  simp_rw [tensor_weight_factor]
  apply Integrable.fintype_prod (f := fun j a => if j = i then w a * f j a else f j a)
  intro j
  by_cases h : j = i
  · subst j; simpa only [ite_true] using hwi
  · simpa only [ite_eq_right h] using hf j

lemma weighted_tensor_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (f : Fin n → A → ℂ) (w : A → ℂ) (i : Fin n) :
    (∫ x : Fin n → A, w (x i) * ∏ j, f j (x j) ∂(Measure.pi fun _ => μ)) =
      (∫ a, w a * f i a ∂μ) * ∏ j ∈ Finset.univ.erase i, ∫ a, f j a ∂μ := by
  simp_rw [tensor_weight_factor]
  rw [integral_fintype_prod_eq_prod (f := fun j a => if j = i then w a * f j a else f j a) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1]

lemma one_body_tensor_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℂ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (∫ x : Fin n → A, w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j))
      ∂(Measure.pi fun _ => μ)) =
      (∫ a, w a * (star (v (p i) a) * v (q i) a) ∂μ) *
        ∏ j ∈ Finset.univ.erase i, if p j = q j then (1 : ℂ) else 0 := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  rw [weighted_tensor_integral (fun j a => star (v (p j) a) * v (q j) a) w i]
  simp_rw [ho]

lemma one_body_tensor_integrable {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (hw : ∀ i j, Integrable (fun a => w a * (star (v i a) * v j a)) μ)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    Integrable (fun x : Fin n → A =>
      w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j)))
      (Measure.pi fun _ => μ) := by
  simp only [star_prod, ← Finset.prod_mul_distrib]
  exact weighted_tensor_integrable (μ := μ) (fun j a => star (v (p j) a) * v (q j) a) w i
    (fun j => (hv (p j)).star.integrable_mul (hv (q j))) (hw _ _)

lemma determinant_one_body_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ i j, (∫ a, star (v i a) * v j a ∂μ) = if i = j then (1 : ℂ) else 0)
    (hw : ∀ i j, Integrable (fun a => w a * (star (v i a) * v j a)) μ) :
    (∫ x : Fin n → A, (∑ i, w (x i)) *
      (star (determinantWave v x) * determinantWave v x) ∂(Measure.pi fun _ => μ)) =
      (n.factorial : ℂ) * ∑ i, ∫ a, w a * (star (v i a) * v i a) ∂μ := by
  let F (p q : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) : ℂ :=
    w (x i) * (star (∏ j, v (p j) (x j)) * ∏ j, v (q j) (x j))
  let c (p q : Equiv.Perm (Fin n)) : ℂ :=
    star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ))
  have hi (p q : Equiv.Perm (Fin n)) : Integrable (fun x => ∑ i, F p q i x)
      (Measure.pi fun _ => μ) :=
    integrable_finsetSum Finset.univ (fun i _ => one_body_tensor_integrable v w hv hw p q i)
  have hj (p : Equiv.Perm (Fin n)) : Integrable (fun x => ∑ q, c p q * ∑ i, F p q i x)
      (Measure.pi fun _ => μ) :=
    integrable_finsetSum Finset.univ (fun q _ => (hi p q).const_mul (c p q))
  calc
    _ = ∫ x : Fin n → A, ∑ p, ∑ q, c p q * ∑ i, F p q i x
        ∂(Measure.pi fun _ => μ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact determinant_one_body_expansion v w x
    _ = ∑ p, ∑ q, c p q * ∑ i, ∫ x : Fin n → A, F p q i x
        ∂(Measure.pi fun _ => μ) := by
      rw [integral_finsetSum _ (fun p _ => hj p)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_finsetSum _ (fun q _ => (hi p q).const_mul (c p q))]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_const_mul, integral_finsetSum _
        (fun i _ => one_body_tensor_integrable v w hv hw p q i)]
    _ = _ := by
      simp only [F, one_body_tensor_integral v w ho]
      exact slater_one_body_trace_algebra (fun i j => ∫ a, w a * (star (v i a) * v j a) ∂μ)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinCubeEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace Coulomb

noncomputable def spinCubeEquiv (n : ℕ) :
    (Fin n → (Fin 2 × (Fin 3 → ℝ))) ≃ᵐ (Spins n × ((Fin n × Fin 3) → ℝ)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)).trans
    ((MeasurableEquiv.refl (Spins n)).prodCongr (MeasurableEquiv.curry (Fin n) (Fin 3) ℝ).symm)

noncomputable def cubeState {n : ℕ} (ψ : H1Vector n)
    (z : Fin n → (Fin 2 × (Fin 3 → ℝ))) : ℂ :=
  ψ.value (fun i => (z i).1) (WithLp.toLp 2 (fun ij => (z ij.1).2 ij.2))

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_IntegrableIntegralAeTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma spinCubeEquiv_full_measurePreserving (n : ℕ) :
    MeasurePreserving (spinCubeEquiv n) (Measure.pi fun _ : Fin n => spinSpaceMeasure)
      (Measure.count.prod volume) := by
  have h1 := measurePreserving_arrowProdEquivProdArrow (Fin 2) (Fin 3 → ℝ) (Fin n)
    (fun _ => Measure.count) (fun _ => volume)
  rw [measure_pi_count] at h1
  have h2 := (MeasurePreserving.id (Measure.count : Measure (Spins n))).prod
    (measurePreserving_const_uncurry (I := Fin n) (J := Fin 3) (volume : Measure ℝ))
  exact h2.comp h1

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SmoothCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma complex_smooth_compact_ibp {n : ℕ} (f : Configuration n → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hC : HasCompactSupport f)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφC : HasCompactSupport φ) (v : Configuration n) :
    (∫ x, f x * (fderiv ℝ φ x v : ℂ)) =
      -(∫ x, fderiv ℝ f x v * (φ x : ℂ)) := by
  let g : Configuration n → ℂ := fun x => (φ x : ℂ)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := Complex.ofRealCLM.contDiff.comp hφ
  have hgC : HasCompactSupport g := hφC.comp_left Complex.ofReal_zero
  have hd (x : Configuration n) : fderiv ℝ g x v = (fderiv ℝ φ x v : ℂ) := by
    exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L v)
      ((Complex.ofRealCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hf' : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi1 : Integrable (fun x => fderiv ℝ f x v * g x) volume := (hf'.mul hg.continuous).integrable_of_hasCompactSupport
    (hgC.mul_left (f := fun x => fderiv ℝ f x v))
  have hi2 : Integrable (fun x => f x * fderiv ℝ g x v) volume := (hf.continuous.mul hg').integrable_of_hasCompactSupport
    (hC.mul_right (f' := fun x => fderiv ℝ g x v))
  have hi3 : Integrable (fun x => f x * g x) volume := (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
    (hC.mul_right (f' := g))
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => (hg.differentiable (by simp)) x)
  simpa only [hd] using h

noncomputable def H1Vector.ofSmoothCompact {n : ℕ} (f : Spins n → Configuration n → ℂ)
    (hf : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (f s))
    (hC : ∀ s, HasCompactSupport (f s)) : H1Vector n where
  value := f
  gradient s a x := fderiv ℝ (f s) x (EuclideanSpace.single a 1)
  value_L2 s := (hf s).continuous.memLp_of_hasCompactSupport (hC s)
  partial_L2 s a :=
    (((hf s).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hC s).fderiv_apply ℝ (EuclideanSpace.single a 1))
  weak_partial s a φ hφ hφC := complex_smooth_compact_ibp (f s) (hf s) (hC s) φ hφ hφC _

noncomputable def configurationHomeomorph (n : ℕ) : Configuration n ≃ₜ (Fin n → Space) :=
  ((PiLp.homeomorph 2 (fun _ : Fin n × Fin 3 => ℝ)).trans
    (Homeomorph.piCurry (X := Fin n) (Y := Fin 3) (Z := ℝ))).trans
    (Homeomorph.piCongrRight fun _ => (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm)

lemma tensorOrbital_compact_support {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (b : Fin n → α) (s : Spins n) : HasCompactSupport (tensorOrbital v b s) := by
  exact (tensor_compact_support (fun i x => v (b i) x (s i)) (fun i => hC (b i) (s i))).comp_homeomorph
    (configurationHomeomorph n)

lemma tensorOrbital_contDiff {n : ℕ} {α : Type*}
    (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (b : Fin n → α) (s : Spins n) : ContDiff ℝ (⊤ : ℕ∞) (tensorOrbital v b s) := by
  unfold tensorOrbital
  apply contDiff_prod
  intro i _
  exact (hv (b i) (s i)).comp (positionCLM i).contDiff

noncomputable def slaterConfiguration {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (s : Spins n) (x : Configuration n) : ℂ :=
  slaterWave (fun i (a : Fin 2 × Space) => v i a.2 a.1) (fun i => (s i, position x i))

lemma slaterConfiguration_expansion {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (s : Spins n) : slaterConfiguration v s =
      fun x => (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        ∑ p : Equiv.Perm (Fin n), (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x := by
  funext x
  simp only [slaterConfiguration, slaterWave, determinantWave_expansion, tensorOrbital]

lemma slaterConfiguration_contDiff {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s)) (s : Spins n) :
    ContDiff ℝ (⊤ : ℕ∞) (slaterConfiguration v s) := by
  rw [slaterConfiguration_expansion]
  apply contDiff_const.mul
  exact ContDiff.sum (fun p _ => contDiff_const.mul (tensorOrbital_contDiff v hv p s))

lemma slaterConfiguration_compact_support {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) (s : Spins n) :
    HasCompactSupport (slaterConfiguration v s) := by
  have ht (p : Equiv.Perm (Fin n)) : HasCompactSupport
      (fun x => (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x) :=
    (tensorOrbital_compact_support v hC p s).mul_left
  have hs : HasCompactSupport (fun x => ∑ p : Equiv.Perm (Fin n),
      (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x) :=
    by
      convert (HasCompactSupport.finset_sum (s := Finset.univ)
        (f := fun (p : Equiv.Perm (Fin n)) x => (((p.sign : ℤ) : ℂ)) * tensorOrbital v p s x) (fun p _ => ht p)) using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | (funext x; simp only [Finset.sum_apply])
  rw [slaterConfiguration_expansion]
  exact hs.mul_left (f := fun _ => (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ))

noncomputable def slaterState {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) : H1Vector n :=
  H1Vector.ofSmoothCompact (slaterConfiguration v)
    (slaterConfiguration_contDiff v hv) (slaterConfiguration_compact_support v hC)

noncomputable def flatSpinOrbital (v : Space → Fin 2 → ℂ) : Fin 2 × (Fin 3 → ℝ) → ℂ :=
  fun sx => v (WithLp.toLp 2 sx.2) sx.1

lemma flatSpinOrbital_memLp (v : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume) :
    MemLp (flatSpinOrbital v) 2 spinSpaceMeasure := by
  change MemLp (flatSpinOrbital v) 2 (Measure.count.prod volume)
  have hi (s : Fin 2) : MemLp (fun t : Fin 2 => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Fin 2) _ => tensorPair_memLp (hi s)
    ((hv s).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext sx
  simp [flatSpinOrbital, ite_mul]

lemma flatSpinOrbital_inner (v u : Space → Fin 2 → ℂ)
    (hv : ∀ s, MemLp (fun x => v x s) 2 volume)
    (hu : ∀ s, MemLp (fun x => u x s) 2 volume) :
    (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂spinSpaceMeasure) =
      ∑ s : Fin 2, ∫ x : Space, star (v x s) * u x s := by
  have hI := (flatSpinOrbital_memLp v hv).star.integrable_mul (flatSpinOrbital_memLp u hu)
  change Integrable (fun a => star (flatSpinOrbital v a) * flatSpinOrbital u a)
    (Measure.count.prod volume) at hI
  change (∫ a, star (flatSpinOrbital v a) * flatSpinOrbital u a ∂(Measure.count.prod volume)) = _
  rw [integral_prod _ hI, integral_count]
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => star (v x s) * u x s)

lemma slaterState_cubeState {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) :
    cubeState (slaterState v hv hC) = slaterWave (fun i => flatSpinOrbital (v i)) := by
  funext x
  rfl

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_TruncatedCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma compact_coulomb_cross_integrable (f g u v : Space → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hu : Continuous u) (hv : Continuous v)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun xy : Space × Space => (coulombKernel (xy.1-xy.2) : ℂ) *
      ((star (f xy.1)*u xy.1)*(star (g xy.2)*v xy.2))) := by
  have hF : Continuous (fun x => ‖f x‖*‖u x‖) := hf.norm.mul hu.norm
  have hG : Continuous (fun x => ‖g x‖*‖v x‖) := hg.norm.mul hv.norm
  have hFC : HasCompactSupport (fun x => ‖f x‖*‖u x‖) := hfc.norm.mul_right
  have hGC : HasCompactSupport (fun x => ‖g x‖*‖v x‖) := hgc.norm.mul_right
  obtain ⟨M,hM⟩ := hGC.exists_bound_of_continuous hG
  have H := coulomb_pair_integrable (hF.integrable_of_hasCompactSupport hFC) hF.measurable
    (hG.integrable_of_hasCompactSupport hGC) hG.measurable hM
  apply H.mono' ?_ (ae_of_all _ (fun xy => ?_))
  · exact (((coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).complex_ofReal).mul
      (((hf.star.mul hu).measurable.comp measurable_fst).mul
      ((hg.star.mul hv).measurable.comp measurable_snd))).aestronglyMeasurable
  · simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (coulombKernel_nonneg _)]
    exact le_of_eq (by ring)

lemma flatSpinOrbital_coulomb_cross_integrable {ι : Type*} [Fintype ι] (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ i s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v i x s))
    (hC : ∀ i s, HasCompactSupport (fun x => v i x s)) (a b c d : ι) :
    Integrable (fun xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)) =>
      (coulombKernel (WithLp.toLp 2 xy.1.2 - WithLp.toLp 2 xy.2.2) : ℂ) *
      ((star (flatSpinOrbital (v a) xy.1)*flatSpinOrbital (v c) xy.1)*
        (star (flatSpinOrbital (v b) xy.2)*flatSpinOrbital (v d) xy.2)))
      (spinSpaceMeasure.prod spinSpaceMeasure) := by
  have hsp (s t : Fin 2) := compact_coulomb_cross_integrable
    (fun x => v a x s) (fun x => v b x t) (fun x => v c x s) (fun x => v d x t)
    (hv a s).continuous (hv b t).continuous (hv c s).continuous (hv d t).continuous
    (hC a s) (hC b t)
  have hm0 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  have hm := hm0.prod hm0
  let F (sz : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) : ℂ :=
    (coulombKernel (WithLp.toLp 2 sz.2.1 - WithLp.toLp 2 sz.2.2) : ℂ) *
      ((star (v a (WithLp.toLp 2 sz.2.1) sz.1.1)*v c (WithLp.toLp 2 sz.2.1) sz.1.1)*
      (star (v b (WithLp.toLp 2 sz.2.2) sz.1.2)*v d (WithLp.toLp 2 sz.2.2) sz.1.2))
  have hF : Integrable F (Measure.count.prod (volume.prod volume)) :=
    integrable_finite_count_prod F (fun st => hm.integrable_comp_of_integrable (hsp st.1 st.2))
  have hR := pairRegroup_measurePreserving (Measure.count : Measure (Fin 2))
    (volume : Measure (Fin 3 → ℝ)) (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [count_prod_count] at hR
  exact hR.integrable_comp_of_integrable hF
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PermOrCompSwapOffTwo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma permutation_second_minor {α : Type*} [Fintype α] [DecidableEq α]
    (p q : Equiv.Perm α) (i j : α) (hij : i ≠ j) :
    (∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1 : ℂ) else 0) =
      (if q = p then 1 else 0) + (if q = p * Equiv.swap i j then 1 else 0) := by
  by_cases h1 : q = p
  · subst q
    simp [Ne.symm (perm_mul_swap_ne p i j hij)]
  by_cases h2 : q = p * Equiv.swap i j
  · rw [ite_eq_right h1, ite_eq_left h2, zero_add]
    apply Finset.prod_eq_one
    intro k hk
    obtain ⟨hkj,hki,_⟩ := Finset.mem_erase.mp hk |>.imp_right Finset.mem_erase.mp
    simp only [h2, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, ite_true]
  · rw [ite_eq_right h1, ite_eq_right h2, zero_add]
    obtain ⟨k,hki,hkj,hk⟩ : ∃ k, k ≠ i ∧ k ≠ j ∧ p k ≠ q k := by
      by_contra he
      have h := perm_eq_or_comp_swap_of_eq_off_two p q i j hij (fun k hki hkj => by
        by_contra hk
        exact he ⟨k,hki,hkj,hk⟩)
      exact h.elim h1 h2
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj,Finset.mem_erase.mpr ⟨hki,Finset.mem_univ _⟩⟩)
      (ite_eq_right hk)

lemma pair_minor_trace {n : ℕ} (K : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p : Equiv.Perm (Fin n)) (i j : Fin n) (hij : i ≠ j) :
    (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        (K (p i) (p j) (q i) (q j) *
          ∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1:ℂ) else 0)) =
      K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i) := by
  simp_rw [permutation_second_minor p _ i j hij, mul_add, Finset.sum_add_distrib]
  have h1 : (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
      (K (p i) (p j) (q i) (q j) * (if q = p then 1 else 0))) = K (p i) (p j) (p i) (p j) := by
    rw [Finset.sum_eq_single p]
    · simp only [ite_true, mul_one, sign_star_mul, one_mul]
    · intro q _ hq
      simp only [ite_eq_right hq, mul_zero]
    · simp
  have h2 : (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
      (K (p i) (p j) (q i) (q j) * (if q = p * Equiv.swap i j then 1 else 0))) =
        -K (p i) (p j) (p j) (p i) := by
    rw [Finset.sum_eq_single (p * Equiv.swap i j)]
    · simp only [ite_true, mul_one, sign_star_mul_swap p i j hij, neg_one_mul,
        Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    · intro q _ hq
      simp only [ite_eq_right hq, mul_zero]
    · simp
  rw [h1,h2,sub_eq_add_neg]

lemma slater_two_body_trace_algebra {n : ℕ} (K : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
      star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          K (p i) (p j) (q i) (q j) *
            ∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1:ℂ) else 0) =
      (n.factorial : ℂ) * ∑ i, ∑ j, (K i j i j - K i j j i) := by
  have hp (p : Equiv.Perm (Fin n)) :
      (∑ q : Equiv.Perm (Fin n), star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          K (p i) (p j) (q i) (q j) *
            ∏ k ∈ (Finset.univ.erase i).erase j, if p k = q k then (1:ℂ) else 0) =
      ∑ i, ∑ j, (K i j i j - K i j j i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
          (K (p i) (p j) (p i) (p j) - K (p i) (p j) (p j) (p i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        exact pair_minor_trace K p i j (Finset.mem_erase.mp hj).1.symm
      _ = _ := pair_trace_reindex K p
  simp_rw [hp]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_TwoBodyTensorIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma determinant_two_body_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → A → ℂ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b c d, Integrable (fun xy : A × A => w xy.1 xy.2 *
      ((star (v a xy.1) * v c xy.1) * (star (v b xy.2) * v d xy.2))) (μ.prod μ)) :
    (∫ x : Fin n → A, (∑ i, ∑ j ∈ Finset.univ.erase i, w (x i) (x j)) *
      (star (determinantWave v x) * determinantWave v x) ∂(Measure.pi fun _ => μ)) =
      (n.factorial : ℂ) * ∑ i, ∑ j,
        ((∫ xy : A × A, w xy.1 xy.2 *
          ((star (v i xy.1) * v i xy.1) * (star (v j xy.2) * v j xy.2)) ∂(μ.prod μ)) -
        (∫ xy : A × A, w xy.1 xy.2 *
          ((star (v i xy.1) * v j xy.1) * (star (v j xy.2) * v i xy.2)) ∂(μ.prod μ))) := by
  let F (p q : Equiv.Perm (Fin n)) (i j : Fin n) (x : Fin n → A) : ℂ :=
    w (x i) (x j) * (star (∏ k, v (p k) (x k)) * ∏ k, v (q k) (x k))
  let c (p q : Equiv.Perm (Fin n)) : ℂ := star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ))
  have hi (p q : Equiv.Perm (Fin n)) : Integrable
      (fun x => ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x) (Measure.pi fun _ => μ) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j hj =>
      two_body_tensor_integrable v w hv hw p q i j (Finset.mem_erase.mp hj).1.symm))
  have hj (p : Equiv.Perm (Fin n)) : Integrable
      (fun x => ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x)
      (Measure.pi fun _ => μ) := integrable_finsetSum _ (fun q _ => (hi p q).const_mul _)
  calc
    _ = ∫ x : Fin n → A, ∑ p, ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i, F p q i j x
        ∂(Measure.pi fun _ => μ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact determinant_two_body_expansion v w x
    _ = ∑ p, ∑ q, c p q * ∑ i, ∑ j ∈ Finset.univ.erase i,
        ∫ x : Fin n → A, F p q i j x ∂(Measure.pi fun _ => μ) := by
      rw [integral_finsetSum _ (fun p _ => hj p)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_finsetSum _ (fun q _ => (hi p q).const_mul _)]
      apply Finset.sum_congr rfl
      intro q _
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _
        (fun j hj => two_body_tensor_integrable v w hv hw p q i j (Finset.mem_erase.mp hj).1.symm))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j hj =>
        two_body_tensor_integrable v w hv hw p q i j (Finset.mem_erase.mp hj).1.symm)
    _ = _ := by
      have H := slater_two_body_trace_algebra (fun a b c d =>
        ∫ xy : A × A, w xy.1 xy.2 * ((star (v a xy.1) * v c xy.1) *
          (star (v b xy.2) * v d xy.2)) ∂(μ.prod μ))
      rw [← H]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j hj
      exact two_body_tensor_integral v w ho p q i j (Finset.mem_erase.mp hj).1.symm

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SpinConfigurationIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma spinConfiguration_integral {n : ℕ} (F : Spins n → Configuration n → ℝ)
    (hF : ∀ s, Integrable (F s)) :
    (∫ z, F ((spinCubeEquiv n) z).1 (WithLp.toLp 2 ((spinCubeEquiv n) z).2)
      ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = ∑ s, ∫ x, F s x := by
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => F sx.1 (WithLp.toLp 2 sx.2))]
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  rw [integral_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hF s))]
  apply Finset.sum_congr rfl
  intro s _
  exact hm.integral_comp' (F s)

lemma cubeState_pair_energy {n : ℕ} (ψ : H1Vector n) :
    (∫ z, (∑ i, ∑ j ∈ Finset.univ.erase i,
      coulombKernel (WithLp.toLp 2 (z i).2-WithLp.toLp 2 (z j).2)) * ‖cubeState ψ z‖^2
      ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) = 2*pairEnergy ψ := by
  have hs (z : Fin n → Fin 2 × (Fin 3 → ℝ)) := sum_pair_symmetric
    (fun i j => coulombKernel (WithLp.toLp 2 (z i).2-WithLp.toLp 2 (z j).2))
    (fun i j => congrArg (fun r : ℝ => r⁻¹) (norm_sub_rev _ _))
  simp_rw [hs, mul_assoc]
  rw [integral_const_mul]
  congr 1
  exact spinConfiguration_integral
    (fun s x => (∑ i : Fin n, ∑ j : Fin n, if i < j then
      coulombKernel (position x i-position x j) else 0)*‖ψ.value s x‖^2)
    ψ.pair_integrable

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma spinPair_integral (F : Fin 2 → Fin 2 → Space × Space → ℝ)
    (hF : ∀ s t, Integrable (F s t)) :
    (∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
      F xy.1.1 xy.2.1 (WithLp.toLp 2 xy.1.2, WithLp.toLp 2 xy.2.2)
      ∂(spinSpaceMeasure.prod spinSpaceMeasure)) = ∑ s, ∑ t, ∫ xy, F s t xy := by
  have hm0 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  have hm : MeasurePreserving ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).prodCongr
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))) volume volume := hm0.prod hm0
  have hR := pairRegroup_measurePreserving (Measure.count : Measure (Fin 2))
    (volume : Measure (Fin 3 → ℝ)) (Measure.count : Measure (Fin 2)) (volume : Measure (Fin 3 → ℝ))
  rw [count_prod_count] at hR
  let G (sz : (Fin 2 × Fin 2) × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) : ℝ :=
    F sz.1.1 sz.1.2 (WithLp.toLp 2 sz.2.1, WithLp.toLp 2 sz.2.2)
  change (∫ p, G (pairRegroup p) ∂((Measure.count.prod volume).prod (Measure.count.prod volume))) = _
  rw [hR.integral_comp' G, integral_finite_count_prod (μ := volume.prod volume) G
    (fun st => hm.integrable_comp_of_integrable (hF st.1 st.2))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  exact hm.integral_comp' (F s t)

lemma compact_coulomb_direct_integrable (f g : Space → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(‖f xy.1‖^2*‖g xy.2‖^2)) := by
  have h := compact_coulomb_cross_integrable f g f g hf hg hf hg hfc hgc
  simp only [complex_star_mul_self, ← Complex.ofReal_mul] at h
  exact h.re

noncomputable def slaterDensity {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ) (x : Space) : ℝ :=
  ∑ a, ∑ s : Fin 2, ‖v a x s‖^2

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SlotTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma slotTensor_factor {A : Type*} {n : ℕ} (v d : Fin n → A → ℂ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n → A) :
    slotTensor v d p i x = d (p i) (x i) * ∏ j ∈ Finset.univ.erase i, v (p j) (x j) := by
  unfold slotTensor
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => if j = i then d (p j) (x j) else v (p j) (x j)) (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

lemma slotTensor_memLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    MemLp (slotTensor v d p i) 2 (Measure.pi fun _ : Fin n => μ) := by
  have H (j : Fin n) : MemLp (fun a => if j = i then d (p j) a else v (p j) a) 2 μ := by
    by_cases h : j = i
    · simpa only [ite_eq_left h] using hd (p j)
    · simpa only [ite_eq_right h] using hv (p j)
  exact scalarTensor_memLp (fun j a => if j = i then d (p j) a else v (p j) a) H id

lemma slotTensor_inner_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (p q : Equiv.Perm (Fin n)) (i : Fin n) :
    (∫ x, star (slotTensor v d p i x) * slotTensor v d q i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      (∫ a, star (d (p i) a) * d (q i) a ∂μ) *
        ∏ j ∈ Finset.univ.erase i, if p j = q j then (1:ℂ) else 0 := by
  simp only [slotTensor, star_prod, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (f := fun j a =>
    star (if j = i then d (p j) a else v (p j) a) *
      (if j = i then d (q j) a else v (q j) a)) (μ := fun _ => μ)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => ∫ a,
    star (if j = i then d (p j) a else v (p j) a) *
      (if j = i then d (q j) a else v (q j) a) ∂μ) (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [ite_eq_right (Finset.mem_erase.mp hj).1, ho]

lemma slotDeterminant_inner_integral {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (i : Fin n) :
    (∫ x, star (slotDeterminant v d i x) * slotDeterminant v d i x
      ∂(Measure.pi fun _ : Fin n => μ)) =
      ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ((∫ a, star (d (p i) a) * d (q i) a ∂μ) *
            ∏ j ∈ Finset.univ.erase i, if p j = q j then (1:ℂ) else 0) := by
  have hi (p q : Equiv.Perm (Fin n)) : Integrable
      (fun x : Fin n → A => star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
        (star (slotTensor v d p i x) * slotTensor v d q i x)) (Measure.pi fun _ => μ) :=
    ((slotTensor_memLp v d hv hd p i).star.integrable_mul
      (slotTensor_memLp v d hv hd q i)).const_mul _
  simp_rw [slotDeterminant_bilinear]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hi p q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_const_mul, slotTensor_inner_integral v d ho]

lemma slotDeterminant_total_norm_sq {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v d : Fin n → A → ℂ)
    (hv : ∀ a, MemLp (v a) 2 μ) (hd : ∀ a, MemLp (d a) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x) * v b x ∂μ) = if a = b then (1:ℂ) else 0) :
    (∑ i, ∫ x, ‖slotDeterminant v d i x‖^2 ∂(Measure.pi fun _ : Fin n => μ)) =
      (n.factorial : ℝ) * ∑ i, ∫ a, ‖d i a‖^2 ∂μ := by
  have hn (z : ℂ) : (↑(‖z‖^2) : ℂ) = star z * z := by
    rw [mul_comm, Complex.ofReal_pow]
    exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z).symm
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← integral_complex_ofReal, hn, slotDeterminant_inner_integral v d hv hd ho]
  calc
    _ = ∑ p : Equiv.Perm (Fin n), ∑ q : Equiv.Perm (Fin n),
        star (((p.sign : ℤ) : ℂ)) * (((q.sign : ℤ) : ℂ)) *
          ∑ i, (∫ a, star (d (p i) a) * d (q i) a ∂μ) *
            ∏ j ∈ Finset.univ.erase i, if p j = q j then (1:ℂ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
    _ = _ := slater_one_body_trace_algebra
      (fun a b => ∫ x, star (d a x) * d b x ∂μ)

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_CubeGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma tensorOrbital_fderiv {n : ℕ} {α : Type*} (v : α → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (p : Fin n → α) (s : Spins n) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (tensorOrbital v p s) x (EuclideanSpace.single (i,b) 1) =
      (fderiv ℝ (fun y => v (p i) y (s i)) (position x i) (EuclideanSpace.single b 1)) *
        ∏ j ∈ Finset.univ.erase i, v (p j) (position x j) (s j) := by
  have hd (j : Fin n) : DifferentiableAt ℝ (fun y : Configuration n =>
      v (p j) (position y j) (s j)) x :=
    by
      change DifferentiableAt ℝ ((fun y : Space => v (p j) y (s j)) ∘ (positionCLM j)) x
      exact ((hv (p j) (s j)).differentiable (by simp) (positionCLM j x)).comp x
        (positionCLM j).differentiableAt
  have he (j : Fin n) : fderiv ℝ (fun y : Configuration n => v (p j) (position y j) (s j)) x =
      (fderiv ℝ (fun y => v (p j) y (s j)) (position x j)).comp (positionCLM j) := by
    exact (((hv (p j) (s j)).differentiable (by simp) (position x j)).hasFDerivAt.comp x
      (positionCLM j).hasFDerivAt).fderiv
  unfold tensorOrbital
  rw [fderiv_finsetProd (fun j _ => hd j), sum_apply]
  simp only [smul_apply, smul_eq_mul, he, ContinuousLinearMap.comp_apply,
    positionCLM_single]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j hj hji
    simp only [ite_eq_right hji, map_zero, mul_zero]
  · simp

lemma slaterConfiguration_fderiv {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (s : Spins n) (x : Configuration n) (i : Fin n) (b : Fin 3) :
    fderiv ℝ (slaterConfiguration v s) x (EuclideanSpace.single (i,b) 1) =
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        slotDeterminant (fun a (sx : Fin 2 × Space) => v a sx.2 sx.1)
          (fun a sx => fderiv ℝ (fun y => v a y sx.1) sx.2 (EuclideanSpace.single b 1)) i
          (fun j => (s j, position x j)) := by
  have ht (p : Equiv.Perm (Fin n)) : DifferentiableAt ℝ (tensorOrbital v p s) x :=
    (tensorOrbital_contDiff v hv p s).differentiable (by simp) x
  rw [slaterConfiguration_expansion, fderiv_const_mul (DifferentiableAt.fun_sum (fun p _ =>
      (ht p).const_mul _)), fderiv_fun_sum (fun p _ => (ht p).const_mul _)]
  simp only [smul_apply, smul_eq_mul, sum_apply,
    fderiv_const_mul (ht _), tensorOrbital_fderiv v hv]
  unfold slotDeterminant
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [slotTensor_factor]

noncomputable def cubeGradient {n : ℕ} (ψ : H1Vector n) (a : Fin n × Fin 3)
    (z : Fin n → Fin 2 × (Fin 3 → ℝ)) : ℂ :=
  ψ.gradient ((spinCubeEquiv n) z).1 a (WithLp.toLp 2 ((spinCubeEquiv n) z).2)

lemma H1Vector.gradient_spinSpace_memLp {n : ℕ} (ψ : H1Vector n) (a : Fin n × Fin 3) :
    MemLp (fun sx : Spins n × ((Fin n × Fin 3) → ℝ) =>
      ψ.gradient sx.1 a (WithLp.toLp 2 sx.2)) 2 (Measure.count.prod volume) := by
  have hi (s : Spins n) : MemLp (fun t : Spins n => if t = s then (1:ℂ) else 0) 2 Measure.count := by
    apply MemLp.of_bound (by fun_prop) 1
    exact ae_of_all _ (fun t => by split_ifs <;> norm_num)
  have H := memLp_finsetSum Finset.univ (fun (s : Spins n) _ => tensorPair_memLp (hi s)
    ((ψ.partial_L2 s a).comp_measurePreserving (PiLp.volume_preserving_toLp _)))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext sx
  simp only [ite_mul, one_mul, zero_mul]
  simp

lemma cubeGradient_full_norm {n : ℕ} (ψ : H1Vector n) (a : Fin n × Fin 3) :
    (∫ z, ‖cubeGradient ψ a z‖^2 ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) =
      ∑ s, ∫ x, ‖ψ.gradient s a x‖^2 := by
  unfold cubeGradient
  rw [(spinCubeEquiv_full_measurePreserving n).integral_comp'
    (fun sx => ‖ψ.gradient sx.1 a (WithLp.toLp 2 sx.2)‖^2)]
  rw [integral_prod _ (ψ.gradient_spinSpace_memLp a).norm.integrable_sq, integral_count]
  apply Finset.sum_congr rfl
  intro s _
  exact (show MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin n × Fin 3) → ℝ)) volume volume from
    PiLp.volume_preserving_toLp _).integral_comp' (fun x => ‖ψ.gradient s a x‖^2)

lemma slaterState_cubeGradient {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (i : Fin n) (b : Fin 3) (z : Fin n → Fin 2 × (Fin 3 → ℝ)) :
    cubeGradient (slaterState v hv hC) (i,b) z =
      (↑(Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) *
        slotDeterminant (fun a => flatSpinOrbital (v a))
          (fun a => flatSpinOrbital (fun x s =>
            fderiv ℝ (fun y => v a y s) x (EuclideanSpace.single b 1))) i z := by
  change fderiv ℝ (slaterConfiguration v _) _ (EuclideanSpace.single (i,b) 1) = _
  rw [slaterConfiguration_fderiv v hv]
  rfl

lemma slaterState_kinetic {n : ℕ} (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ i j, (∑ s : Fin 2, ∫ x : Space, star (v i x s) * v j x s) =
      if i = j then (1:ℂ) else 0) :
    kinetic (slaterState v hv hC) = (1/2:ℝ) * ∑ i, ∑ s, ∑ b : Fin 3,
      ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
  have hV (i : Fin n) (s : Fin 2) : MemLp (fun x => v i x s) 2 volume :=
    (hv i s).continuous.memLp_of_hasCompactSupport (hC i s)
  have hD (i : Fin n) (s : Fin 2) (b : Fin 3) :
      MemLp (fun x => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)) 2 volume :=
    (((hv i s).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hC i s).fderiv_apply ℝ _)
  have hO (i j : Fin n) : (∫ a, star (flatSpinOrbital (v i) a) * flatSpinOrbital (v j) a
      ∂spinSpaceMeasure) = if i = j then (1:ℂ) else 0 := by
    rw [flatSpinOrbital_inner (v i) (v j) (hV i) (hV j)]
    exact ho i j
  have hb (b : Fin 3) : (∑ i, ∑ s, ∫ x, ‖(slaterState v hv hC).gradient s (i,b) x‖^2) =
      ∑ i, ∑ s, ∫ x : Space,
        ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
    simp_rw [← cubeGradient_full_norm, slaterState_cubeGradient]
    have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
    simp only [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le, integral_const_mul]
    rw [← Finset.mul_sum, slotDeterminant_total_norm_sq _ _
      (fun i => flatSpinOrbital_memLp (v i) (hV i))
      (fun i => flatSpinOrbital_memLp _ (fun s => hD i s b)) hO,
      ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
    apply Finset.sum_congr rfl
    intro i _
    have h := flatSpinOrbital_inner
      (fun x s => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1))
      (fun x s => fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1))
      (fun s => hD i s b) (fun s => hD i s b)
    have hz (z : ℂ) : star z * z = (↑(‖z‖^2) : ℂ) := by
      rw [mul_comm, Complex.ofReal_pow]
      exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z
    simp_rw [hz, integral_complex_ofReal] at h
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_sum] using h)
  unfold kinetic
  congr 1
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ b : Fin 3, ∑ i, ∑ s, ∫ x, ‖(slaterState v hv hC).gradient s (i,b) x‖^2 := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ i, ∑ b : Fin 3, ∑ s, ∫ x, ‖(slaterState v hv hC).gradient s (i,b) x‖^2 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      simp_rw [hb]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_DeterminantBodyReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma determinant_one_body_real {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b, Integrable (fun x => (w x : ℂ)*(star (v a x)*v b x)) μ) :
    (∫ x : Fin n → A, (∑ i, w (x i))*‖determinantWave v x‖^2 ∂(Measure.pi fun _ => μ)) =
      (n.factorial : ℝ)*(∑ a, ∫ x, w x*‖v a x‖^2 ∂μ) := by
  have H := determinant_one_body_integral v (fun x => (w x : ℂ)) hv ho hw
  simp_rw [complex_star_mul_self] at H
  apply Complex.ofReal_injective
  push_cast
  simpa only [← Complex.ofReal_sum, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.ofReal_natCast] using H

lemma slaterWave_one_body_real {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (w : A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hw : ∀ a b, Integrable (fun x => (w x : ℂ)*(star (v a x)*v b x)) μ) :
    (∫ x : Fin n → A, (∑ i, w (x i))*‖slaterWave v x‖^2 ∂(Measure.pi fun _ => μ)) =
      ∑ a, ∫ x, w x*‖v a x‖^2 ∂μ := by
  have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have he (x : Fin n → A) : (∑ i, w (x i))*‖slaterWave v x‖^2 =
      (n.factorial : ℝ)⁻¹*((∑ i, w (x i))*‖determinantWave v x‖^2) := by
    simp only [slaterWave, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le]
    ring
  simp_rw [he]
  rw [integral_const_mul, determinant_one_body_real v w hv ho hw,
    ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

lemma compact_coulomb_onebody_integrable (f u : Space → ℂ)
    (hf : Continuous f) (hu : Continuous u) (hC : HasCompactSupport f) (R : Space) :
    Integrable (fun x => (coulombKernel (x-R) : ℂ)*(star (f x)*u x)) := by
  have hF := hf.norm.mul hu.norm
  have hFC : HasCompactSupport (fun x => ‖f x‖*‖u x‖) := hC.norm.mul_right
  obtain ⟨M,hM⟩ := hFC.exists_bound_of_continuous hF
  have hI := coulomb_convolution_integrable (hF.integrable_of_hasCompactSupport hFC)
    hF.measurable (fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun x => (le_abs_self _).trans (hM x)) (by norm_num : (0:ℝ)<1) R
  apply hI.mono' ?_ (ae_of_all _ (fun x => ?_))
  · exact (((coulombKernel_measurable.comp (measurable_id.sub_const R)).complex_ofReal).mul
      (hf.star.mul hu).measurable).aestronglyMeasurable
  · simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (coulombKernel_nonneg _)]
    exact le_of_eq (by rw [coulombKernel, coulombKernel, norm_sub_rev]; rfl)

lemma compact_attraction_cross_integrable {M : ℕ} (S : Nuclei M) (f u : Space → ℂ)
    (hf : Continuous f) (hu : Continuous u) (hC : HasCompactSupport f) :
    Integrable (fun x => (attraction S x : ℂ)*(star (f x)*u x)) := by
  have H := integrable_finsetSum Finset.univ (fun j _ =>
    (compact_coulomb_onebody_integrable f u hf hu hC (S.position j)).const_mul (S.charge j : ℂ))
  apply H.congr
  filter_upwards [] with x
  simp only [attraction, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_assoc]

lemma slaterState_nuclear {M n : ℕ} (S : Nuclei M) (v : Fin n → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) :
    nuclearEnergy S (slaterState v hv hC) = ∫ x, attraction S x*slaterDensity v x := by
  have hV (a : Fin n) (s : Fin 2) : MemLp (fun x => v a x s) 2 volume :=
    (hv a s).continuous.memLp_of_hasCompactSupport (hC a s)
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp _
  have hi (a b : Fin n) (s : Fin 2) := compact_attraction_cross_integrable S
    (fun x => v a x s) (fun x => v b x s) (hv a s).continuous (hv b s).continuous (hC a s)
  have hO (a b : Fin n) : (∫ x, star (flatSpinOrbital (v a) x)*flatSpinOrbital (v b) x
      ∂spinSpaceMeasure) = if a = b then (1:ℂ) else 0 := by
    rw [flatSpinOrbital_inner (v a) (v b) (hV a) (hV b)]
    exact ho a b
  have hW (a b : Fin n) : Integrable (fun x => (attraction S (WithLp.toLp 2 x.2) : ℂ)*
      (star (flatSpinOrbital (v a) x)*flatSpinOrbital (v b) x)) spinSpaceMeasure :=
    integrable_finite_count_prod _ (fun s => hm.integrable_comp_of_integrable (hi a b s))
  have H := slaterWave_one_body_real (fun a => flatSpinOrbital (v a))
    (fun x => attraction S (WithLp.toLp 2 x.2))
    (fun a => flatSpinOrbital_memLp (v a) (hV a)) hO hW
  rw [← slaterState_cubeState v hv hC] at H
  have he := spinConfiguration_integral
    (fun s x => (∑ i, attraction S (position x i))*‖(slaterState v hv hC).value s x‖^2)
    ((slaterState v hv hC).nuclear_integrable S)
  change (∫ x, (∑ i, attraction S (WithLp.toLp 2 (x i).2))*
    ‖cubeState (slaterState v hv hC) x‖^2 ∂(Measure.pi fun _ : Fin n => spinSpaceMeasure)) =
      nuclearEnergy S (slaterState v hv hC) at he
  rw [he] at H
  rw [H]
  have hr (a : Fin n) (s : Fin 2) : Integrable (fun x => attraction S x*‖v a x s‖^2) := by
    have ht := hi a a s
    simp_rw [complex_star_mul_self, ← Complex.ofReal_mul] at ht
    exact ht.re
  have he1 (a : Fin n) : (∫ x, attraction S (WithLp.toLp 2 x.2)*‖flatSpinOrbital (v a) x‖^2
      ∂spinSpaceMeasure) = ∑ s, ∫ x : Space, attraction S x*‖v a x s‖^2 := by
    unfold spinSpaceMeasure flatSpinOrbital
    rw [integral_finite_count_prod (μ := volume)
      (fun x : Fin 2 × (Fin 3 → ℝ) => attraction S (WithLp.toLp 2 x.2)*‖v a (WithLp.toLp 2 x.2) x.1‖^2)
      (fun s => hm.integrable_comp_of_integrable (hr a s))]
    apply Finset.sum_congr rfl
    intro s _
    exact hm.integral_comp' (fun x : Space => attraction S x*‖v a x s‖^2)
  simp_rw [he1]
  simp only [slaterDensity, Finset.mul_sum]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun s _ => hr a s))]
  apply Finset.sum_congr rfl
  intro a _
  exact (integral_finsetSum _ (fun s _ => hr a s)).symm
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_Occupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma slaterWave_two_body_exact {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [SigmaFinite μ] {n : ℕ} (v : Fin n → A → ℂ) (W : A → A → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ) *
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ)) :
    (∫ x : Fin n → A, (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
      ‖slaterWave v x‖^2 ∂(Measure.pi fun _ => μ)) = ∑ i, ∑ j, slaterPairEntry μ v W i j := by
  have H := determinant_two_body_integral v (fun x y => (W x y : ℂ)) hv ho hW
  simp only [complex_star_mul_self, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
    integral_complex_ofReal] at H
  have HR := congrArg Complex.re H
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum, Complex.sub_re] at HR
  have hn : (0:ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have he (x : Fin n → A) : (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
      ‖slaterWave v x‖^2 = (n.factorial : ℝ)⁻¹ *
        ((∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) * ‖determinantWave v x‖^2) := by
    simp only [slaterWave, norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt hn.le]
    ring
  simp_rw [he]
  rw [integral_const_mul, HR, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  simp only [slaterPairEntry, complex_star_mul_self, ← Complex.ofReal_mul,
    integral_complex_ofReal, Complex.ofReal_re]

lemma bernoulli_slater_pair_mean {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] (v : ι → A → ℂ) (W : A → A → ℝ)
    (lam : ι → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ) *
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ)) :
    (∑ w : ι → Bool, bernoulliWeight lam w *
      (∫ x : Fin (Fintype.card {i // w i = true}) → A,
        (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
        ‖slaterWave (fun a => v (occupiedIndex w a)) x‖^2 ∂(Measure.pi fun _ => μ))) =
      ∑ i, ∑ j, lam i * lam j * slaterPairEntry μ v W i j := by
  classical
  have he (w : ι → Bool) := slaterWave_two_body_exact
    (fun a => v (occupiedIndex w a)) W (fun a => hv _) (fun a b => by
      simp only [ho, (occupiedIndex w).injective.eq_iff])
    (fun a b c d => hW _ _ _ _)
  simp_rw [he]
  have hs (w : ι → Bool) :
      (∑ a, ∑ b, slaterPairEntry μ (fun a => v (occupiedIndex w a)) W a b) =
      ∑ i, ∑ j, occupancy (w i)*occupancy (w j)*slaterPairEntry μ v W i j := by
    change (∑ a, ∑ b, slaterPairEntry μ v W (occupiedIndex w a) (occupiedIndex w b)) = _
    rw [sum_occupiedIndex_real w (fun i => ∑ b, slaterPairEntry μ v W i (occupiedIndex w b))]
    simp_rw [sum_occupiedIndex_real, Finset.mul_sum, mul_assoc]
  simp_rw [hs]
  exact bernoulli_pair_mean lam _ (slaterPairEntry_self μ v W)
end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WeightedExchangeAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma bernoulli_slater_pair_upper {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [SigmaFinite μ] (v : ι → A → ℂ) (W : A → A → ℝ)
    (lam : ι → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (ho : ∀ a b, (∫ x, star (v a x)*v b x ∂μ) = if a = b then (1:ℂ) else 0)
    (hW : ∀ a b c d, Integrable (fun xy : A × A => (W xy.1 xy.2 : ℂ) *
      ((star (v a xy.1)*v c xy.1)*(star (v b xy.2)*v d xy.2))) (μ.prod μ))
    (hW0 : ∀ x y, 0 ≤ W x y) :
    (∑ w : ι → Bool, bernoulliWeight lam w *
      (∫ x : Fin (Fintype.card {i // w i = true}) → A,
        (∑ i, ∑ j ∈ Finset.univ.erase i, W (x i) (x j)) *
        ‖slaterWave (fun a => v (occupiedIndex w a)) x‖^2 ∂(Measure.pi fun _ => μ))) ≤
      ∫ xy : A × A, W xy.1 xy.2 *
        ((∑ i, lam i*‖v i xy.1‖^2)*(∑ j, lam j*‖v j xy.2‖^2)) ∂(μ.prod μ) := by
  rw [bernoulli_slater_pair_mean v W lam hv ho hW]
  exact weighted_slaterPairEntry_upper μ v lam W hW hW0

noncomputable def selectedSlater {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (w : ι → Bool) :
    H1Vector (Fintype.card {i // w i = true}) :=
  slaterState (fun index => v (occupiedIndex w index))
    (fun index spin => hv (occupiedIndex w index) spin)
    (fun index spin => hC (occupiedIndex w index) spin)

lemma bernoulli_slater_kinetic_mean {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * kinetic (selectedSlater v hv hC w)) =
      (1/2:ℝ)*∑ i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2 := by
  have hk (w : ι → Bool) := slaterState_kinetic
    (fun a => v (occupiedIndex w a)) (fun a s => hv _ s) (fun a s => hC _ s)
    (fun a b => by simp only [ho, (occupiedIndex w).injective.eq_iff])
  simp only [selectedSlater, hk]
  simp_rw [mul_left_comm (bernoulliWeight lam _) (1/2:ℝ)]
  rw [← Finset.mul_sum]
  congr 1
  exact bernoulli_chosen_sum lam (fun i => ∑ s, ∑ b : Fin 3,
    ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2)

noncomputable def finiteFermiDensity {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ) (lam : ι → ℝ) (x : Space) : ℝ :=
  ∑ i, lam i * ∑ s, ‖v i x s‖^2

lemma selectedSlater_density {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ) (w : ι → Bool) (x : Space) :
    slaterDensity (fun a => v (occupiedIndex w a)) x =
      ∑ i, occupancy (w i)*∑ s, ‖v i x s‖^2 :=
  sum_occupiedIndex_real w (fun i => ∑ s, ‖v i x s‖^2)

lemma finiteFermiDensity_nuclear_integrable {ι : Type*} [Fintype ι] {M : ℕ}
    (S : Nuclei M) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (lam : ι → ℝ) :
    Integrable (fun x => attraction S x*finiteFermiDensity v lam x) := by
  have hi (i : ι) (s : Fin 2) : Integrable (fun x => attraction S x*‖v i x s‖^2) := by
    have h := compact_attraction_cross_integrable S (fun x => v i x s) (fun x => v i x s)
      (hv i s).continuous (hv i s).continuous (hC i s)
    simp_rw [complex_star_mul_self, ← Complex.ofReal_mul] at h
    exact h.re
  have H := integrable_finsetSum Finset.univ (fun i _ =>
    (integrable_finsetSum Finset.univ (fun s _ => hi i s)).const_mul (lam i))
  apply H.congr
  filter_upwards [] with x
  simp only [finiteFermiDensity, Finset.mul_sum]
  congr 1
  funext i
  congr 1
  funext s
  ring

lemma bernoulli_slater_nuclear_mean {ι : Type*} [Fintype ι] {M : ℕ}
    (S : Nuclei M) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * nuclearEnergy S (selectedSlater v hv hC w)) =
      ∫ x, attraction S x*finiteFermiDensity v lam x := by
  have hn (w : ι → Bool) := slaterState_nuclear S
    (fun a => v (occupiedIndex w a)) (fun a s => hv _ s) (fun a s => hC _ s)
    (fun a b => by simp only [ho, (occupiedIndex w).injective.eq_iff])
  simp only [selectedSlater, hn, selectedSlater_density]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun w _ =>
    (finiteFermiDensity_nuclear_integrable S v hv hC (fun i => occupancy (w i))).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp_rw [mul_left_comm (bernoulliWeight lam _) (attraction S x)]
  rw [← Finset.mul_sum, bernoulli_linear_mean]
  rfl
end Coulomb

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FiniteProdSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma finiteFermiDensity_direct_flat {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (lam : ι → ℝ) :
    (∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
      coulombKernel (WithLp.toLp 2 xy.1.2-WithLp.toLp 2 xy.2.2) *
        ((∑ i, lam i*‖flatSpinOrbital (v i) xy.1‖^2)*
          (∑ j, lam j*‖flatSpinOrbital (v j) xy.2‖^2))
        ∂(spinSpaceMeasure.prod spinSpaceMeasure)) =
    ∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
      (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2) := by
  let F (s t : Fin 2) (xy : Space × Space) : ℝ := coulombKernel (xy.1-xy.2)*
    ((∑ i, lam i*‖v i xy.1 s‖^2)*(∑ j, lam j*‖v j xy.2 t‖^2))
  have hF (s t : Fin 2) : Integrable (F s t) :=
    finite_weighted_bilinear_integrable volume (fun i x => ‖v i x s‖^2)
      (fun i x => ‖v i x t‖^2) lam (fun x y => coulombKernel (x-y))
      (fun i j => compact_coulomb_direct_integrable (fun x => v i x s) (fun x => v j x t)
        (hv i s).continuous (hv j t).continuous (hC i s) (hC j t))
  change (∫ xy : (Fin 2 × (Fin 3 → ℝ)) × (Fin 2 × (Fin 3 → ℝ)),
    F xy.1.1 xy.2.1 (WithLp.toLp 2 xy.1.2, WithLp.toLp 2 xy.2.2)
      ∂(spinSpaceMeasure.prod spinSpaceMeasure)) = _
  rw [spinPair_integral F hF]
  simp_rw [← integral_finsetSum _ (fun t _ => hF _ t)]
  rw [← integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun t _ => hF s t))]
  apply integral_congr_ae
  filter_upwards [] with xy
  have hs (x : Space) : (∑ s, ∑ i, lam i*‖v i x s‖^2) = finiteFermiDensity v lam x := by
    rw [Finset.sum_comm]
    simp only [finiteFermiDensity, Finset.mul_sum]
  change (∑ s, ∑ t, F s t xy) = _
  rw [← hs xy.1, ← hs xy.2, finiteProd_sum]

lemma bernoulli_slater_pairEnergy_upper {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * pairEnergy (selectedSlater v hv hC w)) ≤
      (1/2:ℝ)*∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2) := by
  have hV (i : ι) (s : Fin 2) : MemLp (fun x => v i x s) 2 volume :=
    (hv i s).continuous.memLp_of_hasCompactSupport (hC i s)
  have hO (i j : ι) : (∫ x, star (flatSpinOrbital (v i) x)*flatSpinOrbital (v j) x
      ∂spinSpaceMeasure) = if i = j then (1:ℂ) else 0 := by
    rw [flatSpinOrbital_inner (v i) (v j) (hV i) (hV j)]
    exact ho i j
  have H := bernoulli_slater_pair_upper (fun i => flatSpinOrbital (v i))
    (fun x y => coulombKernel (WithLp.toLp 2 x.2-WithLp.toLp 2 y.2)) lam
    (fun i => flatSpinOrbital_memLp (v i) (hV i)) hO
    (flatSpinOrbital_coulomb_cross_integrable v hv hC)
    (fun x y => coulombKernel_nonneg _)
  have he (w : ι → Bool) :
      (∫ x : Fin (Fintype.card {i // w i = true}) → Fin 2 × (Fin 3 → ℝ),
        (∑ i, ∑ j ∈ Finset.univ.erase i,
          coulombKernel (WithLp.toLp 2 (x i).2-WithLp.toLp 2 (x j).2)) *
        ‖slaterWave (fun a => flatSpinOrbital (v (occupiedIndex w a))) x‖^2
          ∂(Measure.pi fun _ => spinSpaceMeasure)) = 2*pairEnergy (selectedSlater v hv hC w) := by
    rw [← slaterState_cubeState (fun a => v (occupiedIndex w a))
      (fun a s => hv _ s) (fun a s => hC _ s), cubeState_pair_energy]
    rfl
  simp_rw [he] at H
  rw [finiteFermiDensity_direct_flat v hv hC lam] at H
  have hm : (∑ w : ι → Bool, bernoulliWeight lam w * (2*pairEnergy (selectedSlater v hv hC w))) =
      2*∑ w : ι → Bool, bernoulliWeight lam w * pairEnergy (selectedSlater v hv hC w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hm] at H
  linarith

lemma bernoulli_slater_form_upper {ι : Type*} [Fintype ι] {M : ℕ}
    (S : Nuclei M) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * form S (selectedSlater v hv hC w)) ≤
      (1/2:ℝ)*(∑ i, lam i * ∑ s, ∑ b : Fin 3,
        ∫ x : Space, ‖fderiv ℝ (fun y => v i y s) x (EuclideanSpace.single b 1)‖^2) -
      (∫ x, attraction S x*finiteFermiDensity v lam x) +
      (1/2:ℝ)*(∫ xy : Space × Space, coulombKernel (xy.1-xy.2)*
        (finiteFermiDensity v lam xy.1*finiteFermiDensity v lam xy.2)) := by
  simp only [form, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [bernoulli_slater_kinetic_mean v hv hC ho lam, bernoulli_slater_nuclear_mean S v hv hC ho lam]
  gcongr
  exact bernoulli_slater_pairEnergy_upper v hv hC ho lam

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_JoinSpins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
namespace Coulomb
def joinSpins (m k : ℕ) : Spins m × Spins k ≃ Spins (m+k) where
  toFun := fun s => Fin.addCases s.1 s.2
  invFun := fun s => (s ∘ Fin.castAdd k, s ∘ Fin.natAdd m)
  left_inv := by
    intro s
    ext i <;> simp
  right_inv := by
    intro s
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Function.comp_def]

lemma joinSpins_left (m k : ℕ) (s : Spins m) (t : Spins k) :
    (joinSpins m k (s,t)) ∘ Fin.castAdd k = s := by
  funext i
  simp [joinSpins, Function.comp_def]
lemma joinSpins_right (m k : ℕ) (s : Spins m) (t : Spins k) :
    (joinSpins m k (s,t)) ∘ Fin.natAdd m = t := by
  funext i
  simp [joinSpins, Function.comp_def]

lemma sum_joinSpins {m k : ℕ} (F : Spins (m+k) → ℝ) :
    (∑ s, F s) = ∑ s : Spins m, ∑ t : Spins k, F (joinSpins m k (s,t)) := by
  rw [← Equiv.sum_comp (joinSpins m k), Fintype.sum_prod_type]

lemma tensorGradient_square_integral_left {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin m × Fin 3) :
    (∫ x, ‖tensorGradient u v s (Fin.castAdd k a.1,a.2) x‖^2) =
      (∫ x, ‖u.gradient (s ∘ Fin.castAdd k) a x‖^2)*
        (∫ y, ‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
  rw [← (joinConfiguration_measurePreserving m k).integral_comp'
    (fun x => ‖tensorGradient u v s (Fin.castAdd k a.1,a.2) x‖^2)]
  change (∫ z : Configuration m × Configuration k,
    ‖tensorGradient u v s (Fin.castAdd k a.1,a.2) (joinConfiguration m k z)‖^2
      ∂(volume.prod volume)) = _
  simp_rw [tensorGradient_join_left, norm_mul, mul_pow]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun x : Configuration m => ‖u.gradient (s ∘ Fin.castAdd k) a x‖^2)
    (fun y : Configuration k => ‖v.value (s ∘ Fin.natAdd m) y‖^2)

lemma tensorGradient_square_integral_right {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) (a : Fin k × Fin 3) :
    (∫ x, ‖tensorGradient u v s (Fin.natAdd m a.1,a.2) x‖^2) =
      (∫ x, ‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, ‖v.gradient (s ∘ Fin.natAdd m) a y‖^2) := by
  rw [← (joinConfiguration_measurePreserving m k).integral_comp'
    (fun x => ‖tensorGradient u v s (Fin.natAdd m a.1,a.2) x‖^2)]
  change (∫ z : Configuration m × Configuration k,
    ‖tensorGradient u v s (Fin.natAdd m a.1,a.2) (joinConfiguration m k z)‖^2
      ∂(volume.prod volume)) = _
  simp_rw [tensorGradient_join_right, norm_mul, mul_pow]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun x : Configuration m => ‖u.value (s ∘ Fin.castAdd k) x‖^2)
    (fun y : Configuration k => ‖v.gradient (s ∘ Fin.natAdd m) a y‖^2)

lemma kinetic_tensor {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    kinetic (u.tensor v) = kinetic u*mass v+mass u*kinetic v := by
  change (1/2:ℝ)*(∑ s, ∑ a, ∫ x, ‖tensorGradient u v s a x‖^2) = _
  simp_rw [sum_configurationBlocks, tensorGradient_square_integral_left,
    tensorGradient_square_integral_right]
  rw [sum_joinSpins]
  simp only [joinSpins_left, joinSpins_right]
  simp only [mass, kinetic, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [← Finset.sum_mul_sum]
  ring
end Coulomb

open scoped Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
namespace Coulomb

noncomputable section
lemma test_L2 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) :
    MemLp (fun x => (φ x : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
    (hC.comp_left Complex.ofReal_zero)

lemma test_derivative_L2 {n : ℕ} {φ : Configuration n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hC : HasCompactSupport φ) (a : Configuration n) :
    MemLp (fun x => (fderiv ℝ φ x a : ℂ)) 2 volume :=
  (Complex.continuous_ofReal.comp
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
    ((hC.fderiv_apply ℝ a).comp_left Complex.ofReal_zero)

def H1Vector.finiteSum {n : ℕ} {ι : Type*} [Fintype ι] (u : ι → H1Vector n) : H1Vector n where
  value := fun s x => ∑ i, (u i).value s x
  gradient := fun s a x => ∑ i, (u i).gradient s a x
  value_L2 := fun s => memLp_finsetSum _ (fun i _ => (u i).value_L2 s)
  partial_L2 := fun s a => memLp_finsetSum _ (fun i _ => (u i).partial_L2 s a)
  weak_partial := by
    intro s a φ hφ hC
    simp only [Finset.sum_mul]
    rw [integral_finsetSum (f := fun i x => (u i).value s x *
        (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) _ (fun i _ => (u i).value_L2 s |>.integrable_mul
      (test_derivative_L2 hφ hC (EuclideanSpace.single a 1))),
      integral_finsetSum (f := fun i x => (u i).gradient s a x * (φ x : ℂ))
        _ (fun i _ => (u i).partial_L2 s a |>.integrable_mul
      (test_L2 hφ hC))]
    simp_rw [H1Vector.weak_partial _ _ _ _ hφ hC]
    rw [Finset.sum_neg_distrib]

lemma permutationIsometry_single {n : ℕ} (p : Equiv.Perm (Fin n)) (a : Fin n × Fin 3) :
    permutationIsometry p (EuclideanSpace.single a 1) =
      EuclideanSpace.single (p.symm a.1,a.2) 1 := by
  rw [permutationIsometry_apply]
  ext ⟨i,b⟩
  simp [permute, PiLp.single_apply, Prod.ext_iff, ← Equiv.eq_symm_apply]

lemma permutation_gradient {n : ℕ} (u : H1Vector n) (p : Equiv.Perm (Fin n))
    (s : Spins n) (a : Fin n × Fin 3) (x : Configuration n) :
    (u.permutation p).gradient s a x =
      u.gradient (s ∘ p) (p.symm a.1,a.2) (permute p x) := by
  change (∑ k, ((permutationIsometry p (EuclideanSpace.single a 1)) k : ℂ) *
    u.gradient (s ∘ p) k (permutationIsometry p x)) = _
  rw [permutationIsometry_single, permutationIsometry_apply]
  simp [PiLp.single_apply, apply_ite]

lemma permute_mul {n : ℕ} (p q : Equiv.Perm (Fin n)) (x : Configuration n) :
    permute q (permute p x) = permute (p*q) x := by
  rfl

def H1Vector.fullAntisymmetrize {n : ℕ} (u : H1Vector n) : H1Vector n :=
  H1Vector.finiteSum (fun p : Equiv.Perm (Fin n) =>
    (u.permutation p).scale (((p.sign : ℤ) : ℂ)))

end
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PermuteJoinBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
namespace Coulomb
lemma permute_join_block {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k))
    (x : Configuration m) (y : Configuration k) :
    permute (blockHom m k (p,q)) (joinConfiguration m k (x,y)) =
      joinConfiguration m k (permute p x, permute q y) := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    change joinConfiguration m k (x,y) (blockHom m k (p,q) (Fin.castAdd k j),b) = _
    rw [blockHom_left, joinConfiguration_left, joinConfiguration_left]
    rfl
  · intro j
    change joinConfiguration m k (x,y) (blockHom m k (p,q) (Fin.natAdd m j),b) = _
    rw [blockHom_right, joinConfiguration_right, joinConfiguration_right]
    rfl

lemma spins_block_left {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k))
    (s : Spins (m+k)) :
    (s ∘ blockHom m k (p,q)) ∘ Fin.castAdd k = (s ∘ Fin.castAdd k) ∘ p := by
  funext i
  simp [Function.comp_def, blockHom_left]
lemma spins_block_right {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k))
    (s : Spins (m+k)) :
    (s ∘ blockHom m k (p,q)) ∘ Fin.natAdd m = (s ∘ Fin.natAdd m) ∘ q := by
  funext i
  simp [Function.comp_def, blockHom_right]

lemma tensor_block_covariance {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v)
    (h : Equiv.Perm (Fin (m+k))) (hh : h ∈ blockGroup m k) (s : Spins (m+k)) :
    (u.tensor v).permutation h |>.value s =ᵐ[volume]
      fun x => ((h.sign : ℤ) : ℂ)*(u.tensor v).value s x := by
  rcases hh with ⟨⟨p,q⟩,rfl⟩
  have H1 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      u.value ((s ∘ Fin.castAdd k) ∘ p) (permute p z.1) =
        ((p.sign : ℤ) : ℂ)*u.value (s ∘ Fin.castAdd k) z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (hu p (s ∘ Fin.castAdd k))
  have H2 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      v.value ((s ∘ Fin.natAdd m) ∘ q) (permute q z.2) =
        ((q.sign : ℤ) : ℂ)*v.value (s ∘ Fin.natAdd m) z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (hv q (s ∘ Fin.natAdd m))
  have H1' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H1
  have H2' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H2
  filter_upwards [H1',H2'] with x hx hy
  obtain ⟨⟨x,y⟩,rfl⟩ := (joinConfiguration m k).surjective x
  have hez : (joinConfiguration m k).symm.toHomeomorph.toMeasurableEquiv
      ((joinConfiguration m k) (x,y)) = (x,y) :=
    (joinConfiguration m k).symm_apply_apply (x,y)
  rw [hez] at hx hy
  change u.value ((s ∘ Fin.castAdd k) ∘ p) (permute p x) =
    ((p.sign : ℤ) : ℂ)*u.value (s ∘ Fin.castAdd k) x at hx
  change v.value ((s ∘ Fin.natAdd m) ∘ q) (permute q y) =
    ((q.sign : ℤ) : ℂ)*v.value (s ∘ Fin.natAdd m) y at hy
  rw [permutation_value]
  change tensorValue u v (s ∘ blockHom m k (p,q))
    (permute (blockHom m k (p,q)) (joinConfiguration m k (x,y))) =
    (((blockHom m k (p,q)).sign : ℤ) : ℂ)*tensorValue u v s (joinConfiguration m k (x,y))
  rw [permute_join_block, tensorValue_join, tensorValue_join, spins_block_left,
    spins_block_right, blockHom_sign, hx, hy]
  push_cast
  ring
lemma position_join_left {m k : ℕ} (x : Configuration m) (y : Configuration k) (i : Fin m) :
    position (joinConfiguration m k (x,y)) (Fin.castAdd k i) = position x i := by
  ext b
  exact joinConfiguration_left m k x y i b

lemma position_split_left {m k : ℕ} (x : Configuration (m+k)) (i : Fin m) :
    position ((joinConfiguration m k).symm x).1 i = position x (Fin.castAdd k i) := by
  obtain ⟨⟨y,z⟩,rfl⟩ := (joinConfiguration m k).surjective x
  rw [ContinuousLinearEquiv.symm_apply_apply, position_join_left]

def blockRegion (m k : ℕ) (A B : Set Space) : Set (Configuration (m+k)) :=
  {x | (∀ i : Fin m, position x (Fin.castAdd k i) ∈ A) ∧
    (∀ j : Fin k, position x (Fin.natAdd m j) ∈ B)}

lemma blockRegion_split {m k : ℕ} (A B : Set Space) (x : Configuration (m+k)) :
    x ∈ blockRegion m k A B ↔
      ((joinConfiguration m k).symm x).1 ∈ allPositions A ∧
      ((joinConfiguration m k).symm x).2 ∈ allPositions B := by
  simp only [blockRegion, allPositions, Set.mem_ofPred_eq, position_split_left,
    position_split_right]

lemma isClosed_blockRegion {m k : ℕ} {A B : Set Space} (hA : IsClosed A) (hB : IsClosed B) :
    IsClosed (blockRegion m k A B) := by
  have he : blockRegion m k A B =
      (⋂ i : Fin m, (fun x => position x (Fin.castAdd k i)) ⁻¹' A) ∩
      (⋂ j : Fin k, (fun x => position x (Fin.natAdd m j)) ⁻¹' B) := by
    ext x
    simp [blockRegion]
  rw [he]
  exact (isClosed_iInter (fun i => hA.preimage (continuous_position _))).inter
    (isClosed_iInter (fun j => hB.preimage (continuous_position _)))

lemma tensor_configSupported {m k : ℕ} (u : H1Vector m) (v : H1Vector k) (A B : Set Space)
    (hu : SpatiallySupported u A) (hv : SpatiallySupported v B) :
    ConfigSupported (u.tensor v) (blockRegion m k A B) := by
  intro s
  have H1 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      z.1 ∉ allPositions A → u.value (s ∘ Fin.castAdd k) z.1 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (hu (s ∘ Fin.castAdd k))
  have H2 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      z.2 ∉ allPositions B → v.value (s ∘ Fin.natAdd m) z.2 = 0 :=
    Measure.quasiMeasurePreserving_snd.ae (hv (s ∘ Fin.natAdd m))
  have H1' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H1
  have H2' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H2
  filter_upwards [H1',H2'] with x hx hy
  intro hn
  change u.value _ _ * v.value _ _ = 0
  change ((joinConfiguration m k).symm x).1 ∉ allPositions A →
    u.value (s ∘ Fin.castAdd k) ((joinConfiguration m k).symm x).1 = 0 at hx
  change ((joinConfiguration m k).symm x).2 ∉ allPositions B →
    v.value (s ∘ Fin.natAdd m) ((joinConfiguration m k).symm x).2 = 0 at hy
  by_cases ha : ((joinConfiguration m k).symm x).1 ∈ allPositions A
  · have hb : ((joinConfiguration m k).symm x).2 ∉ allPositions B :=
      fun h => hn ((blockRegion_split A B x).2 ⟨ha,h⟩)
    rw [hy hb, mul_zero]
  · rw [hx ha, zero_mul]

lemma blockRegion_orbit_disjoint {m k : ℕ} {A B : Set Space} (hAB : Disjoint A B)
    (p q : Equiv.Perm (Fin (m+k))) (hpq : p⁻¹*q ∉ blockGroup m k)
    (x : Configuration (m+k)) :
    ¬ (permute p x ∈ blockRegion m k A B ∧ permute q x ∈ blockRegion m k A B) := by
  rcases exists_crossing_of_not_mem (p⁻¹*q) hpq with ⟨i,j,hij⟩
  intro ⟨hp,hq⟩
  have he : q (Fin.castAdd k i) = p (Fin.natAdd m j) := by
    have H := congrArg p hij
    simpa using H
  have ha := hq.1 i
  have hb := hp.2 j
  rw [position_permute, he] at ha
  rw [position_permute] at hb
  exact Set.disjoint_left.1 hAB ha hb

lemma configSupported_value_orthogonal {n : ℕ} (u : H1Vector n) (R : Set (Configuration n))
    (hu : ConfigSupported u R) (p q : Equiv.Perm (Fin n))
    (hR : ∀ x, ¬(permute p x ∈ R ∧ permute q x ∈ R)) (s : Spins n) :
    ∀ᵐ x ∂volume, star ((u.permutation p).value s x)*(u.permutation q).value s x = 0 := by
  have hp := (permute_measurePreserving p).quasiMeasurePreserving.ae (hu (s ∘ p))
  have hq := (permute_measurePreserving q).quasiMeasurePreserving.ae (hu (s ∘ q))
  filter_upwards [hp,hq] with x hx hy
  rw [permutation_value, permutation_value]
  by_cases hpx : permute p x ∈ R
  · rw [hy (fun h => hR x ⟨hpx,h⟩), mul_zero]
  · rw [hx hpx, star_zero, zero_mul]

lemma configSupported_gradient_orthogonal {n : ℕ} (u : H1Vector n) (R : Set (Configuration n))
    (hu : ConfigSupported u R) (hclosed : IsClosed R) (p q : Equiv.Perm (Fin n))
    (hR : ∀ x, ¬(permute p x ∈ R ∧ permute q x ∈ R)) (s : Spins n) (a : Fin n × Fin 3) :
    ∀ᵐ x ∂volume, star ((u.permutation p).gradient s a x)*(u.permutation q).gradient s a x = 0 := by
  have hp := (permute_measurePreserving p).quasiMeasurePreserving.ae
    (hu.gradient hclosed (s ∘ p) (p.symm a.1,a.2))
  have hq := (permute_measurePreserving q).quasiMeasurePreserving.ae
    (hu.gradient hclosed (s ∘ q) (q.symm a.1,a.2))
  filter_upwards [hp,hq] with x hx hy
  rw [permutation_gradient, permutation_gradient]
  by_cases hpx : permute p x ∈ R
  · rw [hy (fun h => hR x ⟨hpx,h⟩), mul_zero]
  · rw [hx hpx, star_zero, zero_mul]
end Coulomb

open scoped BigOperators ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NormSqSumCosets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb

lemma signed_coset_correlation {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : ∀ p, χ p*χ p = 1) (hχr : ∀ p, conj (χ p) = χ p)
    (H : Subgroup G) (f : G → ℂ)
    (hc : ∀ p h, h ∈ H → f (p*h) = χ h*f p)
    (hz : ∀ p q, p⁻¹*q ∉ H → conj (f p)*f q = 0) (p q : G) :
    conj (χ p*f p)*(χ q*f q) =
      if p⁻¹*q ∈ H then ((‖χ p*f p‖^2 : ℝ) : ℂ) else 0 := by
  by_cases h : p⁻¹*q ∈ H
  · rw [ite_eq_left h]
    have hq : q = p*(p⁻¹*q) := by group
    have hf := hc p (p⁻¹*q) h
    rw [← hq] at hf
    rw [hf]
    conv_lhs => arg 2; arg 1; rw [hq, map_mul]
    have he : χ p * χ (p⁻¹*q) * (χ (p⁻¹*q)*f p) = χ p*f p := by
      rw [mul_assoc, ← mul_assoc (χ (p⁻¹*q)), hχ, one_mul]
    rw [he, Complex.conj_mul']
    push_cast
    rfl
  · rw [ite_eq_right h, map_mul, hχr]
    calc
      _ = χ p*χ q*(conj (f p)*f q) := by ring
      _ = 0 := by rw [hz p q h, mul_zero]

lemma norm_sq_signed_sum_cosets {G : Type*} [Group G] [Fintype G]
    (χ : G →* ℂ) (hχ : ∀ p, χ p*χ p = 1) (hχr : ∀ p, conj (χ p) = χ p)
    (H : Subgroup G) (f : G → ℂ)
    (hc : ∀ p h, h ∈ H → f (p*h) = χ h*f p)
    (hz : ∀ p q, p⁻¹*q ∉ H → conj (f p)*f q = 0) :
    ‖∑ p, χ p*f p‖^2 = (Fintype.card H : ℝ)*∑ p, ‖f p‖^2 := by
  rw [norm_sq_sum_cosets H (fun p => χ p*f p)
    (signed_coset_correlation χ hχ hχr H f hc hz)]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have hn : ‖χ p‖^2 = 1 := by
    have H := congrArg norm (hχ p)
    simpa [norm_mul, pow_two] using H
  rw [norm_mul, mul_pow, hn, one_mul]
lemma permutation_mul_value {n : ℕ} (u : H1Vector n) (p q : Equiv.Perm (Fin n))
    (s : Spins n) (x : Configuration n) :
    (u.permutation (p*q)).value s x = ((u.permutation q).permutation p).value s x := by
  simp only [permutation_value, permute_mul]
  rfl
lemma permutation_mul_gradient {n : ℕ} (u : H1Vector n) (p q : Equiv.Perm (Fin n))
    (s : Spins n) (a : Fin n × Fin 3) (x : Configuration n) :
    (u.permutation (p*q)).gradient s a x = ((u.permutation q).permutation p).gradient s a x := by
  simp only [permutation_gradient, permute_mul]
  rfl

lemma permutation_gradient_covariance {n : ℕ} (u : H1Vector n) (h : Equiv.Perm (Fin n))
    (c : ℂ) (hc : ∀ s, (u.permutation h).value s =ᵐ[volume] fun x => c*u.value s x)
    (p : Equiv.Perm (Fin n)) (s : Spins n) (a : Fin n × Fin 3) :
    (u.permutation (p*h)).gradient s a =ᵐ[volume]
      fun x => c*(u.permutation p).gradient s a x := by
  have hg := H1Vector.gradient_congr_ae (u.permutation h) (u.scale c) hc
    (s ∘ p) (p.symm a.1,a.2)
  have H := (permute_measurePreserving p).quasiMeasurePreserving.ae hg
  filter_upwards [H] with x hx
  rw [permutation_mul_gradient]
  simpa only [permutation_gradient, H1Vector.scale] using hx

lemma fullAntisymmetrize_gradient {n : ℕ} (u : H1Vector n) (s : Spins n)
    (a : Fin n × Fin 3) (x : Configuration n) :
    u.fullAntisymmetrize.gradient s a x =
      ∑ p : Equiv.Perm (Fin n), complexSign n p*(u.permutation p).gradient s a x := rfl

lemma separated_fullAntisymmetrize_gradient_sq {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (s : Spins (m+k)) (a : Fin (m+k) × Fin 3) :
    ∀ᵐ x ∂volume, ‖(u.tensor v).fullAntisymmetrize.gradient s a x‖^2 =
      (Fintype.card (blockGroup m k) : ℝ)*
        ∑ p : Equiv.Perm (Fin (m+k)), ‖((u.tensor v).permutation p).gradient s a x‖^2 := by
  have hc : ∀ᵐ x ∂volume, ∀ p : Equiv.Perm (Fin (m+k)), ∀ h : Equiv.Perm (Fin (m+k)),
      h ∈ blockGroup m k →
      ((u.tensor v).permutation (p*h)).gradient s a x =
        complexSign (m+k) h*((u.tensor v).permutation p).gradient s a x := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro h
    by_cases hh : h ∈ blockGroup m k
    · exact (permutation_gradient_covariance (u.tensor v) h _
        (tensor_block_covariance u v hu hv h hh) p s a).mono (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun x h => (hh h).elim)
  have hz : ∀ᵐ x ∂volume, ∀ p q : Equiv.Perm (Fin (m+k)), p⁻¹*q ∉ blockGroup m k →
      conj (((u.tensor v).permutation p).gradient s a x)*((u.tensor v).permutation q).gradient s a x = 0 := by
    apply ae_all_iff.2
    intro p
    apply ae_all_iff.2
    intro q
    by_cases h : p⁻¹*q ∈ blockGroup m k
    · exact Filter.Eventually.of_forall (fun x hn => (hn h).elim)
    · exact (configSupported_gradient_orthogonal (u.tensor v) (blockRegion m k A B)
        (tensor_configSupported u v A B hsu hsv) (isClosed_blockRegion hA hB) p q
        (blockRegion_orbit_disjoint hAB p q h) s a).mono (fun x hx _ => hx)
  filter_upwards [hc,hz] with x hx hy
  rw [fullAntisymmetrize_gradient]
  exact norm_sq_signed_sum_cosets (complexSign (m+k)) complexSign_sq complexSign_real
    (blockGroup m k) (fun p => ((u.tensor v).permutation p).gradient s a x) hx hy
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_WedgeMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb

lemma kinetic_fullAntisymmetrize_of_sq {n : ℕ} (u : H1Vector n) (c : ℝ)
    (h : ∀ s a, ∀ᵐ x ∂volume, ‖u.fullAntisymmetrize.gradient s a x‖^2 =
      c*∑ p : Equiv.Perm (Fin n), ‖(u.permutation p).gradient s a x‖^2) :
    kinetic u.fullAntisymmetrize = c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ)*kinetic u := by
  have hi (s : Spins n) (a : Fin n × Fin 3) : (∫ x, ‖u.fullAntisymmetrize.gradient s a x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∫ x, ‖(u.permutation p).gradient s a x‖^2 := by
    rw [integral_congr_ae (h s a), integral_const_mul,
      integral_finsetSum _ (fun p _ => ((u.permutation p).partial_L2 s a).norm.integrable_sq)]
  have hf : (∑ s, ∑ a, ∫ x, ‖u.fullAntisymmetrize.gradient s a x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∑ s, ∑ a, ∫ x, ‖(u.permutation p).gradient s a x‖^2 := by
    simp_rw [hi, ← Finset.mul_sum]
    congr 1
    simp_rw [Finset.sum_comm (γ := Fin n × Fin 3)]
    rw [Finset.sum_comm]
  unfold kinetic
  rw [hf]
  calc
    _ = c*∑ p : Equiv.Perm (Fin n), kinetic (u.permutation p) := by
      simp only [kinetic, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring_nf
    _ = _ := by
      simp_rw [kinetic_permutation]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change c*((Fintype.card (Equiv.Perm (Fin n)) : ℝ)*kinetic u) = _
      unfold kinetic
      ring

lemma mass_scale {n : ℕ} (u : H1Vector n) (c : ℂ) :
    mass (u.scale c) = ‖c‖^2*mass u := by
  simp only [mass,H1Vector.scale,norm_mul,mul_pow,integral_const_mul,← Finset.mul_sum]
lemma kinetic_scale {n : ℕ} (u : H1Vector n) (c : ℂ) :
    kinetic (u.scale c) = ‖c‖^2*kinetic u := by
  simp only [kinetic,H1Vector.scale,norm_mul,mul_pow,integral_const_mul,← Finset.mul_sum]
  ring

def H1Vector.wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k) : H1Vector (m+k) :=
  (u.tensor v).fullAntisymmetrize.scale ((Real.sqrt (wedgeMultiplicity m k))⁻¹ : ℝ)

lemma kinetic_wedge {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v) (A B : Set Space)
    (hsu : SpatiallySupported u A) (hsv : SpatiallySupported v B)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    kinetic (u.wedge v) = kinetic u*mass v+mass u*kinetic v := by
  unfold H1Vector.wedge
  rw [kinetic_scale, wedge_normalizer_sq,
    kinetic_fullAntisymmetrize_of_sq (u.tensor v) _
      (separated_fullAntisymmetrize_gradient_sq u v hu hv A B hsu hsv hA hB hAB)]
  change (wedgeMultiplicity m k)⁻¹*(wedgeMultiplicity m k*kinetic (u.tensor v)) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (wedgeMultiplicity_pos m k)), one_mul, kinetic_tensor]

lemma potential_integrable_permutation {n : ℕ} (W : Configuration n → ℝ)
    (hW : ∀ p x, W (permute p x) = W x) (u : H1Vector n)
    (hi : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2))
    (p : Equiv.Perm (Fin n)) (s : Spins n) :
    Integrable (fun x => W x*‖(u.permutation p).value s x‖^2) := by
  have H := (permute_measurePreserving p).integrable_comp_of_integrable (hi (s ∘ p))
  simpa only [Function.comp_def, hW, permutation_value] using H

lemma potentialEnergy_fullAntisymmetrize_of_sq {n : ℕ} (u : H1Vector n) (c : ℝ)
    (W : Configuration n → ℝ) (hW : ∀ p x, W (permute p x) = W x)
    (hi : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2))
    (h : ∀ s, ∀ᵐ x ∂volume, ‖u.fullAntisymmetrize.value s x‖^2 =
      c*∑ p : Equiv.Perm (Fin n), ‖(u.permutation p).value s x‖^2) :
    potentialEnergy W u.fullAntisymmetrize =
      c*(Fintype.card (Equiv.Perm (Fin n)) : ℝ)*potentialEnergy W u := by
  have he (s : Spins n) : (∫ x, W x*‖u.fullAntisymmetrize.value s x‖^2) =
      c*∑ p : Equiv.Perm (Fin n), ∫ x, W x*‖(u.permutation p).value s x‖^2 := by
    rw [integral_congr_ae ((h s).mono (fun x hx => congrArg (W x*·) hx))]
    simp_rw [mul_left_comm (W _) c, Finset.mul_sum]
    rw [integral_finsetSum _
      (fun p _ => (potential_integrable_permutation W hW u hi p s).const_mul c)]
    simp only [integral_const_mul]
  unfold potentialEnergy
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  change c*(∑ p : Equiv.Perm (Fin n), potentialEnergy W (u.permutation p)) = _
  simp_rw [potentialEnergy_permutation W hW]
  simp [potentialEnergy, mul_assoc]

lemma potentialEnergy_scale {n : ℕ} (W : Configuration n → ℝ) (u : H1Vector n) (c : ℂ) :
    potentialEnergy W (u.scale c) = ‖c‖^2*potentialEnergy W u := by
  simp only [potentialEnergy,H1Vector.scale,norm_mul,mul_pow]
  simp_rw [mul_left_comm (W _) (‖c‖^2),integral_const_mul,← Finset.mul_sum]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Propagation_NuclearPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical

namespace Coulomb

lemma nuclearPotential_join {M m k : ℕ} (S : Nuclei M)
    (x : Configuration m) (y : Configuration k) :
    nuclearPotential S (joinConfiguration m k (x,y)) = nuclearPotential S x+nuclearPotential S y := by
  simp [nuclearPotential, Fin.sum_univ_add, position_join_left, position_join_right]

def crossPotential {m k : ℕ} (x : Configuration m) (y : Configuration k) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin k, coulombKernel (position x i-position y j)

lemma pairPotential_join {m k : ℕ} (x : Configuration m) (y : Configuration k) :
    pairPotential (joinConfiguration m k (x,y)) = pairPotential x+pairPotential y+crossPotential x y := by
  have hll (i j : Fin m) : Fin.castAdd k i < Fin.castAdd k j ↔ i < j := Iff.rfl
  have hlr (i : Fin m) (j : Fin k) : Fin.castAdd k i < Fin.natAdd m j := by
    change i.val < m+j.val
    omega
  have hrl (i : Fin k) (j : Fin m) : ¬Fin.natAdd m i < Fin.castAdd k j := by
    change ¬m+i.val < j.val
    omega
  simp only [pairPotential, Fin.sum_univ_add,position_join_left,position_join_right,
    hll,Fin.natAdd_lt_natAdd_iff,hlr,hrl,
    ite_true,ite_false,Finset.sum_const_zero,add_zero,Finset.sum_add_distrib]
  unfold crossPotential
  ring
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_LeftPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb
def leftPotential {m k : ℕ} (W : Configuration m → ℝ) (x : Configuration (m+k)) : ℝ :=
  W ((joinConfiguration m k).symm x).1
def rightPotential {m k : ℕ} (W : Configuration k → ℝ) (x : Configuration (m+k)) : ℝ :=
  W ((joinConfiguration m k).symm x).2

def crossEnergy {m k : ℕ} (u : H1Vector m) (v : H1Vector k) : ℝ :=
  potentialEnergy (fun x => crossPotential ((joinConfiguration m k).symm x).1
    ((joinConfiguration m k).symm x).2) (u.tensor v)

lemma tensor_leftPotential_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration m → ℝ) (hW : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2))
    (s : Spins (m+k)) :
    Integrable (fun x => leftPotential W x*‖(u.tensor v).value s x‖^2) := by
  have hp : Integrable (fun z : Configuration m × Configuration k =>
      (W z.1*‖u.value (s ∘ Fin.castAdd k) z.1‖^2)*‖v.value (s ∘ Fin.natAdd m) z.2‖^2)
      (volume.prod volume) :=
    (hW (s ∘ Fin.castAdd k)).mul_prod ((v.value_L2 (s ∘ Fin.natAdd m)).norm.integrable_sq)
  have H := (joinConfiguration_symm_measurePreserving m k).integrable_comp_of_integrable hp
  apply H.congr
  filter_upwards [] with x
  change (W _*‖u.value _ _‖^2)*‖v.value _ _‖^2 = W _*‖u.value _ _*v.value _ _‖^2
  rw [norm_mul,mul_pow,mul_assoc]
  rfl

lemma tensor_rightPotential_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration k → ℝ) (hW : ∀ s, Integrable (fun x => W x*‖v.value s x‖^2))
    (s : Spins (m+k)) :
    Integrable (fun x => rightPotential W x*‖(u.tensor v).value s x‖^2) := by
  have hp : Integrable (fun z : Configuration m × Configuration k =>
      ‖u.value (s ∘ Fin.castAdd k) z.1‖^2*(W z.2*‖v.value (s ∘ Fin.natAdd m) z.2‖^2))
      (volume.prod volume) :=
    ((u.value_L2 (s ∘ Fin.castAdd k)).norm.integrable_sq).mul_prod (hW (s ∘ Fin.natAdd m))
  have H := (joinConfiguration_symm_measurePreserving m k).integrable_comp_of_integrable hp
  apply H.congr
  filter_upwards [] with x
  change ‖u.value _ _‖^2*(W _*‖v.value _ _‖^2) = W _*‖u.value _ _*v.value _ _‖^2
  rw [norm_mul,mul_pow,mul_left_comm]
  rfl

lemma potentialEnergy_tensor_left {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration m → ℝ) :
    potentialEnergy (leftPotential W) (u.tensor v) = potentialEnergy W u*mass v := by
  have hi (s : Spins (m+k)) : (∫ x, leftPotential W x*‖(u.tensor v).value s x‖^2) =
      (∫ x, W x*‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, ‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
    rw [← (joinConfiguration_measurePreserving m k).integral_comp'
      (fun x => leftPotential W x*‖(u.tensor v).value s x‖^2)]
    change (∫ z : Configuration m × Configuration k,
      leftPotential W (joinConfiguration m k z)*‖tensorValue u v s (joinConfiguration m k z)‖^2
        ∂(volume.prod volume)) = _
    simp only [leftPotential, ContinuousLinearEquiv.symm_apply_apply, tensorValue_join,norm_mul,mul_pow,← mul_assoc]
    exact integral_prod_mul (μ := volume) (ν := volume)
      (fun x : Configuration m => W x*‖u.value (s ∘ Fin.castAdd k) x‖^2)
      (fun y : Configuration k => ‖v.value (s ∘ Fin.natAdd m) y‖^2)
  unfold potentialEnergy mass
  rw [sum_joinSpins]
  simp_rw [hi, joinSpins_left, joinSpins_right]
  rw [Finset.sum_mul_sum]

lemma potentialEnergy_tensor_right {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (W : Configuration k → ℝ) :
    potentialEnergy (rightPotential W) (u.tensor v) = mass u*potentialEnergy W v := by
  have hi (s : Spins (m+k)) : (∫ x, rightPotential W x*‖(u.tensor v).value s x‖^2) =
      (∫ x, ‖u.value (s ∘ Fin.castAdd k) x‖^2)*
        (∫ y, W y*‖v.value (s ∘ Fin.natAdd m) y‖^2) := by
    rw [← (joinConfiguration_measurePreserving m k).integral_comp'
      (fun x => rightPotential W x*‖(u.tensor v).value s x‖^2)]
    change (∫ z : Configuration m × Configuration k,
      rightPotential W (joinConfiguration m k z)*‖tensorValue u v s (joinConfiguration m k z)‖^2
        ∂(volume.prod volume)) = _
    simp only [rightPotential, ContinuousLinearEquiv.symm_apply_apply,tensorValue_join,norm_mul,mul_pow]
    simp_rw [mul_left_comm (W _) (‖u.value _ _‖^2)]
    exact integral_prod_mul (μ := volume) (ν := volume)
      (fun x : Configuration m => ‖u.value (s ∘ Fin.castAdd k) x‖^2)
      (fun y : Configuration k => W y*‖v.value (s ∘ Fin.natAdd m) y‖^2)
  unfold potentialEnergy mass
  rw [sum_joinSpins]
  simp_rw [hi, joinSpins_left, joinSpins_right]
  rw [Finset.sum_mul_sum]

lemma potentialEnergy_add {n : ℕ} (u : H1Vector n) (V W : Configuration n → ℝ)
    (hV : ∀ s, Integrable (fun x => V x*‖u.value s x‖^2))
    (hW : ∀ s, Integrable (fun x => W x*‖u.value s x‖^2)) :
    potentialEnergy (fun x => V x+W x) u = potentialEnergy V u+potentialEnergy W u := by
  simp only [potentialEnergy,add_mul]
  simp_rw [integral_add (hV _) (hW _)]
  rw [Finset.sum_add_distrib]

lemma nuclearPotential_split {M m k : ℕ} (S : Nuclei M) (x : Configuration (m+k)) :
    nuclearPotential S x = leftPotential (nuclearPotential S) x+
      rightPotential (nuclearPotential S) x := by
  have H := nuclearPotential_join S ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,leftPotential,rightPotential] using H

lemma pairPotential_split {m k : ℕ} (x : Configuration (m+k)) :
    pairPotential x = leftPotential pairPotential x+rightPotential pairPotential x+
      crossPotential ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2 := by
  have H := pairPotential_join ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2
  simpa only [Prod.mk.eta,ContinuousLinearEquiv.apply_symm_apply,leftPotential,rightPotential] using H

lemma nuclearEnergy_tensor {M m k : ℕ} (S : Nuclei M) (u : H1Vector m) (v : H1Vector k) :
    nuclearEnergy S (u.tensor v) = nuclearEnergy S u*mass v+mass u*nuclearEnergy S v := by
  change potentialEnergy (nuclearPotential S) (u.tensor v) = _
  rw [show (nuclearPotential S : Configuration (m+k) → ℝ) = fun x =>
      leftPotential (nuclearPotential S) x+rightPotential (nuclearPotential S) x
      from funext (nuclearPotential_split S)]
  have h1 : ∀ s, Integrable (fun x => leftPotential (nuclearPotential S) x*‖(u.tensor v).value s x‖^2) :=
    tensor_leftPotential_integrable u v (nuclearPotential S) (u.nuclear_integrable S)
  have h2 : ∀ s, Integrable (fun x => rightPotential (nuclearPotential S) x*‖(u.tensor v).value s x‖^2) :=
    tensor_rightPotential_integrable u v (nuclearPotential S) (v.nuclear_integrable S)
  rw [potentialEnergy_add _ _ _ h1 h2,
      potentialEnergy_tensor_left,potentialEnergy_tensor_right]
  rfl

lemma tensor_crossPotential_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins (m+k)) : Integrable (fun x =>
      crossPotential ((joinConfiguration m k).symm x).1 ((joinConfiguration m k).symm x).2 *
        ‖(u.tensor v).value s x‖^2) := by
  have H := ((u.tensor v).pair_integrable s).sub
    ((tensor_leftPotential_integrable u v pairPotential u.pair_integrable s).add
      (tensor_rightPotential_integrable u v pairPotential v.pair_integrable s))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  change _ = pairPotential x*_-(_+_)
  rw [pairPotential_split]
  ring

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_UnitNucleus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
namespace Coulomb

lemma crossPotential_nuclear {m k : ℕ} (x : Configuration m) (y : Configuration k) :
    crossPotential x y = ∑ i : Fin m, nuclearPotential (unitNucleus (position x i)) y := by
  simp only [crossPotential,nuclearPotential,attraction_unitNucleus]
  congr 1
  funext i
  congr 1
  funext j
  exact coulombKernel_sub_comm _ _

lemma crossPotential_spin_integral {m k : ℕ} (x : Configuration m) (v : H1Vector k) :
    (∑ t : Spins k, ∫ y, crossPotential x y*‖v.value t y‖^2) =
      ∑ i : Fin m, nuclearEnergy (unitNucleus (position x i)) v := by
  have h (t : Spins k) (i : Fin m) : Integrable (fun y =>
      nuclearPotential (unitNucleus (position x i)) y*‖v.value t y‖^2) :=
    v.nuclear_integrable (unitNucleus (position x i)) t
  simp only [crossPotential_nuclear,Finset.sum_mul]
  simp_rw [integral_finsetSum _ (fun i _ => h _ i)]
  exact Finset.sum_comm

lemma tensor_cross_prod_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins m) (t : Spins k) : Integrable
      (fun z : Configuration m × Configuration k =>
        crossPotential z.1 z.2*(‖u.value s z.1‖^2*‖v.value t z.2‖^2))
        (volume.prod volume) := by
  have H := (joinConfiguration_measurePreserving m k).integrable_comp_of_integrable
    (tensor_crossPotential_integrable u v (joinSpins m k (s,t)))
  apply H.congr
  filter_upwards [] with z
  change crossPotential ((joinConfiguration m k).symm (joinConfiguration m k z)).1
      ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
      ‖tensorValue u v (joinSpins m k (s,t)) (joinConfiguration m k z)‖^2 = _
  rw [ContinuousLinearEquiv.symm_apply_apply,tensorValue_join,joinSpins_left,joinSpins_right,norm_mul,mul_pow]

lemma cross_integral_core_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins m) (t : Spins k) : Integrable (fun x =>
      (∫ y, crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2) := by
  have H := (tensor_cross_prod_integrable u v s t).integral_prod_left
  apply H.congr
  filter_upwards [] with x
  have he (y : Configuration k) :
      crossPotential x y*(‖u.value s x‖^2*‖v.value t y‖^2) =
      (crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2 := by ring
  simp_rw [he, integral_mul_const]

lemma crossEnergy_iterated {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    crossEnergy u v = ∑ s : Spins m, ∑ t : Spins k,
      ∫ x, (∫ y, crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2 := by
  unfold crossEnergy potentialEnergy
  rw [sum_joinSpins]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  rw [← (joinConfiguration_measurePreserving m k).integral_comp']
  change (∫ z : Configuration m × Configuration k,
    crossPotential ((joinConfiguration m k).symm (joinConfiguration m k z)).1
      ((joinConfiguration m k).symm (joinConfiguration m k z)).2 *
      ‖tensorValue u v (joinSpins m k (s,t)) (joinConfiguration m k z)‖^2
        ∂(volume.prod volume)) = _
  simp only [ContinuousLinearEquiv.symm_apply_apply,tensorValue_join,joinSpins_left,joinSpins_right,
    norm_mul,mul_pow]
  rw [integral_prod _ (tensor_cross_prod_integrable u v s t)]
  apply integral_congr_ae
  filter_upwards [] with x
  have he (y : Configuration k) :
      crossPotential x y*(‖u.value s x‖^2*‖v.value t y‖^2) =
      (crossPotential x y*‖v.value t y‖^2)*‖u.value s x‖^2 := by ring
  simp_rw [he, integral_mul_const]

lemma cross_core_integrable {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (s : Spins m) : Integrable (fun x =>
      (∑ i : Fin m, nuclearEnergy (unitNucleus (position x i)) v)*‖u.value s x‖^2) := by
  simp_rw [← crossPotential_spin_integral,Finset.sum_mul]
  exact integrable_finsetSum _ (fun t _ => cross_integral_core_integrable u v s t)

lemma crossEnergy_core {m k : ℕ} (u : H1Vector m) (v : H1Vector k) :
    crossEnergy u v = ∑ s : Spins m,
      ∫ x, (∑ i : Fin m, nuclearEnergy (unitNucleus (position x i)) v)*‖u.value s x‖^2 := by
  rw [crossEnergy_iterated]
  apply Finset.sum_congr rfl
  intro s _
  rw [← integral_finsetSum _ (fun t _ => cross_integral_core_integrable u v s t)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Finset.sum_mul,crossPotential_spin_integral]

noncomputable def coreInteractionDensity {m : ℕ} (u : H1Vector m) (d : Space → ℝ) : ℝ :=
  ∑ s : Spins m, ∫ x, (∑ i : Fin m, ∫ z : Space,
    coulombKernel (z-position x i)*d z)*‖u.value s x‖^2

lemma bernoulli_core_cross_mean {ι : Type*} [Fintype ι] {m : ℕ}
    (u : H1Vector m) (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s))
    (ho : ∀ a b, (∑ s : Fin 2, ∫ x : Space, star (v a x s)*v b x s) =
      if a = b then (1:ℂ) else 0) (lam : ι → ℝ) :
    (∑ w : ι → Bool, bernoulliWeight lam w * crossEnergy u (selectedSlater v hv hC w)) =
      coreInteractionDensity u (finiteFermiDensity v lam) := by
  simp only [crossEnergy_core,Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold coreInteractionDensity
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun w _ =>
    (cross_core_integrable u (selectedSlater v hv hC w) s).const_mul (bernoulliWeight lam w))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [← mul_assoc,← Finset.sum_mul]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [bernoulli_slater_nuclear_mean _ v hv hC ho lam]
  simp only [attraction_unitNucleus]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CoreCoulombPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical

open scoped Classical
namespace Coulomb
lemma coreInteractionDensity_integrand_integrable {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) (s : Spins m) (i : Fin m) :
    Integrable (fun x => (∫ z, coulombKernel (z-position x i)*d z)*‖u.value s x‖^2) := by
  apply (u.coulomb_density_prod_integrable s i d hd).integral_prod_left.congr
  filter_upwards [] with x
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [coulombKernel_sub_comm z]
  ring

lemma coreInteractionDensity_eq {m : ℕ} (u : H1Vector m)
    (d : Space → ℝ) (hd : Integrable d) :
    coreInteractionDensity u d = ∫ z, coreCoulombPotential u z*d z := by
  rw [coreCoulombPotential_fubini u d hd]
  unfold coreInteractionDensity
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => coreInteractionDensity_integrand_integrable u d hd s i)]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [coulombKernel_sub_comm]

lemma finiteFermiDensity_integrable {ι : Type*} [Fintype ι]
    (v : ι → Space → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ (⊤ : ℕ∞) (fun x => v a x s))
    (hC : ∀ a s, HasCompactSupport (fun x => v a x s)) (lam : ι → ℝ) :
    Integrable (finiteFermiDensity v lam) := by
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro s _
  exact ((hv i s).continuous.memLp_of_hasCompactSupport (hC i s) (p := 2)).integrable_norm_pow (by norm_num)

lemma attraction_measurable {M : ℕ} (S : Nuclei M) : Measurable (attraction S) := by
  unfold attraction
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (coulombKernel_measurable.comp (measurable_id.sub measurable_const)))

end Coulomb

open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_HilbertBasisSumSqInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

lemma compactSpectralBasis_quadratic_hasSum (T : E →L[ℂ] E)
    (hc : IsCompactOperator T) (hT : T.IsSymmetric) (u : E) :
    HasSum (fun i : Σ z, eigenspaceBasisSet T z =>
      i.1.re * ‖inner ℂ (compactSpectralBasis T hc hT i) u‖^2)
      (inner ℂ u (T u)).re := by
  let b := compactSpectralBasis T hc hT
  have h := (((b.hasSum_repr u).mapL T).mapL (innerSL ℂ u)).mapL Complex.reCLM
  convert h using 1
  · ext i
    have hi : i.1 = (i.1.re : ℂ) := Complex.ext rfl (by
      simpa only [Complex.ofReal_im] using compactSpectralBasis_eigen_real T hc hT i)
    simp only [ContinuousLinearMap.map_smul, innerSL_apply_apply,
      HilbertBasis.repr_apply_apply, b, compactSpectralBasis_eigen,
      Complex.reCLM_apply]
    rw [hi, ← inner_conj_symm (u) (compactSpectralBasis T hc hT i)]
    simp only [smul_eq_mul, Complex.ofReal_re]
    rw [show inner ℂ (compactSpectralBasis T hc hT i) u *
        ((i.1.re : ℂ) * conj (inner ℂ (compactSpectralBasis T hc hT i) u)) =
        (i.1.re : ℂ) * (conj (inner ℂ (compactSpectralBasis T hc hT i) u) *
        inner ℂ (compactSpectralBasis T hc hT i) u) by ring]
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
    simp [-Complex.ofReal_pow]
  · rfl

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SumSwapNonnegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
namespace Coulomb
variable {X E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [SeparableSpace E] in
lemma frameOperator_spectral_image_quadratic_hasSum
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] F) (u : F) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ‖inner ℂ u (B (compactSpectralBasis (frameOperator μ v)
        (frameOperator_compact hv) (frameOperator_symmetric hv) i))‖^2)
      (inner ℂ u (frameOperator μ (fun x => B (v x)) u)).re := by
  have h := compactSpectralBasis_quadratic_hasSum (frameOperator μ v)
    (frameOperator_compact hv) (frameOperator_symmetric hv) (B.adjoint u)
  convert h using 1
  · ext i
    simp only [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  · have hB : MemLp (fun x => B (v x)) 2 μ := B.comp_memLp' hv
    rw [frameOperator_quadratic hB, frameOperator_quadratic hv]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ContinuousLinearMap.adjoint_inner_right]

omit [SeparableSpace E] in
lemma frameOperator_spectral_image_hasSum {ι : Type*} [Countable ι]
    {μ : Measure X} {v : X → E} (hv : MemLp v 2 μ)
    (B : E →L[ℂ] F) (c : HilbertBasis ι ℂ F) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i)‖^2) (∫ x, ‖B (v x)‖^2 ∂μ) := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let f : ι × (Σ z, eigenspaceBasisSet (frameOperator μ v) z) → ℝ := fun ji =>
    ji.2.1.re * ‖inner ℂ (c ji.1) (B (b ji.2))‖^2
  refine hasSum_swap_nonnegative (f := f)
      (r := fun j => (inner ℂ (c j) (frameOperator μ (fun x => B (v x)) (c j))).re) ?_ ?_ ?_ ?_
  · intro ji
    exact mul_nonneg (compactSpectralBasis_eigen_nonneg (frameOperator μ v)
      (frameOperator_compact hv) (frameOperator_positive hv) ji.2) (sq_nonneg _)
  · intro j
    exact frameOperator_spectral_image_quadratic_hasSum hv B (c j)
  · intro i
    exact (hilbertBasis_hasSum_sq_inner c (B (b i))).mul_left i.1.re
  · exact frameOperator_hasSum_diagonal (B.comp_memLp' hv) c
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2MeasureInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb

section
variable {Y : Type*} [MeasurableSpace Y]

lemma l2MeasureInclusion_norm_sq {ν η : Measure Y} (h : η ≤ ν) (u : Lp ℂ 2 ν) :
    ‖l2MeasureInclusion h u‖^2 = ∫ y, ‖u y‖^2 ∂η := by
  rw [l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [l2MeasureInclusion_coe h u] with y hy
  rw [hy]
end

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma frame_l2_submeasure_trace {μ : Measure X} {ν η : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] [SeparableSpace (Lp ℂ 2 η)]
    {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) (hη : η ≤ ν) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * (∫ y, ‖compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i y‖^2 ∂η))
      (∫ x, ∫ y, ‖v x y‖^2 ∂η ∂μ) := by
  let I := (exists_hilbertBasis ℂ (Lp ℂ 2 η)).choose
  let c : HilbertBasis I ℂ (Lp ℂ 2 η) := (exists_hilbertBasis ℂ (Lp ℂ 2 η)).choose_spec.choose
  let : Countable I := orthonormal_countable c.orthonormal
  have h := frameOperator_spectral_image_hasSum hv (l2MeasureInclusion hη) c
  simpa only [l2MeasureInclusion_norm_sq] using h
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_IntegrableTsumSummableNormIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {Y ι : Type*} [MeasurableSpace Y] [Countable ι]

lemma l2_weighted_density_integrable {ν : Measure Y} (u : ι → Lp ℂ 2 ν) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable (fun i => w i * ‖u i‖^2)) :
    Integrable (fun y => ∑' i, w i * ‖u i y‖^2) ν ∧
      ∀ᵐ y ∂ν, Summable (fun i => w i * ‖u i y‖^2) := by
  apply integrable_tsum_of_summable_norm_integral
  · intro i
    exact ((Lp.memLp (u i)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul _
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw _) (sq_nonneg _)),
      integral_const_mul, ← l2_norm_sq] using hs

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_L2WeightedDensitySetIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {Y ι : Type*} [MeasurableSpace Y] [Countable ι]
lemma l2_weighted_density_setIntegral {ν : Measure Y} (u : ι → Lp ℂ 2 ν) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable (fun i => w i * ‖u i‖^2)) (A : Set Y) :
    HasSum (fun i => w i * ∫ y in A, ‖u i y‖^2 ∂ν)
      (∫ y in A, ∑' i, w i * ‖u i y‖^2 ∂ν) := by
  have hi (i : ι) : Integrable (fun y => w i * ‖u i y‖^2) ν :=
    ((Lp.memLp (u i)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul (w i)
  have hp (i : ι) (y : Y) : 0 ≤ w i * ‖u i y‖^2 := mul_nonneg (hw i) (sq_nonneg _)
  have hn : Summable (fun i => ∫ y in A, ‖w i * ‖u i y‖^2‖ ∂ν) := by
    apply Summable.of_nonneg_of_le (fun index =>
      integral_nonneg (fun point => norm_nonneg (w index * ‖u index point‖^2)))
      (f := fun i => w i * ‖u i‖^2) _ hs
    intro i
    simp only [Real.norm_eq_abs, abs_of_nonneg (hp i _)]
    calc
      (∫ y in A, w i * ‖u i y‖^2 ∂ν) ≤ ∫ y, w i * ‖u i y‖^2 ∂ν :=
        setIntegral_le_integral (hi i) (Filter.Eventually.of_forall (hp i))
      _ = w i * ‖u i‖^2 := by rw [integral_const_mul, ← l2_norm_sq]
  have h := hasSum_integral_of_summable_integral_norm (fun i => (hi i).restrict) hn
  simpa only [integral_const_mul] using h
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FrameDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma frameDensity_integrable {μ : Measure X} {ν : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) :
    Integrable (frameDensity hv) ν := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  apply (l2_weighted_density_integrable b (fun i => i.1.re)
    (compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)) _).1
  simpa only [b.orthonormal.1, one_pow, mul_one] using (frameOperator_spectral_hasSum hv).summable

lemma frameDensity_eq_ae {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] [MeasurableSpace.CountablyGenerated Y]
    {v : X → Lp ℂ 2 ν} (hv : MemLp v 2 μ) (V : X → Y → ℂ)
    (hV : ∀ x, v x =ᵐ[ν] V x)
    (hI : Integrable (fun xy : X × Y => ‖V xy.1 xy.2‖^2) (μ.prod ν)) :
    frameDensity hv =ᵐ[ν] (fun y => ∫ x, ‖V x y‖^2 ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  have hsum : Summable (fun i => i.1.re * ‖b i‖^2) := by
    simpa only [b.orthonormal.1, one_pow, mul_one] using (frameOperator_spectral_hasSum hv).summable
  have hpos := compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (frameDensity_integrable hv)
    hI.integral_prod_right
  intro A hA _
  have h1 := l2_weighted_density_setIntegral b (fun i => i.1.re) hpos hsum A
  have h2 := frame_l2_submeasure_trace hv (Measure.restrict_le_self (s := A))
  have he := h1.unique h2
  change (∫ y in A, frameDensity hv y ∂ν) = ∫ x, ∫ y in A, ‖v x y‖^2 ∂ν ∂μ at he
  rw [he]
  have hre : (∫ x, ∫ y in A, ‖v x y‖^2 ∂ν ∂μ) =
      ∫ x, ∫ y in A, ‖V x y‖^2 ∂ν ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [(hV x).restrict] with y hy
    rw [hy]
  rw [hre]
  apply integral_integral_swap
  exact hI.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FrameImageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb

section
variable {X E Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]

omit [SeparableSpace E] in
lemma frame_spectral_l2image_hasSum {μ : Measure X} {ν : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i)‖^2)
      (∫ x, ‖B (v x)‖^2 ∂μ) := by
  let I := (exists_hilbertBasis ℂ (Lp ℂ 2 ν)).choose
  let c : HilbertBasis I ℂ (Lp ℂ 2 ν) := (exists_hilbertBasis ℂ (Lp ℂ 2 ν)).choose_spec.choose
  let : Countable I := orthonormal_countable c.orthonormal
  exact frameOperator_spectral_image_hasSum hv B c

omit [SeparableSpace E] in
lemma frame_spectral_l2image_submeasure_trace {μ : Measure X} {ν η : Measure Y}
    [SeparableSpace (Lp ℂ 2 η)] {v : X → E} (hv : MemLp v 2 μ)
    (B : E →L[ℂ] Lp ℂ 2 ν) (hη : η ≤ ν) :
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * (∫ y, ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
        (frameOperator_symmetric hv) i) y‖^2 ∂η))
      (∫ x, ∫ y, ‖B (v x) y‖^2 ∂η ∂μ) := by
  have h := frame_spectral_l2image_hasSum hv ((l2MeasureInclusion hη).comp B)
  simpa only [ContinuousLinearMap.comp_apply, l2MeasureInclusion_norm_sq] using h

noncomputable def frameImageDensity {μ : Measure X} {ν : Measure Y}
    {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) (y : Y) : ℝ :=
  ∑' i : Σ z, eigenspaceBasisSet (frameOperator μ v) z,
    i.1.re * ‖B (compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
      (frameOperator_symmetric hv) i) y‖^2

lemma frameImageDensity_integrable {μ : Measure X} {ν : Measure Y}
    [SeparableSpace (Lp ℂ 2 ν)] {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) :
    Integrable (frameImageDensity hv B) ν := by
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  exact (l2_weighted_density_integrable (fun i => B (b i)) (fun i => i.1.re)
    (compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv))
    (frame_spectral_l2image_hasSum hv B).summable).1

lemma frameImageDensity_eq_ae {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] [MeasurableSpace.CountablyGenerated Y]
    {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) (V : X → Y → ℂ)
    (hV : ∀ x, B (v x) =ᵐ[ν] V x)
    (hI : Integrable (fun xy : X × Y => ‖V xy.1 xy.2‖^2) (μ.prod ν)) :
    frameImageDensity hv B =ᵐ[ν] (fun y => ∫ x, ‖V x y‖^2 ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  have hsum := (frame_spectral_l2image_hasSum hv B).summable
  have hpos := compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (frameImageDensity_integrable hv B)
    hI.integral_prod_right
  intro A hA _
  have h1 := l2_weighted_density_setIntegral (fun i => B (b i)) (fun i => i.1.re) hpos hsum A
  have h2 := frame_spectral_l2image_submeasure_trace hv B (Measure.restrict_le_self (s := A))
  have he := h1.unique h2
  change (∫ y in A, frameImageDensity hv B y ∂ν) = ∫ x, ∫ y in A, ‖B (v x) y‖^2 ∂ν ∂μ at he
  rw [he]
  have hre : (∫ x, ∫ y in A, ‖B (v x) y‖^2 ∂ν ∂μ) =
      ∫ x, ∫ y in A, ‖V x y‖^2 ∂ν ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    apply integral_congr_ae
    filter_upwards [(hV x).restrict] with y hy
    rw [hy]
  rw [hre]
  apply integral_integral_swap
  exact hI.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
end

variable {X E Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]

lemma frameImage_weighted_trace {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] [MeasurableSpace.CountablyGenerated Y]
    {v : X → E} (hv : MemLp v 2 μ) (B : E →L[ℂ] Lp ℂ 2 ν) (V : X → Y → ℂ)
    (hV : ∀ x, B (v x) =ᵐ[ν] V x)
    (hI : Integrable (fun xy : X × Y => ‖V xy.1 xy.2‖^2) (μ.prod ν))
    (W : Y → ℝ) (hW : AEStronglyMeasurable W ν) (hWp : ∀ y, 0 ≤ W y)
    (hWI : Integrable (fun xy : X × Y => W xy.2 * ‖V xy.1 xy.2‖^2) (μ.prod ν)) :
    (∀ i : Σ z, eigenspaceBasisSet (frameOperator μ v) z, i.1.re ≠ 0 →
      Integrable (fun y => W y * ‖B (compactSpectralBasis (frameOperator μ v)
        (frameOperator_compact hv) (frameOperator_symmetric hv) i) y‖^2) ν) ∧
    HasSum (fun i : Σ z, eigenspaceBasisSet (frameOperator μ v) z =>
      i.1.re * ∫ y, W y * ‖B (compactSpectralBasis (frameOperator μ v)
        (frameOperator_compact hv) (frameOperator_symmetric hv) i) y‖^2 ∂ν)
      (∫ x, ∫ y, W y * ‖V x y‖^2 ∂ν ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  let b := compactSpectralBasis (frameOperator μ v) (frameOperator_compact hv)
    (frameOperator_symmetric hv)
  let : Countable (Σ z, eigenspaceBasisSet (frameOperator μ v) z) :=
    orthonormal_countable b.orthonormal
  have hpos := compactSpectralBasis_eigen_nonneg _ (frameOperator_compact hv) (frameOperator_positive hv)
  have hsum := (frame_spectral_l2image_hasSum hv B).summable
  have hae := frameImageDensity_eq_ae hv B V hV hI
  have ht : (fun y => W y * frameImageDensity hv B y) =ᵐ[ν]
      (fun y => ∫ x, W y * ‖V x y‖^2 ∂μ) := by
    filter_upwards [hae] with y hy
    rw [hy, integral_const_mul]
  have hint : Integrable (fun y => W y * frameImageDensity hv B y) ν :=
    hWI.integral_prod_right.congr ht.symm
  have hF (i : Σ z, eigenspaceBasisSet (frameOperator μ v) z) :
      AEStronglyMeasurable (fun y => i.1.re * ‖B (b i) y‖^2) ν :=
    ((Lp.aestronglyMeasurable (B (b i))).norm.pow 2).const_mul _
  have hp (i : Σ z, eigenspaceBasisSet (frameOperator μ v) z) (y : Y) :
      0 ≤ i.1.re * ‖B (b i) y‖^2 := mul_nonneg (hpos i) (sq_nonneg _)
  have hi := weighted_series_integrable_hasSum hF hp
    (l2_weighted_density_integrable (fun i => B (b i)) (fun i => i.1.re) hpos hsum).2 hW hWp hint
  constructor
  · intro i hi0
    have H := (hi.1 i).const_mul (i.1.re)⁻¹
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    dsimp only [b]
    field_simp
  · convert hi.2 using 1
    · funext i
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    · change (∫ x, ∫ y, W y * ‖V x y‖^2 ∂ν ∂μ) =
        ∫ y, W y * frameImageDensity hv B y ∂ν
      rw [integral_congr_ae ht]
      exact integral_integral_swap hWI
end Coulomb

open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_ModulatedRealDerivativeNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
namespace Coulomb
lemma modulated_real_derivative_norm (G : Space → ℝ) (hG : Differentiable ℝ G)
    (y p x a : Space) :
    ‖fderiv ℝ (fun z : Space => Complex.exp ((2*Real.pi*inner ℝ z p : ℝ)*Complex.I) *
      (G (z-y) : ℂ)) x a‖^2 =
      (2*Real.pi*inner ℝ a p)^2 * G (x-y)^2 + (fderiv ℝ G (x-y) a)^2 := by
  have hθ := ((Complex.ofRealCLM.hasFDerivAt.comp x
    (((innerSL ℝ).flip p).hasFDerivAt.const_mul (2*Real.pi)))).mul_const Complex.I
  have hq := Complex.ofRealCLM.hasFDerivAt.comp x
    ((hG (x-y)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y))
  have H := congrArg (fun L : Space →L[ℝ] ℂ => L a) (hθ.cexp.mul hq).fderiv
  have hd : fderiv ℝ (fun z : Space => Complex.exp ((2*Real.pi*inner ℝ z p : ℝ)*Complex.I) *
      (G (z-y) : ℂ)) x a =
      Complex.exp ((2*Real.pi*inner ℝ x p : ℝ)*Complex.I) *
        ((fderiv ℝ G (x-y) a : ℂ) + (2*Real.pi*inner ℝ a p*G (x-y) : ℝ)*Complex.I) := by
    calc
      _ = _ := H
      _ = _ := by
        simp only [add_apply, smul_apply,
          ContinuousLinearMap.comp_apply, Function.comp_apply, id_eq,
          ContinuousLinearMap.id_apply,
          Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply,
          smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
  rw [hd, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, sub_zero, Real.exp_zero, one_mul]
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NearCoulombFiveHalves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

noncomputable def nearCoulombFiveHalves (x : Space) : ℝ :=
  (Metric.ball (0:Space) 1).indicator (fun y => coulombKernel y^(5/2:ℝ)) x

lemma nearCoulombFiveHalves_integrable : Integrable nearCoulombFiveHalves := by
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 5/2) (by simp [Space]) (by norm_num [Space])
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (coulombKernel_nonneg x) _),one_mul]
    change (‖x‖⁻¹)^(5/2:ℝ) ≤ ‖x‖^(-(5/2:ℝ))
    rw [Real.inv_rpow (norm_nonneg x),Real.rpow_neg (norm_nonneg x)]
  · exact (coulombKernel_measurable.pow_const _).aestronglyMeasurable

lemma density_coulomb_integrand_bound (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (x y : Space) :
    coulombKernel (x-y)*ρ y ≤ nearCoulombFiveHalves (x-y) + ρ y^(5/3:ℝ) + ρ y := by
  by_cases h : x-y ∈ Metric.ball (0:Space) 1
  · rw [nearCoulombFiveHalves,Set.indicator_of_mem h]
    have HY := Real.young_inequality_of_nonneg (coulombKernel_nonneg (x-y)) (hp y)
      (show (5/2:ℝ).HolderConjugate (5/3:ℝ) from ⟨by norm_num,by norm_num,by norm_num⟩)
    have H1 := Real.rpow_nonneg (coulombKernel_nonneg (x-y)) (5/2:ℝ)
    have H2 := Real.rpow_nonneg (hp y) (5/3:ℝ)
    linarith [hp y]
  · rw [nearCoulombFiveHalves,Set.indicator_of_notMem h,zero_add]
    have hn : (1:ℝ) ≤ ‖x-y‖ := by simpa [Metric.mem_ball,dist_zero_right] using h
    have hk : coulombKernel (x-y) ≤ 1 := by simpa [coulombKernel] using inv_anti₀ (by norm_num : (0:ℝ)<1) hn
    have H := mul_le_mul_of_nonneg_right hk (hp y)
    linarith [Real.rpow_nonneg (hp y) (5/3:ℝ)]

lemma density_coulomb_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (x : Space) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) := by
  apply (((nearCoulombFiveHalves_integrable.comp_sub_left x).add ht).add hi).mono'
    (((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).mul hm).aestronglyMeasurable)
  filter_upwards [] with y
  change ‖coulombKernel (x-y)*ρ y‖ ≤ nearCoulombFiveHalves (x-y) + ρ y^(5/3:ℝ) + ρ y
  rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hp y))]
  exact density_coulomb_integrand_bound ρ hp x y

lemma density_coulomb_bound (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (ht : Integrable (fun x => ρ x^(5/3:ℝ))) (x : Space) :
    (∫ y, coulombKernel (x-y)*ρ y) ≤
      (∫ y, nearCoulombFiveHalves y) + (∫ y, ρ y^(5/3:ℝ)) + ∫ y, ρ y := by
  calc
    _ ≤ ∫ y, nearCoulombFiveHalves (x-y) + ρ y^(5/3:ℝ) + ρ y :=
      integral_mono (density_coulomb_integrable ρ hp hm hi ht x)
        (((nearCoulombFiveHalves_integrable.comp_sub_left x).add ht).add hi)
        (density_coulomb_integrand_bound ρ hp x)
    _ = _ := by
      have HA := integral_add ((nearCoulombFiveHalves_integrable.comp_sub_left x).add ht) hi
      have HB := integral_add (nearCoulombFiveHalves_integrable.comp_sub_left x) ht
      simp only [Pi.add_apply] at HA HB
      rw [HA,HB,integral_sub_left_eq_self]

lemma density_coulomb_pair_integrable (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) (ht : Integrable (fun x => ρ x^(5/3:ℝ))) :
    Integrable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) := by
  have hm' : Measurable (fun xy : Space × Space => coulombKernel (xy.1-xy.2)*(ρ xy.1*ρ xy.2)) :=
    (coulombKernel_measurable.comp (measurable_fst.sub measurable_snd)).mul
      ((hm.comp measurable_fst).mul (hm.comp measurable_snd))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with x
    apply ((density_coulomb_integrable ρ hp hm hi ht x).const_mul (ρ x)).congr
    filter_upwards [] with y
    ring
  · let C := (∫ y, nearCoulombFiveHalves y) + (∫ y, ρ y^(5/3:ℝ)) + ∫ y, ρ y
    apply (hi.mul_const C).mono' hm'.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    have he : (∫ y, ‖coulombKernel (x-y)*(ρ x*ρ y)‖) =
        ρ x*(∫ y, coulombKernel (x-y)*ρ y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (mul_nonneg (hp _) (hp _)))]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (density_coulomb_bound ρ hp hm hi ht x) (hp x)
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PhaseRegion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb

lemma integral_ball_norm_sq_three (r : ℝ) (hr : 0 ≤ r) :
    (∫ p : Space in ball 0 r, ‖p‖^2) = 4*Real.pi/5*r^5 := by
  have he : (fun p : Space => (ball 0 r).indicator (fun p => ‖p‖^2) p) =
      fun p : Space => (Iio r).indicator (fun t : ℝ => t^2) ‖p‖ := by
    ext p
    simp only [Set.indicator, mem_ball, dist_zero_right, mem_Iio]
  rw [← integral_indicator measurableSet_ball, he,
    integral_fun_norm_addHaar volume]
  simp only [Space, finrank_euclideanSpace_fin, Nat.reduceSub,
    nsmul_eq_mul, smul_eq_mul]
  have hf : (fun t : ℝ => t^2 * (Iio r).indicator (fun s : ℝ => s^2) t) =
      (Iio r).indicator (fun t : ℝ => t^4) := by
    ext t
    by_cases ht : t < r <;> simp [Set.indicator, ht]
    ring
  rw [hf, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by ext t; simp; tauto
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr,
    integral_pow, volume_real_ball_three 1 (by norm_num)]
  norm_num
  ring

lemma integrableOn_ball_norm_sq_three (r : ℝ) :
    IntegrableOn (fun p : Space => ‖p‖^2) (ball 0 r) := by
  exact (continuous_norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Space) r) |>.mono_set ball_subset_closedBall

lemma phaseMeasure_lintegral_momentum {R : Space → ℝ} (hR : Measurable R)
    (hRp : ∀ y, 0 ≤ R y) :
    (∫⁻ yp, ENNReal.ofReal (‖yp.2‖^2) ∂phaseMeasure R) =
      ∫⁻ y : Space, ENNReal.ofReal (4*Real.pi/5*R y^5) := by
  rw [phaseMeasure_lintegral hR _ (by fun_prop)]
  apply lintegral_congr
  intro y
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_ball_norm_sq_three (R y))
    (Filter.Eventually.of_forall (fun p => sq_nonneg _)), integral_ball_norm_sq_three _ (hRp y)]

lemma phaseMeasure_momentum_memLp {R : Space → ℝ} (hR : Measurable R)
    (hRp : ∀ y, 0 ≤ R y) (hI : Integrable (fun y => R y^5)) :
    MemLp (fun yp : Space × Space => yp.2) 2 (phaseMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun yp => sq_nonneg _)),
    phaseMeasure_lintegral_momentum hR hRp,
    ← ofReal_integral_eq_lintegral_ofReal (hI.const_mul (4*Real.pi/5))
      (Filter.Eventually.of_forall (fun y => mul_nonneg (by positivity) (pow_nonneg (hRp y) _)))]
  exact ENNReal.ofReal_lt_top

lemma phaseMeasure_real_momentum {R : Space → ℝ} (hR : Measurable R)
    (hRp : ∀ y, 0 ≤ R y) :
    (∫ yp, ‖yp.2‖^2 ∂phaseMeasure R) = 4*Real.pi/5 * ∫ y : Space, R y^5 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun yp => sq_nonneg _))
    (by fun_prop), phaseMeasure_lintegral_momentum hR hRp,
    ← integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun y => mul_nonneg (by positivity) (pow_nonneg (hRp y) _))) (by fun_prop), integral_const_mul]

lemma fermiRadius_fifth (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (y : Space) :
    fermiRadius ρ y ^ 5 = (3/(8*Real.pi))^(5/3 : ℝ) * ρ y^(5/3 : ℝ) := by
  rw [fermiRadius, ← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ y)), Real.mul_rpow (by positivity) (hρ y)]
  norm_num

lemma fermiMeasure_momentum_memLp (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hI : Integrable (fun y => ρ y^(5/3 : ℝ))) :
    MemLp (fun yp : Space × Space => yp.2) 2 (phaseMeasure (fermiRadius ρ)) := by
  apply phaseMeasure_momentum_memLp (fermiRadius_measurable ρ hm) (fermiRadius_nonneg ρ hρ)
  simp only [fermiRadius_fifth ρ hρ]
  exact hI.const_mul _
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketWindowed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
lemma packetAnalysis_integral (g h : 𝓢(Space,ℂ)) (y p : Space) :
    packetAnalysis g h y p = ∫ x : Space,
      Complex.exp ((-2*Real.pi*inner ℝ x p : ℝ)*Complex.I)*(conj (g (x-y))*h x) := by
  unfold packetAnalysis
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  simp only [packetWindowed_apply,smul_eq_mul]
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
lemma packetState_apply (g : 𝓢(Space,ℂ)) (y p x : Space) :
    packetState g y p x = Complex.exp ((2*Real.pi*inner ℝ x p : ℝ)*Complex.I)*g (x-y) := by
  let h := SchwartzMap.compSubConstCLM ℂ y g
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (-(innerₗ Space)) (⇑(𝓕 h : 𝓢(Space,ℂ))) (-p)) x
  have ht' : 𝓕⁻ (SchwartzMap.compSubConstCLM ℂ p (𝓕 h)) x =
      Real.fourierChar (inner ℝ p x) • 𝓕⁻ (𝓕 h) x := by
    have hh : ((𝓕 h : 𝓢(Space,ℂ)) ∘ fun v => v + -p) =
        (SchwartzMap.compSubConstCLM ℂ p (𝓕 h) : Space → ℂ) := by
      ext v
      simp [sub_eq_add_neg]
    rw [hh] at ht
    change 𝓕⁻ (⇑(SchwartzMap.compSubConstCLM ℂ p (𝓕 h))) x =
      Real.fourierChar (-inner ℝ (-p) x) • 𝓕⁻ (⇑(𝓕 h : 𝓢(Space,ℂ))) x at ht
    simp only [inner_neg_left,neg_neg] at ht
    simpa only [SchwartzMap.fourierInv_coe] using ht
  change 𝓕⁻ (SchwartzMap.compSubConstCLM ℂ p (𝓕 h)) x = _
  rw [ht',FourierTransform.fourierInv_fourier_eq]
  simp [h,Circle.smul_def,Real.fourierChar_apply,real_inner_comm]
lemma packetState_norm (g : 𝓢(Space,ℂ)) (y p x : Space) :
    ‖packetState g y p x‖ = ‖g (x-y)‖ := by
  rw [packetState_apply,norm_mul,Complex.norm_exp]
  simp
lemma packetState_integral_norm_sq (g : 𝓢(Space,ℂ)) (y p : Space) :
    (∫ x : Space,‖packetState g y p x‖^2) = ∫ x : Space,‖g x‖^2 := by
  simp only [packetState_norm]
  exact integral_sub_right_eq_self (fun x : Space => ‖g x‖^2) y
lemma packetState_inner (g h : 𝓢(Space,ℂ)) (y p : Space) :
    inner ℂ ((packetState g y p).toLp 2 volume) (h.toLp 2 volume) = packetAnalysis g h y p := by
  rw [SchwartzMap.inner_toL2_toL2_eq _ _ volume,packetAnalysis_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [packetState_apply,RCLike.inner_apply',starRingEnd_apply,map_mul,mul_assoc]
  congr 1
  change conj (Complex.exp _) = _
  rw [←Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  push_cast
  ring

lemma packetAnalysis_continuous (g h : 𝓢(Space,ℂ)) :
    Continuous (fun yp : Space × Space => packetAnalysis g h yp.1 yp.2) := by
  simp only [packetAnalysis_integral]
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hC := SchwartzMap.norm_le_seminorm ℝ g
  apply MeasureTheory.continuous_of_dominated
    (bound := fun x : Space => C * ‖h x‖)
  · intro yp
    exact (((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const).cexp.mul
      ((Complex.continuous_conj.comp (g.continuous.comp (continuous_id.sub continuous_const))).mul
        h.continuous)).aestronglyMeasurable
  · intro yp
    filter_upwards [] with x
    simp only [norm_mul, Complex.norm_exp]
    have he : ((-2*Real.pi*inner ℝ x yp.2 : ℝ)*Complex.I : ℂ).re = 0 := by simp
    rw [he, Real.exp_zero, one_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (hC (x-yp.1)) (norm_nonneg _)
  · exact h.integrable.norm.const_mul C
  · filter_upwards [] with x
    exact (((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_const.inner continuous_snd))).mul continuous_const).cexp.mul
      ((Complex.continuous_conj.comp (g.continuous.comp (continuous_const.sub continuous_fst))).mul
        continuous_const))
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_PacketStateL2Norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
lemma packetState_toL2_norm (g : 𝓢(Space,ℂ)) (y p : Space) :
    ‖(packetState g y p).toLp 2 volume‖ = ‖g.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp' (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp),
    SchwartzMap.norm_toLp' (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [packetState_integral_norm_sq]

lemma packetState_toL2_continuous (g : 𝓢(Space,ℂ)) :
    Continuous (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume) := by
  rw [continuous_iff_continuousAt]
  intro yp₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc : Continuous (fun yp : Space × Space =>
      ‖(packetState g yp.1 yp.2).toLp 2 volume -
        (packetState g yp₀.1 yp₀.2).toLp 2 volume‖^2) := by
    simp only [norm_sub_sq (𝕜 := ℂ), packetState_toL2_norm, packetState_inner]
    exact (continuous_const.sub (continuous_const.mul
      (Complex.continuous_re.comp (packetAnalysis_continuous g (packetState g yp₀.1 yp₀.2))))).add continuous_const
  have h := hc.sqrt.continuousAt (x := yp₀)
  simpa only [ContinuousAt, Real.sqrt_sq (norm_nonneg _), sub_self, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    Real.sqrt_zero] using h

lemma schwartz_toL2_norm_sq (g : 𝓢(Space,ℂ)) :
    ‖g.toLp 2 volume‖^2 = ∫ x : Space, ‖g x‖^2 := by
  have h := congrArg Complex.re (SchwartzMap.inner_toL2_toL2_eq g g volume)
  rw [inner_self_eq_norm_sq_to_K] at h
  change ((‖g.toLp 2 volume‖ : ℂ)^2).re = (∫ x : Space, inner ℂ (g x) (g x)).re at h
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at h
  rw [h]
  change RCLike.re (∫ x : Space, inner ℂ (g x) (g x)) = _
  rw [← integral_re]
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  · convert ((g.memLp 2 volume).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).ofReal using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]

lemma packetState_toL2_memLp (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    MemLp (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume) 2 μ :=
  MemLp.of_bound (packetState_toL2_continuous g).aestronglyMeasurable ‖g.toLp 2 volume‖
    (Filter.Eventually.of_forall fun yp => (packetState_toL2_norm g yp.1 yp.2).le)
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketStateJointSquareIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
lemma packetState_joint_square_integrable (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Integrable (fun z : (Space × Space) × Space => ‖packetState g z.1.1 z.1.2 z.2‖^2)
      (μ.prod volume) := by
  have hm : Continuous (fun z : (Space × Space) × Space => ‖packetState g z.1.1 z.1.2 z.2‖^2) := by
    simp only [packetState_norm]
    exact ((g.continuous.comp (continuous_snd.sub continuous_fst.fst)).norm.pow 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun yp => ?_), ?_⟩
  · exact ((packetState g yp.1 yp.2).memLp 2 volume).integrable_norm_pow (by norm_num)
  · simpa only [Real.norm_of_nonneg (sq_nonneg (_ : ℝ)), packetState_integral_norm_sq]
      using (integrable_const (∫ x : Space, ‖g x‖^2) : Integrable (fun _ : Space × Space => ∫ x : Space, ‖g x‖^2) μ)

lemma packetFrame_density (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    frameDensity (packetState_toL2_memLp g μ) =ᵐ[volume]
      (fun x : Space => ∫ yp : Space × Space, ‖g (x-yp.1)‖^2 ∂μ) := by
  have h := frameDensity_eq_ae (packetState_toL2_memLp g μ)
    (fun yp x => packetState g yp.1 yp.2 x)
    (fun yp => (packetState g yp.1 yp.2).coeFn_toLp 2 volume)
    (packetState_joint_square_integrable g μ)
  simpa only [packetState_norm] using h
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PacketFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
noncomputable def packetFrame (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  frameOperator μ (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume)

lemma packetFrame_positive (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    (packetFrame g μ).toLinearMap.IsPositive :=
  frameOperator_positive (packetState_toL2_memLp g μ)

lemma packetFrame_compact (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] : IsCompactOperator (packetFrame g μ) :=
  frameOperator_compact (packetState_toL2_memLp g μ)

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketSynthesisIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
namespace Coulomb

lemma compactPhase_finite (A : Set (Space × Space)) (K : Set Space) (hK : IsCompact K)
    (P : ℝ) (hAK : ∀ yp ∈ A, yp.1 ∈ K) (hAP : ∀ yp ∈ A, ‖yp.2‖ ≤ P) :
    IsFiniteMeasure ((volume : Measure (Space × Space)).restrict A) := by
  constructor
  rw [Measure.restrict_apply_univ]
  have hs : A ⊆ K ×ˢ closedBall 0 P := by
    intro yp hy
    exact ⟨hAK yp hy, by simpa only [mem_closedBall, dist_zero_right] using hAP yp hy⟩
  exact (measure_mono hs).trans_lt ((hK.prod (isCompact_closedBall (0 : Space) P)).measure_lt_top)

open scoped Pointwise
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
namespace Coulomb
abbrev packetIndex (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) :=
  Σ z, eigenspaceBasisSet (packetFrame g μ) z

def packetBasis (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HilbertBasis (packetIndex g μ) ℂ (Lp ℂ 2 (volume : Measure Space)) :=
  compactSpectralBasis (packetFrame g μ) (packetFrame_compact g μ)
    (frameOperator_symmetric (packetState_toL2_memLp g μ))

abbrev positivePacketIndex (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) :=
  {i : packetIndex g μ // 0 < i.1.re}

lemma spinOrbital_kinetic {ι : Type*} (F : ι → Space → ℂ) (i : ι × Fin 2) :
    (∑ s : Fin 2, ∑ b : Fin 3, ∫ x : Space,
      ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2) =
    ∑ b : Fin 3, ∫ x : Space, ‖fderiv ℝ (F i.1) x (EuclideanSpace.single b 1)‖^2 := by
  have he (s : Fin 2) : (∑ b : Fin 3, ∫ x : Space,
      ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2) =
      if s = i.2 then ∑ b : Fin 3, ∫ x : Space,
        ‖fderiv ℝ (F i.1) x (EuclideanSpace.single b 1)‖^2 else 0 := by
    by_cases h : s = i.2 <;> simp [spinOrbital,h]
  simp only [he]
  simp
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SchwartzFourierDerivativeNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
namespace Coulomb
lemma schwartz_fourier_derivative_norm (g : 𝓢(Space,ℂ)) (a ξ : Space) :
    ‖(𝓕 (∂_{a} g) : 𝓢(Space,ℂ)) ξ‖^2 =
      (2*Real.pi*inner ℝ ξ a)^2 * ‖(𝓕 g : 𝓢(Space,ℂ)) ξ‖^2 := by
  have ht : (fun ξ : Space => inner ℝ ξ a).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht]
  change ‖(2 * Real.pi * Complex.I) * ((inner ℝ ξ a : ℂ) * (𝓕 g : 𝓢(Space,ℂ)) ξ)‖^2 = _
  rw [← mul_assoc]
  exact fourierMultiplier_norm_sq _ _

lemma schwartz_fourier_weighted_integrable (g : 𝓢(Space,ℂ)) (a : Space) :
    Integrable (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2 * ‖(𝓕 g : 𝓢(Space,ℂ)) ξ‖^2) := by
  simp_rw [← schwartz_fourier_derivative_norm]
  exact ((𝓕 (∂_{a} g) : 𝓢(Space,ℂ)).memLp 2 volume).integrable_norm_pow (by norm_num)

lemma schwartz_fourier_weighted_integral (g : 𝓢(Space,ℂ)) (a : Space) :
    (∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 * ‖(𝓕 g : 𝓢(Space,ℂ)) ξ‖^2) =
      ∫ x : Space, ‖fderiv ℝ g x a‖^2 := by
  simp_rw [← schwartz_fourier_derivative_norm]
  rw [← schwartz_toL2_norm_sq, SchwartzMap.norm_fourier_toL2_eq, schwartz_toL2_norm_sq]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]

lemma packetState_fourier_apply (g : 𝓢(Space,ℂ)) (y p ξ : Space) :
    (𝓕 (packetState g y p) : 𝓢(Space,ℂ)) ξ =
      Complex.exp ((-2*Real.pi*inner ℝ y (ξ-p) : ℝ)*Complex.I) * (𝓕 g : 𝓢(Space,ℂ)) (ξ-p) := by
  rw [packetState, FourierTransform.fourier_fourierInv_eq]
  change (𝓕 (SchwartzMap.compSubConstCLM ℂ y g) : 𝓢(Space,ℂ)) (ξ-p) = _
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ Space) (⇑g) (-y)) (ξ-p)
  have hh : (⇑g ∘ fun v => v + -y) = (SchwartzMap.compSubConstCLM ℂ y g : Space → ℂ) := by
    ext v; simp [sub_eq_add_neg]
  rw [hh] at ht
  change 𝓕 (⇑(SchwartzMap.compSubConstCLM ℂ y g)) (ξ-p) =
    Real.fourierChar (inner ℝ (-y) (ξ-p)) • 𝓕 (⇑g) (ξ-p) at ht
  simpa [SchwartzMap.fourier_coe, Circle.smul_def, Real.fourierChar_apply, inner_neg_left,
    neg_mul, mul_neg] using ht

lemma packetState_fourier_joint_continuous (g : 𝓢(Space,ℂ)) :
    Continuous (fun z : (Space × Space) × Space =>
      (𝓕 (packetState g z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2) := by
  simp only [packetState_fourier_apply]
  fun_prop
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_ComplexWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
namespace Coulomb

lemma packetState_real_derivative_norm (g : 𝓢(Space,ℝ)) (y p x a : Space) :
    ‖fderiv ℝ (packetState (complexWindow g) y p) x a‖^2 =
      (2*Real.pi*inner ℝ a p)^2 * g (x-y)^2 + (fderiv ℝ g (x-y) a)^2 := by
  have he : (packetState (complexWindow g) y p : Space → ℂ) =
      fun z => Complex.exp ((2*Real.pi*inner ℝ z p : ℝ)*Complex.I) * (g (z-y) : ℂ) := by
    ext z; rw [packetState_apply, complexWindow_apply]
  rw [he]
  exact modulated_real_derivative_norm g g.differentiable y p x a

lemma real_schwartz_derivative_square_integrable (g : 𝓢(Space,ℝ)) (a : Space) :
    Integrable (fun x : Space => (fderiv ℝ g x a)^2) := by
  have h := ((∂_{a} g : 𝓢(Space,ℝ)).memLp 2 volume).integrable_norm_pow (by norm_num)
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, Real.norm_eq_abs, sq_abs] using h

lemma packetState_real_kinetic_integral (g : 𝓢(Space,ℝ)) (y p a : Space) :
    (∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
      ‖(𝓕 (packetState (complexWindow g) y p) : 𝓢(Space,ℂ)) ξ‖^2) =
      (2*Real.pi*inner ℝ a p)^2 * (∫ x : Space, g x^2) +
        ∫ x : Space, (fderiv ℝ g x a)^2 := by
  rw [schwartz_fourier_weighted_integral]
  simp only [packetState_real_derivative_norm]
  have hG : Integrable (fun x : Space => g x^2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using (g.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hD := real_schwartz_derivative_square_integrable g a
  rw [integral_add ((hG.comp_sub_right y).const_mul _) (hD.comp_sub_right y),
    integral_const_mul, integral_sub_right_eq_self (fun x : Space => g x^2) y,
    integral_sub_right_eq_self (fun x : Space => (fderiv ℝ g x a)^2) y]

lemma packetState_fourier_joint_square_integrable (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Integrable (fun z : (Space × Space) × Space =>
      ‖(𝓕 (packetState g z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2‖^2) (μ.prod volume) := by
  have hm := (packetState_fourier_joint_continuous g).norm.pow 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun yp =>
    ((𝓕 (packetState g yp.1 yp.2) : 𝓢(Space,ℂ)).memLp 2 volume).integrable_norm_pow (by norm_num)), ?_⟩
  have he (yp : Space × Space) :
      (∫ ξ : Space, ‖(𝓕 (packetState g yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2) =
        ∫ x : Space, ‖g x‖^2 := by
    rw [← schwartz_toL2_norm_sq, SchwartzMap.norm_fourier_toL2_eq, schwartz_toL2_norm_sq,
      packetState_integral_norm_sq]
  change Integrable (fun yp : Space × Space =>
    ∫ ξ : Space, ‖‖(𝓕 (packetState g yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2‖) μ
  simpa only [Real.norm_of_nonneg (sq_nonneg (_ : ℝ)), he] using
    (integrable_const (∫ x : Space, ‖g x‖^2) : Integrable (fun _ : Space × Space => ∫ x : Space, ‖g x‖^2) μ)

lemma packetState_real_weighted_joint_integrable (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space) :
    Integrable (fun z : (Space × Space) × Space => (2*Real.pi*inner ℝ z.2 a)^2 *
      ‖(𝓕 (packetState (complexWindow g) z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2‖^2) (μ.prod volume) := by
  have hm : Continuous (fun z : (Space × Space) × Space => (2*Real.pi*inner ℝ z.2 a)^2 *
      ‖(𝓕 (packetState (complexWindow g) z.1.1 z.1.2) : 𝓢(Space,ℂ)) z.2‖^2) := by
    have hc : Continuous (fun z : (Space × Space) × Space => (2*Real.pi*inner ℝ z.2 a)^2) := by fun_prop
    exact hc.mul ((packetState_fourier_joint_continuous _).norm.pow 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  have hi (yp : Space × Space) : Integrable (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2 *
      ‖(𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2) :=
    schwartz_fourier_weighted_integrable (packetState (complexWindow g) yp.1 yp.2) a
  refine ⟨Filter.Eventually.of_forall hi, ?_⟩
  change Integrable (fun yp : Space × Space => ∫ ξ : Space, ‖(2*Real.pi*inner ℝ ξ a)^2 *
    ‖(𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ‖^2‖) μ
  simp only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg (_ : ℝ)) (sq_nonneg (_ : ℝ))),
    packetState_real_kinetic_integral]
  have hpa := hp.continuousLinearMap_comp ((2*Real.pi) • (innerSL ℝ a))
  have hi : Integrable (fun yp : Space × Space => (2*Real.pi*inner ℝ a yp.2)^2) μ := by
    simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      Function.comp_apply, Real.norm_eq_abs, sq_abs] using hpa.integrable_norm_pow (by norm_num)
  exact (hi.mul_const _).add (integrable_const _)
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SpaceFourierL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
namespace Coulomb
noncomputable def spaceFourierL2 : Lp ℂ 2 (volume : Measure Space) →L[ℂ]
    Lp ℂ 2 (volume : Measure Space) :=
  (Lp.fourierTransformₗᵢ Space ℂ).toContinuousLinearEquiv.toContinuousLinearMap

lemma spaceFourierL2_apply (u : Lp ℂ 2 (volume : Measure Space)) :
    spaceFourierL2 u = 𝓕 u := rfl

lemma packetFrame_fourier_weighted_trace (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space) :
    let hv := packetState_toL2_memLp (complexWindow g) μ
    let b := compactSpectralBasis (packetFrame (complexWindow g) μ)
      (packetFrame_compact (complexWindow g) μ) (frameOperator_symmetric hv)
    (∀ i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z,
      i.1.re ≠ 0 → Integrable (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)) ∧
    HasSum (fun i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z =>
      i.1.re * ∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)
      (∫ yp : Space × Space, (2*Real.pi*inner ℝ a yp.2)^2 * (∫ x : Space, g x^2) +
        (∫ x : Space, (fderiv ℝ g x a)^2) ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  dsimp only
  have hV (yp : Space × Space) :
      spaceFourierL2 ((packetState (complexWindow g) yp.1 yp.2).toLp 2) =ᵐ[volume]
      fun ξ => (𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ := by
    rw [spaceFourierL2_apply, SchwartzMap.toLp_fourier_eq]
    exact SchwartzMap.coeFn_toLp _ 2 volume
  have h := frameImage_weighted_trace (packetState_toL2_memLp (complexWindow g) μ)
    spaceFourierL2 (fun yp ξ => (𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ)
    hV (packetState_fourier_joint_square_integrable (complexWindow g) μ)
    (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2) (by fun_prop) (fun ξ => sq_nonneg _)
    (packetState_real_weighted_joint_integrable g μ hp a)
  constructor
  · exact h.1
  · convert h.2 using 1
    all_goals try with_reducible_and_instances rfl
    all_goals first | rfl | (simp only [packetState_real_kinetic_integral])

lemma packetFrame_positive_eigen_weakDerivative (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space)
    (i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z) (hi : i.1.re ≠ 0) :
    let hv := packetState_toL2_memLp (complexWindow g) μ
    let b := compactSpectralBasis (packetFrame (complexWindow g) μ)
      (packetFrame_compact (complexWindow g) μ) (frameOperator_symmetric hv)
    ∃ d : Lp ℂ 2 (volume : Measure Space),
      (∀ φ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x : Space, (fderiv ℝ φ x a : ℂ) * b i x) =
          -(∫ x : Space, (φ x : ℂ) * d x)) ∧
      ‖d‖^2 = ∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2 := by
  dsimp only
  exact l2_fourier_weighted_derivative _ a
    ((packetFrame_fourier_weighted_trace g μ hp a).1 i hi)
end Coulomb

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ThomasFermiKineticConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb

lemma fermi_kinetic_coefficient :
    (2*Real.pi)^2 * (4*Real.pi/5) * (3/(8*Real.pi))^(5/3:ℝ) =
      thomasFermiKineticConstant := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hA : 0 < 3/(8*Real.pi) := by positivity
  have hpow : (3/(8*Real.pi))^(5/3:ℝ) =
      (3/(8*Real.pi)) * (3/(8*Real.pi))^(2/3:ℝ) := by
    rw [show (5/3:ℝ) = 1+2/3 by norm_num, Real.rpow_add hA, Real.rpow_one]
  have hphase : (2*Real.pi)^2 * (3/(8*Real.pi))^(2/3:ℝ) =
      (3*Real.pi^2)^(2/3:ℝ) := by
    have he : ((2*Real.pi)^3)^(2/3:ℝ) = (2*Real.pi)^2 := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      norm_num
    rw [← he, ← Real.mul_rpow (by positivity) hA.le]
    congr 1
    field_simp
    ring
  rw [hpow]
  calc
    _ = (3/10:ℝ)*((2*Real.pi)^2 * (3/(8*Real.pi))^(2/3:ℝ)) := by field_simp; ring
    _ = thomasFermiKineticConstant := by rw [hphase]; rfl

lemma fermiMeasure_kinetic (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) :
    (2*Real.pi)^2 * (∫ yp, ‖yp.2‖^2 ∂phaseMeasure (fermiRadius ρ)) =
      thomasFermiKineticConstant * ∫ y : Space, ρ y^(5/3:ℝ) := by
  rw [phaseMeasure_real_momentum (fermiRadius_measurable ρ hm) (fermiRadius_nonneg ρ hρ)]
  simp only [fermiRadius_fifth ρ hρ, integral_const_mul]
  rw [← mul_assoc, ← mul_assoc, fermi_kinetic_coefficient]
end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_FermiPacketSpectralTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
namespace Coulomb

lemma fermiPacket_density (g : 𝓢(Space,ℝ))
    (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hI : Integrable ρ) :
    let μ := phaseMeasure (fermiRadius ρ)
    letI := fermiMeasure_finite ρ hρ hm hI
    (fun x : Space => 2 * frameDensity (packetState_toL2_memLp (complexWindow g) μ) x) =ᵐ[volume]
      (fun x : Space => ∫ y : Space, g (x-y)^2 * ρ y) := by
  dsimp only
  let := fermiMeasure_finite ρ hρ hm hI
  filter_upwards [packetFrame_density (complexWindow g) (phaseMeasure (fermiRadius ρ))] with x hx
  rw [hx]
  simp only [complexWindow_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [fermiMeasure_center_integral ρ hρ hm (fun y => g (x-y)^2) (by fun_prop) (fun y => sq_nonneg _)]
  ring

lemma packet_momentum_basis_sum (p : Space) :
    (∑ d : Fin 3, (2*Real.pi*inner ℝ (EuclideanSpace.single d 1) p)^2) =
      (2*Real.pi)^2*‖p‖^2 := by
  simp only [EuclideanSpace.inner_single_left, conj_trivial, one_mul, mul_pow]
  rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]

lemma fermiPacket_kinetic_trace (g : 𝓢(Space,ℝ))
    (hg : (∫ x : Space, g x^2) = 1) (ρ : Space → ℝ) (hρ : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hI : Integrable ρ) (hT : Integrable (fun y => ρ y^(5/3:ℝ))) :
    let μ := phaseMeasure (fermiRadius ρ)
    letI := fermiMeasure_finite ρ hρ hm hI
    let hv := packetState_toL2_memLp (complexWindow g) μ
    let b := compactSpectralBasis (packetFrame (complexWindow g) μ)
      (packetFrame_compact (complexWindow g) μ) (frameOperator_symmetric hv)
    HasSum (fun i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z =>
      i.1.re * ∑ d : Fin 3, ∫ ξ : Space, (2*Real.pi*inner ℝ ξ (EuclideanSpace.single d 1))^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)
      (thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y) *
          ∑ d : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single d 1))^2) := by
  dsimp only
  let μ := phaseMeasure (fermiRadius ρ)
  let := fermiMeasure_finite ρ hρ hm hI
  have hp := fermiMeasure_momentum_memLp ρ hρ hm hT
  have hs := hasSum_sum (s := (Finset.univ : Finset (Fin 3)))
    (fun d _ => (packetFrame_fourier_weighted_trace g μ hp (EuclideanSpace.single d 1)).2)
  simp only [← Finset.mul_sum, hg, mul_one] at hs
  have hi (d : Fin 3) : Integrable (fun yp : Space × Space =>
      (2*Real.pi*inner ℝ (EuclideanSpace.single d 1) yp.2)^2) μ := by
    have ha := hp.continuousLinearMap_comp ((2*Real.pi) • innerSL ℝ (EuclideanSpace.single d 1))
    simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul,
      Function.comp_apply, Real.norm_eq_abs, sq_abs] using ha.integrable_norm_pow (by norm_num)
  have hmμ : μ.real univ = (∫ y : Space, ρ y)/2 := by
    rw [measureReal_def, fermiMeasure_mass ρ hρ hm hI,
      ENNReal.toReal_ofReal (div_nonneg (integral_nonneg hρ) (by norm_num))]
  have he : (∑ d : Fin 3, ∫ yp : Space × Space,
       (2*Real.pi*inner ℝ (EuclideanSpace.single d 1) yp.2)^2 +
         (∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single d 1))^2) ∂μ) =
      thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
        (1/2:ℝ)*(∫ y : Space, ρ y) *
          ∑ d : Fin 3, ∫ x : Space, (fderiv ℝ g x (EuclideanSpace.single d 1))^2 := by
    simp_rw [integral_add (hi _) (integrable_const _), integral_const, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← integral_finsetSum _ (fun d _ => hi d),
      ← Finset.mul_sum]
    simp only [packet_momentum_basis_sum, integral_const_mul]
    rw [fermiMeasure_kinetic ρ hρ hm, hmμ]
    ring
  rw [he] at hs
  exact hs
end Coulomb

open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_SumSpinDuplicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
namespace Coulomb

lemma packetBasis_eigen_nonneg (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space))
    [IsFiniteMeasure μ] (i : packetIndex g μ) : 0 ≤ i.1.re :=
  compactSpectralBasis_eigen_nonneg _ (packetFrame_compact g μ) (packetFrame_positive g μ) i

lemma packet_positive_hasSum {g : 𝓢(Space,ℂ)} {μ : Measure (Space × Space)}
    [IsFiniteMeasure μ] (f : packetIndex g μ → ℝ) {a : ℝ}
    (hs : HasSum (fun i => i.1.re*f i) a) :
    HasSum (fun i : positivePacketIndex g μ => i.val.1.re*f i.val) a := by
  apply (hasSum_subtype_iff_of_support_subset (s := {i : packetIndex g μ | 0 < i.1.re}) ?_).mpr hs
  intro i hi
  change 0 < i.1.re
  apply lt_of_le_of_ne (packetBasis_eigen_nonneg g μ i)
  intro he
  exact hi (by simp only [← he,zero_mul])

lemma packetPositive_directional_energy (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space)
    (i : positivePacketIndex (complexWindow g) μ) (F : Space → ℂ)
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (he : (packetBasis (complexWindow g) μ i.val : Space → ℂ) =ᵐ[volume] F) :
    (∫ x : Space, ‖fderiv ℝ F x a‖^2) =
      ∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (packetBasis (complexWindow g) μ i.val) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2 := by
  obtain ⟨d,hd,heD⟩ := packetFrame_positive_eigen_weakDerivative g μ hp a i.val (ne_of_gt i.property)
  exact (weak_directional_smooth_norm_sq a F hFs hFc he hd).trans heD

lemma fermiPacket_positive_kinetic (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (ρ : Space → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ) (hI : Integrable ρ)
    (hT : Integrable (fun x => ρ x^(5/3:ℝ))) :
    let μ := phaseMeasure (fermiRadius ρ)
    letI := fermiMeasure_finite ρ hρ hm hI
    ∀ (F : positivePacketIndex (complexWindow g) μ → Space → ℂ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) → (∀ i, HasCompactSupport (F i)) →
      (∀ i, (packetBasis (complexWindow g) μ i.val : Space → ℂ) =ᵐ[volume] F i) →
      HasSum (fun i : positivePacketIndex (complexWindow g) μ × Fin 2 =>
        i.1.val.1.re * ∑ s, ∑ b : Fin 3, ∫ x : Space,
          ‖fderiv ℝ (fun y => spinOrbital F i y s) x (EuclideanSpace.single b 1)‖^2)
        (2*(thomasFermiKineticConstant * (∫ y : Space, ρ y^(5/3:ℝ)) +
          (1/2:ℝ)*(∫ y : Space, ρ y)*∑ b : Fin 3, ∫ x : Space,
            (fderiv ℝ g x (EuclideanSpace.single b 1))^2)) := by
  dsimp only
  let := fermiMeasure_finite ρ hρ hm hI
  intro F hFs hFc he
  have hp := fermiMeasure_momentum_memLp ρ hρ hm hT
  have H := packet_positive_hasSum (g := complexWindow g) (μ := phaseMeasure (fermiRadius ρ))
    (fun i => ∑ b : Fin 3, ∫ ξ : Space, (2*Real.pi*inner ℝ ξ (EuclideanSpace.single b 1))^2 *
      ‖(𝓕 (packetBasis (complexWindow g) (phaseMeasure (fermiRadius ρ)) i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)
    (fermiPacket_kinetic_trace g hg ρ hρ hm hI hT)
  have hedir (i : positivePacketIndex (complexWindow g) (phaseMeasure (fermiRadius ρ))) :
      (∑ b : Fin 3, ∫ x : Space, ‖fderiv ℝ (F i) x (EuclideanSpace.single b 1)‖^2) =
      ∑ b : Fin 3, ∫ ξ : Space, (2*Real.pi*inner ℝ ξ (EuclideanSpace.single b 1))^2 *
        ‖(𝓕 (packetBasis (complexWindow g) (phaseMeasure (fermiRadius ρ)) i.val) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2 := by
    apply Finset.sum_congr rfl
    intro b _
    exact packetPositive_directional_energy g _ hp _ i (F i) (hFs i) (hFc i) (he i)
  simp_rw [← hedir] at H
  simpa only [spinOrbital_kinetic] using hasSum_spin_duplicate
    (fun i => mul_nonneg i.property.le (Finset.sum_nonneg (fun b _ => integral_nonneg (fun x => sq_nonneg _)))) H
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
namespace Coulomb

lemma packetDensity_nonneg (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y) (x : Space) :
    0 ≤ packetDensity g ρ x := integral_nonneg (fun y => mul_nonneg (sq_nonneg _) (hp y))

lemma packetDensity_measurable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hm : Measurable ρ) :
    Measurable (packetDensity g ρ) := by
  exact (((g.continuous.measurable.comp (measurable_fst.sub measurable_snd)).pow_const 2).mul
    (hm.comp measurable_snd)).stronglyMeasurable.integral_prod_right.measurable

lemma packetDensity_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) : Integrable (packetDensity g ρ) := by
  let := fermiMeasure_finite ρ hp hm hi
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  exact ((frameDensity_integrable (packetState_toL2_memLp (complexWindow g)
    (phaseMeasure (fermiRadius ρ)))).const_mul 2).congr (fermiPacket_density g ρ hp hm hi)

lemma packetDensity_integrand_integrable (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    Integrable (fun y => g (x-y)^2*ρ y) := by
  apply (hi.const_mul ((SchwartzMap.seminorm ℝ 0 0 g)^2)).mono'
    (((g.continuous.measurable.comp (measurable_const.sub measurable_id)).pow_const 2).mul hm).aestronglyMeasurable
  filter_upwards [] with y
  change ‖g (x-y)^2*ρ y‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hp y))]
  exact mul_le_mul_of_nonneg_right (schwartz_square_le g _) (hp y)

lemma packetDensity_bound (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) (x : Space) :
    packetDensity g ρ x ≤ (SchwartzMap.seminorm ℝ 0 0 g)^2 * ∫ y, ρ y := by
  calc
    _ ≤ ∫ y, (SchwartzMap.seminorm ℝ 0 0 g)^2*ρ y :=
      integral_mono (packetDensity_integrand_integrable g ρ hp hm hi x)
        (hi.const_mul _) (fun y => mul_le_mul_of_nonneg_right (schwartz_square_le g _) (hp y))
    _ = _ := integral_const_mul _ _

lemma complexWindow_tsupport (g : 𝓢(Space,ℝ)) :
    tsupport (complexWindow g : Space → ℂ) = tsupport (g : Space → ℝ) := by
  unfold tsupport
  congr 1
  ext x
  change (↑(g x) : ℂ) ≠ 0 ↔ g x ≠ 0
  exact not_congr Complex.ofReal_eq_zero

lemma complexWindow_compactSupport (g : 𝓢(Space,ℝ)) (hgc : HasCompactSupport (g : Space → ℝ)) :
    HasCompactSupport (complexWindow g : Space → ℂ) := by
  change IsCompact (tsupport (complexWindow g : Space → ℂ))
  rw [complexWindow_tsupport]
  exact hgc

lemma fermiPhase_center_mem (ρ : Space → ℝ) (K : Set Space) (hs : ∀ y, y ∉ K → ρ y = 0)
    (yp : Space × Space) (hyp : yp ∈ phaseRegion (fermiRadius ρ)) : yp.1 ∈ K := by
  by_contra hn
  have hzero : fermiRadius ρ yp.1 = 0 := by simp [fermiRadius,hs yp.1 hn]
  change ‖yp.2‖ < fermiRadius ρ yp.1 at hyp
  rw [hzero] at hyp
  exact (not_lt_of_ge (norm_nonneg _)) hyp

lemma fermiPhase_momentum_bound (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (C : ℝ) (hC : ∀ y, ρ y ≤ C) (yp : Space × Space) (hyp : yp ∈ phaseRegion (fermiRadius ρ)) :
    ‖yp.2‖ ≤ (3/(8*Real.pi)*C)^(1/3:ℝ) := by
  apply (le_of_lt hyp).trans
  exact Real.rpow_le_rpow (mul_nonneg (by positivity) (hp _))
    (mul_le_mul_of_nonneg_left (hC _) (by positivity)) (by norm_num)
end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_CoreScreenedField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
namespace Coulomb

lemma boundedDensity_nuclear_integrable {M : ℕ} (S : Nuclei M) (d : Space → ℝ)
    (hd : Integrable d) (hm : Measurable d) (hp : ∀ x, 0 ≤ d x)
    (C : ℝ) (hC : ∀ x, d x ≤ C) : Integrable (fun x => attraction S x*d x) := by
  simp only [attraction,Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  have H := (coulomb_convolution_integrable hd hm hp hC (by norm_num : (0:ℝ)<1) (S.position j)).const_mul (S.charge j)
  apply H.congr
  filter_upwards [] with x
  rw [coulombKernel_sub_comm (S.position j)]
  ring

lemma packetDensity_nuclear_integrable {M : ℕ} (S : Nuclei M)
    (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ y, 0 ≤ ρ y)
    (hm : Measurable ρ) (hi : Integrable ρ) :
    Integrable (fun x => attraction S x*packetDensity g ρ x) :=
  boundedDensity_nuclear_integrable S _ (packetDensity_integrable g ρ hp hm hi)
    (packetDensity_measurable g ρ hm) (packetDensity_nonneg g ρ hp) _
    (packetDensity_bound g ρ hp hm hi)

end Coulomb

open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_CoreScreenedFieldPacketIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
namespace Coulomb

lemma coreScreenedField_packet_integral {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    (g : 𝓢(Space,ℝ)) (ρ : Space → ℝ) (hp : ∀ x, 0 ≤ ρ x) (hm : Measurable ρ)
    (hi : Integrable ρ) :
    (∫ x, coreScreenedField S u x*packetDensity g ρ x) =
      (∫ x, attraction S x*packetDensity g ρ x) -
      (∫ x, coreCoulombPotential u x*packetDensity g ρ x) := by
  simp only [coreScreenedField,sub_mul]
  exact integral_sub (packetDensity_nuclear_integrable S g ρ hp hm hi)
    (coreCoulombPotential_mul_integrable u _ (packetDensity_integrable g ρ hp hm hi))

end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_WindowCoulomb
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace Convolution
open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal ComplexConjugate Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped Classical SchwartzMap FourierTransform ENNReal NNReal Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
open MeasureTheory Set Filter
open scoped ENNReal NNReal Classical SchwartzMap Pointwise
namespace Coulomb

lemma coreCoulombPotential_packet_eq {m : ℕ} (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsep : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖) :
    (∫ x, coreCoulombPotential u x*packetDensity g ρ x) = ∫ x, coreCoulombPotential u x*ρ x := by
  rw [coreCoulombPotential_fubini u _ (packetDensity_integrable g ρ hp hm hi),
    coreCoulombPotential_fubini u ρ hi]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hu s] with x hx
  by_cases he : u.value s x = 0
  · simp [he]
  · have ha : position x i ∈ A := (by_contra (fun hn => he (hx hn)) : x ∈ allPositions A) i
    change (∫ z, coulombKernel (position x i-z)*packetDensity g ρ z)*‖u.value s x‖^2 = _
    rw [packetDensity_coulomb_eq g hg hrad hR hs ρ hp hm hi (position x i) (hsep _ ha)]

lemma separated_density_nuclear_integrable {M : ℕ} (S : Nuclei M) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    {R : ℝ} (hR : 0 < R)
    (hsep : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    Integrable (fun x => attraction S x*ρ x) := by
  simp only [attraction,Finset.sum_mul]
  apply integrable_finsetSum
  intro j _
  have h := (separated_density_coulomb_integrable hp hm hi hR (S.position j) (hsep j)).const_mul (S.charge j)
  apply h.congr
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [coulombKernel_sub_comm x]
    ring

lemma coreScreenedField_packet_eq {M m : ℕ} (S : Nuclei M) (u : H1Vector m)
    {A : Set Space} (hu : SpatiallySupported u A)
    (g : 𝓢(Space,ℝ)) (hg : (∫ x : Space, g x^2) = 1)
    (hrad : ∀ y, g y = g (EuclideanSpace.single 0 ‖y‖)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ y, R < ‖y‖ → g y = 0) (ρ : Space → ℝ)
    (hp : ∀ y, 0 ≤ ρ y) (hm : Measurable ρ) (hi : Integrable ρ)
    (hsep : ∀ a ∈ A, ∀ y, ρ y ≠ 0 → R ≤ ‖a-y‖)
    (hnuc : ∀ j y, ρ y ≠ 0 → R ≤ ‖S.position j-y‖) :
    (∫ x, coreScreenedField S u x*packetDensity g ρ x) = ∫ x, coreScreenedField S u x*ρ x := by
  rw [coreScreenedField_packet_integral S u g ρ hp hm hi,
    coreCoulombPotential_packet_eq u hu g hg hrad hR hs ρ hp hm hi hsep,
    attraction_packet_eq S g hg hrad hR hs ρ hp hm hi hnuc]
  simp only [coreScreenedField,sub_mul]
  exact (integral_sub (separated_density_nuclear_integrable S ρ hp hm hi hR hnuc)
    (coreCoulombPotential_mul_integrable u ρ hi)).symm

end Coulomb

open MeasureTheory Set
open scoped BigOperators ENNReal

end

end OAI
end


