-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousCoeffSub
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_ContinuousCoeffSub
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:40.328805+00:00
-- url     : https://prove2.me/theorems/3ce298ea-c8b8-4b15-8888-3e28b3f5bbd5
-- title:
--   Continuous Coeff Sub
-- statement:
--   Definitions and structural lemmas for Continuous Coeff Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/ContinuousCoeffSub.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TotalDegreeLinear
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
namespace PositivityTheory.Rg.Sw.FFTSteps
namespace AvgPf
section
variable {ι A B : Type} [Fintype ι]
def actP (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))
end
abbrev εT (N : ℕ) : Fin N → Bool := fun _ => true
theorem isEmbedding_toMK (N : ℕ) : Topology.IsEmbedding (fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k) :=
  (Formalism.REAL.isClosedEmbeddingMatrix N (εT N)).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
instance instSCKG (N : ℕ) : SecondCountableTopology (Formalism.REAL.KG (εT N)) := by
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  exact (isEmbedding_toMK N).isInducing.secondCountableTopology
theorem muK_univ (N : ℕ) : Formalism.REAL.muK (εT N) Set.univ = 1 := by
  have := Measure.haarMeasure_self (G := Formalism.REAL.KG (εT N)) (K₀ := ⊤)
  rw [TopologicalSpace.PositiveCompacts.coe_top] at this
  exact this
theorem map_mul_right_muK (N : ℕ) (g : Formalism.REAL.KG (εT N)) :
    Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N)) = Formalism.REAL.muK (εT N) := by
  have : (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))).IsHaarMeasure :=
    Measure.isHaarMeasure_map_mul_right (Formalism.REAL.muK (εT N)) g
  have h := Measure.haarMeasure_unique (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))) ⊤
  rw [h, TopologicalSpace.PositiveCompacts.coe_top, Measure.map_apply (measurable_mul_const g) MeasurableSet.univ,
    Set.preimage_univ, muK_univ, one_smul]
  rfl
instance (N : ℕ) : (Formalism.REAL.muK (εT N)).IsMulRightInvariant := ⟨fun g => map_mul_right_muK N g⟩
end AvgPf
end PositivityTheory.Rg.Sw.FFTSteps


