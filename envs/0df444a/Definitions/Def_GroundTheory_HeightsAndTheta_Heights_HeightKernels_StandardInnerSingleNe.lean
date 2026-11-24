-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:47.254618+00:00
-- url     : https://prove2.me/theorems/0284fc18-43e9-4b5a-9cee-d9ea4c8792ad
-- title:
--   Standard Inner Single Ne
-- statement:
--   Definitions and structural lemmas for Standard Inner Single Ne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StandardInnerSingleNe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section
def IsOrthogonalFamily {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K) {X : Type*}
    (L : X → Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (σ : K →+* ℂ) (x y : X), x ≠ y → ∀ l ∈ L x, ∀ l' ∈ L y,
    (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] l') = 0
def S6.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (X : Type) [Fintype X]
    [DecidableEq X] (L : X → Submodule (𝓞 K) E.carrier) (μ : ℝ),
    DirectSum.IsInternal L → (∀ x, E.rank (L x) = 1) → IsOrthogonalFamily E L →
    (∀ x, μ ≤ E.normDegree (L x)) →
    ∀ (E' E'' : HermitianBundle.{0} K), HermitianExtension E' E E'' →
      (E''.rank ⊤ : ℝ) * μ ≤ E''.normDegree ⊤
def coordLines (K : Type*) [Field K] : Fin 2 → Submodule (𝓞 K) (Fin 2 → 𝓞 K) :=
  fun x => LinearMap.range (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


