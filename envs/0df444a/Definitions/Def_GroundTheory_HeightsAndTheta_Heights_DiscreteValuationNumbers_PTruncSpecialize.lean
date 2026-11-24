-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTruncSpecialize
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTruncSpecialize
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:54.970659+00:00
-- url     : https://prove2.me/theorems/0f6fdb79-239b-4f2e-b30a-30762f3ef513
-- title:
--   PTrunc Specialize
-- statement:
--   Definitions and structural lemmas for PTrunc Specialize, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTruncSpecialize.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTruncSpecialize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
section Ring
variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E]
def projCoordRing {B : Type*} [CommRing B] [Algebra Ω B] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (u : Fin N → B) :
    (Σ o, bundleIdx ι M o) → B
  | ⟨none, l⟩ => ∑ i, u i * algebraMap Ω B (φ l (w i))
  | ⟨some k, i⟩ => algebraMap Ω B (y ⟨k, i⟩)
end Ring
end
end GroundTheory.Heights₂.Heights.NumbersDVR


