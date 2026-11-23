-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:08.363729+00:00
-- url     : https://prove2.me/theorems/38f2cb1e-b425-48bd-8160-7033765cf734
-- title:
--   Short Vector Every Place
-- statement:
--   Definitions and structural lemmas for Short Vector Every Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ShortVectorEveryPlace.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory
def rootDiscriminant (K : Type) [Field K] [NumberField K] : ℝ :=
  |(discr K : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ))
def ShortVectorEveryPlace (K : Type) [Field K] [NumberField K] [StarRing K] (B : ℝ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M ∈ genus h L, ∃ x ∈ M, x ≠ 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B
end Formalism.MainNotions.BridgeLemma₂
end


