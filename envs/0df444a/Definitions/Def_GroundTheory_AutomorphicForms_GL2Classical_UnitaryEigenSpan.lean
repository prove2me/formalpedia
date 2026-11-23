-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_UnitaryEigenSpan
-- name    : GroundTheory_AutomorphicForms_GL2Classical_UnitaryEigenSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:12.882183+00:00
-- url     : https://prove2.me/theorems/5830a42b-b786-4def-9dd7-3ef7a60e4c3c
-- title:
--   Unitary Eigen Span
-- statement:
--   Definitions and structural lemmas for Unitary Eigen Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/UnitaryEigenSpan.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
namespace GroundTheory.Automorphic
noncomputable section
namespace GL2Classical
variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
section
variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)
def orbitSum (K : Subgroup G) (v : E) (hv : (Set.range fun k : K => ρ k v).Finite) : E :=
  ∑ w ∈ hv.toFinset, w
variable {ρ}
end
variable {ρ : Representation ℂ G E} {ι : E →ₗ[ℂ] H} {T : Submodule ℂ E} {φ : E}
end GL2Classical
end
end GroundTheory.Automorphic


