-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavinBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:04.251074+00:00
-- url     : https://prove2.me/theorems/2eb6e795-9d32-40da-8072-4b2b73dc8201
-- title:
--   Dixmier Malliavin Basic
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
noncomputable def prodExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) : G :=
  (List.ofFn fun i => h.expG (t i • X i)).prod
end IsExpLieAlgebra
end GroundTheory.Automorphic


