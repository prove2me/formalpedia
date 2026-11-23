-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinSeries
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavinSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:04:24.25631+00:00
-- url     : https://prove2.me/theorems/798c06b9-8568-4c3e-ba08-6414186c9d6f
-- title:
--   Dixmier Malliavin Series
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
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
open NormedSpace Set MeasureTheory
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
noncomputable def dirDeriv (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) : ℂ :=
  iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) 0
end IsExpLieAlgebra
end GroundTheory.Automorphic


