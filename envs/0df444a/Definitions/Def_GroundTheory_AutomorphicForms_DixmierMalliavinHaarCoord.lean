-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:25.84869+00:00
-- url     : https://prove2.me/theorems/d2be9376-ba0f-47f4-b050-75f2682fac7b
-- title:
--   Dixmier Malliavin Haar Coord
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Haar Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
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
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
noncomputable def prodExpVal {d : ℕ} (X : Fin d → 𝔸) (t : Fin d → ℝ) : 𝔸 :=
  (List.ofFn fun i => exp (t i • X i)).prod
variable {𝔤 : Submodule ℝ 𝔸}
noncomputable def logCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (w : 𝔸) : Fin d → ℝ :=
  b.equivFun.toContinuousLinearEquiv (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm w))
noncomputable def prodExpCoord {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (t : Fin d → ℝ) :
    Fin d → ℝ :=
  logCoord b (prodExpVal (fun i => (b i : 𝔸)) t)
namespace IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)
end IsExpLieAlgebra
end GroundTheory.Automorphic


