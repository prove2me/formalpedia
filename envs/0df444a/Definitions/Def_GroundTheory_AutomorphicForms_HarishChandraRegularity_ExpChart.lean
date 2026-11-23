-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
-- name    : GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:50.149813+00:00
-- url     : https://prove2.me/theorems/30917447-7bc4-4a73-a1f9-8ed271907a6a
-- title:
--   Exp Chart
-- statement:
--   Definitions and structural lemmas for Exp Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
noncomputable def expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : 𝔸 :=
  exp ((coordEquiv b p.1 : 𝔤) : 𝔸) * exp (p.2 • (X : 𝔸))
noncomputable def expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : EuclideanSpace ℝ (Fin d) :=
  (coordEquiv b).symm (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)))
noncomputable def expChartCoeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  fderiv ℝ (expChartFlow b X) (x, 0) (0, 1)
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
end IsExpLieAlgebra
end GroundTheory.Automorphic


