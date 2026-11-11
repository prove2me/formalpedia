-- Prove2me | Definitions.Def_OAIQ240Bp013
-- name    : OAIQ240Bp013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T00:22:22.617456+00:00
-- url     : https://prove2.me/theorems/a1d39923-7c26-4ea1-97bf-a6308f8c1e59
-- title:
--   Definitions bundle OAIQ240Bp013 of the split of OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 1 definition and 1 theorem. The definitions and types are `OAI.SymplecticBallPacking.Hamiltonian.cutoffWedge`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`BallPacking_Rigidity_PlanarResidueCutoff`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Rigidity/PlanarResidueCutoff.lean), [`BallPacking_Surfaces_QuadricCurveManifold`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Surfaces/QuadricCurveManifold.lean).
--
--   **Imports.** It imports the bundles `OAIQ240Bp008`, `OAIQ240Bp009` and `OAIQ240Bp010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ240Bp019`; the statements `OAI_PackingSufficiencySupport_DiagonalQuadrics_curveEndCutoff_partition_mass`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_polynomial_target_embedding`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_exists_quadric_exact_affine_moser`, `OAI_PackingSufficiencySupport_DiagonalQuadrics_tendsto_curveCutoff_bounded_residue` and `OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_disk_isotopy`; the proofs of `OAI.HigherDimensionalBallPacking.Rigidity.packing_two_line_reduction_bp240`, `OAI_PackingSufficiencySupport_Hamiltonian_exists_hamiltonian_disk_isotopy` and `OAI_PackingSufficiencySupport_Hamiltonian_exists_thin_planar_embedding`.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ240Bp008
import Definitions.Def_OAIQ240Bp009
import Definitions.Def_OAIQ240Bp010

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_PlanarResidueCutoff
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymplecticBallPacking.Hamiltonian
open Set Function MeasureTheory Filter
open scoped ContDiff Topology

def cutoffWedge (f : Plane → ℝ) (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) : ℝ :=
  fderiv ℝ f z (1,0)*β z (0,1)-fderiv ℝ f z (0,1)*β z (1,0)

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Surfaces_QuadricCurveManifold
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

theorem real_transition_smooth (x y : locus a) :
    ContDiffOn ℝ ∞ ((realChart a x).symm.trans (realChart a y))
      ((realChart a x).symm.trans (realChart a y)).source := by
  let e := (normalChartAt a x).sliceChart x
  let f := (normalChartAt a y).sliceChart y
  have hc := ((normalChartAt a x).transition_smooth x (normalChartAt a y) y).restrict_scalars ℝ
  have hd := Complex.equivRealProdCLM.contDiff.comp_contDiffOn
    (hc.comp Complex.equivRealProdCLM.symm.contDiff.contDiffOn (mapsTo_preimage _ _))
  apply hd.mono
  intro z hz
  exact ⟨hz.1.2,hz.2.1⟩

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end


