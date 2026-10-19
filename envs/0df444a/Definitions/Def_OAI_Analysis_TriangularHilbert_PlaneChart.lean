-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
-- name    : OAI_Analysis_TriangularHilbert_PlaneChart
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:25:50.478195+00:00
-- url     : https://prove2.me/theorems/abd4809d-238d-4b74-8f39-d4b768ed5a66
-- title:
--   Charts of the plane of centres with fixed sum
-- statement:
--   The three heat centres $p=(p_0,p_1,p_2)$ of the triangle are constrained to a plane $p_0+p_1+p_2=d$, which is parametrized by two free coordinates $z=(z_1,z_2)$.
--
--   1. **Charts.** $\mathrm{chart}(i,d,z)$ places $d-z_1-z_2$ in coordinate $i$ and $z_1,z_2$ in the other two coordinates, in order:
--   $$
--   \mathrm{chart}(0,d,z)=(d-z_1-z_2,z_1,z_2),\quad\mathrm{chart}(1,d,z)=(z_1,d-z_1-z_2,z_2),\quad\mathrm{chart}(2,d,z)=(z_1,z_2,d-z_1-z_2).
--   $$
--   2. **Changes of chart.** The reflection $(z_1,z_2)\mapsto(z_1,d-z_1-z_2)$ is an involutive homeomorphism of the plane. Composing it with the coordinate swap gives homeomorphisms that transform chart $2$ into chart $i$, so plane integrals can be computed in any chart.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/PlaneChart.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/PlaneChart.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory
open MatrixEnergy
noncomputable section

def chart (i : Three) (d : ℝ) (z : ℝ × ℝ) : Three → ℝ :=
  if i = 0 then ![d-z.1-z.2, z.1, z.2]
  else if i = 1 then ![z.1, d-z.1-z.2, z.2]
  else ![z.1, z.2, d-z.1-z.2]

def chartReflection (d : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1, d-z.1-z.2)
  invFun z := (z.1, d-z.1-z.2)
  left_inv z := by exact Prod.ext rfl (by dsimp; ring)
  right_inv z := by exact Prod.ext rfl (by dsimp; ring)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def chartChange (i : Three) (d : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  if i = 0 then (chartReflection d).trans (Homeomorph.prodComm ℝ ℝ)
  else if i = 1 then chartReflection d
  else Homeomorph.refl _

end
end TriangularHilbert.Heat
end

end OAI


