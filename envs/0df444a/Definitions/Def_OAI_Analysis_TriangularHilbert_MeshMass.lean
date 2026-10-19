-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
-- name    : OAI_Analysis_TriangularHilbert_MeshMass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:07:18.882524+00:00
-- url     : https://prove2.me/theorems/3c4826df-fd18-433b-bf27-b54b8c061531
-- title:
--   Constant bounding Gaussian Riemann sums
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$.
--
--   The mesh mass constant is
--   $$
--   C_{\mathrm{mesh}}=2\,e^{1/2}>0 .
--   $$
--   It bounds the Riemann sums $\sum_{i<n}h\,\phi_\sigma(c+hi)$ of the Gaussian density over any arithmetic progression of mesh $h$, provided the variance satisfies $h^2\le\sigma$. Thus the total heat weight that a grid receives from one Gaussian is bounded independently of the grid size, the offset $c$ and the number of points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MeshMass.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MeshMass.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

def meshMassConstant : ℝ := 2 * Real.exp (1/2)

lemma meshMassConstant_pos : 0 < meshMassConstant := by unfold meshMassConstant; positivity

end
end TriangularHilbert.Heat
end

end OAI


