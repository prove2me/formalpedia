-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
-- name    : OAI_Analysis_TriangularHilbert_Gaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:06:29.767111+00:00
-- url     : https://prove2.me/theorems/a9bb58cf-bddb-4a4a-8d42-15ee84ecf6a6
-- title:
--   Gaussian density, heat weights and scores
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$.
--
--   1. **Gaussian density.** For variance $\sigma$ and $t\in\mathbb R$,
--   $$
--   \phi_\sigma(t)=\frac1{\sqrt{2\pi\sigma}}\,e^{-t^2/(2\sigma)} ,
--   $$
--   which is positive for $\sigma>0$ and nonnegative for $\sigma\ge0$.
--   2. **Heat weight.** $\mathrm{weight}(h,u,p,\sigma)=h\,\phi_\sigma(u-p)$ is the mass a grid point $u$ of mesh $h$ receives from the heat kernel centred at $p$ with variance $\sigma$.
--   3. **Score.** $\mathrm{score}(u,p,\sigma)=(u-p)/\sigma$ is the logarithmic derivative of the weight in the centre $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/Gaussian.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/Gaussian.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert

namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

def density (σ t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t ^ 2 / (2 * σ))

def weight (h u p σ : ℝ) : ℝ := h * density σ (u - p)
def score (u p σ : ℝ) : ℝ := (u - p) / σ

theorem density_pos {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 < density σ t := by
  unfold density
  positivity

theorem density_nonneg {σ : ℝ} (_hσ : 0 ≤ σ) (t : ℝ) : 0 ≤ density σ t := by
  unfold density
  positivity

end TriangularHilbert.Heat
end
end

end OAI


