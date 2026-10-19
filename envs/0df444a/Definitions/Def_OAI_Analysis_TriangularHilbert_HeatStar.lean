-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
-- name    : OAI_Analysis_TriangularHilbert_HeatStar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:18:09.929382+00:00
-- url     : https://prove2.me/theorems/e8ac7db4-345d-4b7c-8d50-d2d34006b02f
-- title:
--   Heat-weighted star energies and their first and second variations
-- statement:
--   These notions belong to a heat-flow proof that the maximally truncated triangular Hilbert transform maps $L^3\times L^3$ to $L^{3/2}$. After a change of variables the problem becomes a cyclic trilinear form $\sum_{i,j,k}A^{(0)}_{ij}A^{(1)}_{jk}A^{(2)}_{ki}\,K(u_i+u_j+u_k)$ over a finite grid, controlled by matrix energies of the form $\operatorname{tr}P^{3/2}$. The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$. Each vertex $v$ of the triangle has a centre $p_v$ and a variance $\sigma_v$.
--
--   1. **Heat array.** The heat weights are $g_v(i)=h\,\phi_{\sigma_v}(u_i-p_v)$, and $\mathrm{heatArray}=\mathrm{weightedArray}(A,g)$.
--   2. **Heat energy.** $\mathrm{heatEnergy}(v)=E\bigl(\mathrm{starGram}(\mathrm{heatArray},v)\bigr)$, the $S^3$-energy of the star at vertex $v$.
--   3. **Local Gram matrices.** For vertices $v,w$, the base is the bare row at $v$ (if $w=v$) or the bare column, and $\mathrm{localGram}$, $\mathrm{localFirst}$, $\mathrm{localSecond}$ are its weighted Gram matrices with the grouped weights, their first centre variation at $w$, and their second variation at $w$.
--   4. **Variations.** $\mathrm{heatFirst}=\nabla E(\mathrm{localGram})[\mathrm{localFirst}]$ and $\mathrm{heatVariance}=\frac12\nabla E(\mathrm{localGram})[\mathrm{localSecond}]$, and
--   $$
--   \mathrm{heatPure}=\mathrm{hessianCost}(\mathrm{localGram},\mathrm{localFirst})+\nabla E(\mathrm{localGram})[\mathrm{localSecond}],
--   $$
--   the second centre derivative of the energy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/HeatStar.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/HeatStar.lean by skeleton subtraction
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

namespace OAI

universe uι

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def heatWeights (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) : Three → ι → ℝ :=
  fun v i => weight h (u i) (p v) (σ v)

def heatArray (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) :=
  weightedArray A (heatWeights h u p σ)

def heatEnergy (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v : Three) : ℝ :=
  energy (starGram (heatArray A h u p σ) v)

def fixedBase (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v w : Three) :=
  if w = v then rowBare A g v else colBare A g v

def localGram (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupWeight h (fun a : BlockSpace ι => u a.2) Prod.fst p σ)

def localFirst (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupFirst h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w)

def localSecond (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) :=
  weightedGram (fixedBase A (heatWeights h u p σ) v w)
    (groupSecond h (fun a : BlockSpace ι => u a.2) Prod.fst p σ w)

def heatFirst (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  energyGradient (localGram A h u p σ v w) (localFirst A h u p σ v w)

def heatPure (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  hessianCost (localGram A h u p σ v w) (localFirst A h u p σ v w) +
    energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)

def heatVariance (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p σ : Three → ℝ) (v w : Three) : ℝ :=
  (1/2 : ℝ) * energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)

end
end TriangularHilbert.Heat
end

end OAI


