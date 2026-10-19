-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
-- name    : OAI_Analysis_TriangularHilbert_GroupedGaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:16:18.772336+00:00
-- url     : https://prove2.me/theorems/0e860d69-a3aa-4fe2-b14e-d4ae478eb5a1
-- title:
--   Heat weights grouped by location and their centre derivatives
-- statement:
--   The Gaussian density is $\phi_\sigma(t)=(2\pi\sigma)^{-1/2}e^{-t^2/(2\sigma)}$, and the heat weight of a grid point $u$ with mesh $h$, centre $p$ and variance $\sigma$ is $h\,\phi_\sigma(u-p)$. Points $i$ carry positions $u_i$ and a location label $\mathrm{loc}(i)$, and each location $v$ has a centre $p_v$ and a variance $\sigma_v$.
--
--   1. **Grouped weight.** $\mathrm{groupWeight}(i)=h\,\phi_{\sigma_{\mathrm{loc}(i)}}(u_i-p_{\mathrm{loc}(i)})$.
--   2. **First variation.** For a location $v$, $\mathrm{groupFirst}_v(i)=\mathrm{score}\cdot\mathrm{weight}$ if $\mathrm{loc}(i)=v$ and $0$ otherwise; this is the derivative of the grouped weights in the centre $p_v$.
--   3. **Second variation.**
--   $$
--   \mathrm{groupSecond}_v(i)=\Bigl(\Bigl(\frac{u_i-p_v}{\sigma_v}\Bigr)^2-\frac1{\sigma_v}\Bigr)h\,\phi_{\sigma_v}(u_i-p_v)
--   $$
--   on location $v$ and $0$ elsewhere, the second centre derivative, which equals twice the variance derivative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/GroupedGaussian.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/GroupedGaussian.lean by skeleton subtraction
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

namespace OAI

universe uι uν

section

namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
open Filter
noncomputable section
variable {ι : Type uι} {ν : Type uν} [Fintype ι] [DecidableEq ι] [DecidableEq ν]

def groupWeight (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (i : ι) : ℝ :=
  weight h (u i) (p (loc i)) (σ (loc i))

def groupFirst (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (v : ν) (i : ι) : ℝ :=
  if loc i = v then score (u i) (p v) (σ v) * weight h (u i) (p v) (σ v) else 0

def groupSecond (h : ℝ) (u : ι → ℝ) (loc : ι → ν) (p σ : ν → ℝ) (v : ν) (i : ι) : ℝ :=
  if loc i = v then (score (u i) (p v) (σ v)^2 - (σ v)⁻¹) *
    weight h (u i) (p v) (σ v) else 0

end
end TriangularHilbert.Heat
end

end OAI


