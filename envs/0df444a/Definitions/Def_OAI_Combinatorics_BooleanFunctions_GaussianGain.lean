-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
-- name    : OAI_Combinatorics_BooleanFunctions_GaussianGain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:29:15.888779+00:00
-- url     : https://prove2.me/theorems/5bd5f93b-e7e2-4cf4-8855-8903b43effe0
-- title:
--   Leaf tests, selector weights and the Gaussian kernel integral $J$
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $\mathbb{R}$, and use the tents $\operatorname{tent}_{a,h}$, the weighted $\operatorname{mass}$, $\operatorname{mean}$ and $\operatorname{var}$, and the grid hats $\operatorname{hat}_i$, selector weights $\omega_i$ and centres $c_i=1+\delta(i-N)$ of the previous files.
--
--   1. **Kernels for general parameters.** For $N\in\mathbb{N}$, $\delta\in\mathbb{R}$ and real families $\mu,v,\beta$ indexed by $i\in\{0,\dots,2N\}$,
--   $$K^{\mathrm{c}}(t)=\sum_{i=0}^{2N}\operatorname{hat}_i(t)\,\frac{(1+t-\mu_i)^2+v_i}{\beta_i},\qquad \rho(t)=1-\sum_{i=0}^{2N}\operatorname{hat}_i(t),$$
--   the central kernel (continuous in $t$) and the residual mass of the hats.
--   2. **Numerical constants.** $N_\ast=(2^{128})^8=2^{1024}$, width $w=1/(2^{128})^{12}=2^{-1536}$, radius $R=96$ and step $\delta_\ast=R/N_\ast$.
--   3. **Leaves and tests.** The leaves are $i\in\{0,\dots,2N_\ast\}$. Leaf $i$ has the leaf test $\ell_i=\operatorname{tent}_{c_i,w}$ with $c_i=1+\delta_\ast(i-N_\ast)$, and the selector test $\omega_i$ (the selector weight for $N_\ast$ and $\delta_\ast$).
--   4. **Gaussian leaf statistics.** $\beta_i=\operatorname{mass}_\gamma(\ell_i)$, $\mu_i=\operatorname{mean}_\gamma(\ell_i)$ and $\sigma_i^2=\operatorname{var}_\gamma(\ell_i)$; the total variance $\sum_i\sigma_i^2$; and, for each $i$, the variance of the other leaves $\sum_{j\neq i}\sigma_j^2$.
--   5. **Kernel and its Gaussian integral.**
--   $$K(t)=\sum_{i=0}^{2N_\ast}\omega_i(t)\,\frac{(1+t-\mu_i)^2+\sum_{j\neq i}\sigma_j^2}{\beta_i},\qquad J=\int_{\mathbb{R}}K\,d\gamma .$$
--
--   These objects describe the Gaussian limit of one amplification step. A standard Gaussian value $t$ selects a leaf $i$ with probability $\omega_i(t)$; a leaf $j$ is passed with probability $\ell_j$, and a passing value lies within the tiny width $w$ of $c_j$. The quantity $\big(\prod_i\beta_i\big)\big(1+\sum_i\sigma_i^2-J\big)$ is the Gaussian gain of the step, and the decisive numerical estimate of the construction is $J<1/2$, which makes this gain positive.
--
--   **Formalization Note** The Lean names are `centralKernel`, `residual`, `gridN`, `width`, `radius`, `step`, `Leaves` (the type `Fin (2*gridN+1)`), `leafTest`, `selectorTest`, `beta`, `mu`, `sigma` (which is a variance, written $\sigma_i^2$ above), `totalVariance`, `otherVariance`, `kernel` and `J`, with `gaussianReal 0 1` for $\gamma$. `kernel` coincides with `centralKernel` plus the residual term at the middle leaf.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/GaussianGain.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/GaussianGain.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace GaussianGain
open SmoothGaussian SmoothSelector

def centralKernel (N : ℕ) (δ : ℝ) (μ v β : Fin (2*N+1) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, hat N δ i t * ((1+t-μ i)^2+v i) / β i

@[fun_prop] theorem centralKernel_continuous (N : ℕ) (δ : ℝ)
    (μ v β : Fin (2*N+1) → ℝ) : Continuous (centralKernel N δ μ v β) := by
  unfold centralKernel
  fun_prop

def residual (N : ℕ) (δ t : ℝ) : ℝ := 1-∑ i, hat N δ i t

def gridN : ℕ := (2^128)^8
def width : ℝ := 1 / ((2:ℝ)^128)^12
def radius : ℝ := 96
def step : ℝ := radius / gridN

abbrev Leaves := Fin (2*gridN+1)
def leafTest (i : Leaves) : ℝ → ℝ := tent (center gridN step i) width
def selectorTest (i : Leaves) : ℝ → ℝ := weight gridN step i
def beta (i : Leaves) : ℝ := mass (gaussianReal 0 1) (leafTest i)
def mu (i : Leaves) : ℝ := mean (gaussianReal 0 1) (leafTest i)
def sigma (i : Leaves) : ℝ := variance (gaussianReal 0 1) (leafTest i)
def totalVariance : ℝ := ∑ i, sigma i
def otherVariance (i : Leaves) : ℝ := ∑ j ∈ Finset.univ.erase i, sigma j

def kernel (t : ℝ) : ℝ := ∑ i, selectorTest i t *((1+t-mu i)^2+otherVariance i)/beta i

def J : ℝ := ∫ t, kernel t ∂gaussianReal 0 1

end GaussianGain
end SquareRootDegree

end

end OAI


