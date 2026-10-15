-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
-- name    : OAI_Combinatorics_BooleanFunctions_MomentTransfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:30:00.239094+00:00
-- url     : https://prove2.me/theorems/1ac3f8bf-69ac-442f-9b42-baad53cd8d91
-- title:
--   Weighted moments, the gain functional, and the Gaussian improvement constant $\eta$
-- statement:
--   Weights are indexed by a finite set $I$ (in the application, the leaves), and moment orders by $k\in\{0,1,2\}$.
--
--   1. **Weighted moments.** For a measure $P$ on $\Omega$, a function $T:\Omega\to\mathbb{R}$ and weights $w_i:\mathbb{R}\to\mathbb{R}$,
--   $$m_k(i)=\int_\Omega w_i\big(T(\omega)\big)\,T(\omega)^k\,dP(\omega).$$
--   2. **Means and variances of an array.** For an array $l=(l_{k,i})$,
--   $$\bar l_i=\frac{l_{1,i}}{l_{0,i}},\qquad v_i(l)=\frac{l_{2,i}}{l_{0,i}}-\bar l_i^{\,2}.$$
--   3. **Gain.** For two arrays $l$ (leaf moments) and $s$ (selector moments),
--   $$\operatorname{gain}(l,s)=\Big(\prod_i l_{0,i}\Big)\Big(1+\sum_i v_i(l)-\sum_i\frac{s_{2,i}+2(1-\bar l_i)\,s_{1,i}+\big((1-\bar l_i)^2+\sum_{j\neq i}v_j(l)\big)s_{0,i}}{l_{0,i}}\Big).$$
--   4. **Gaussian moment arrays.** The arrays $m^\gamma_\ell$ and $m^\gamma_\omega$ of weighted moments of the identity under the standard Gaussian $\gamma$, for the leaf tests $\ell_i$ and the selector tests $\omega_i$. Three recorded identities state that the order-zero leaf moment, leaf mean and leaf variance are $\beta_i$, $\mu_i$ and $\sigma_i^2$.
--   5. **The constant $\eta$.**
--   $$\eta=\tfrac12\,\operatorname{gain}\big(m^{\gamma}_{\ell},m^{\gamma}_{\omega}\big).$$
--
--   The gain is a continuous function of finitely many moments of order at most two (where the order-zero leaf moments are nonzero), so by the central limit theorem its value along normalized sums converges to the Gaussian value. Expanding the Gaussian gain gives $(\prod_i\beta_i)(1+\sum_i\sigma_i^2-J)$, and $\eta$, half of it, is the constant in the factor $1+\eta/(2N_\ast+2)$ by which each amplification step improves the variance-to-cost ratio.
--
--   **Formalization Note** The Lean names are `moments`, `means`, `vars`, `gain`, `gaussianLeafMoments`, `gaussianSelectorMoments`, the simp lemmas `gaussianLeaf_zero`, `gaussianLeaf_mean`, `gaussianLeaf_var`, and `eta`. Moment orders are `Fin 3`; divisions follow Lean's convention that division by zero gives zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/MomentTransfer.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/MomentTransfer.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace MomentTransfer
open SmoothGaussian SmoothSelector GaussianGain
def moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : Ω → ℝ)
    {ι : Type*} (w : ι → ℝ → ℝ) (k : Fin 3) (i : ι) : ℝ :=
  ∫ x, w i (T x)*(T x)^(k:ℕ) ∂P

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def means (l : Fin 3 → ι → ℝ) (i : ι) : ℝ := l 1 i / l 0 i
def vars (l : Fin 3 → ι → ℝ) (i : ι) : ℝ := l 2 i / l 0 i - (means l i)^2

def gain (l s : Fin 3 → ι → ℝ) : ℝ :=
  (∏ i, l 0 i) * (1 + ∑ i, vars l i -
    ∑ i, (s 2 i + 2*(1-means l i)*s 1 i +
      ((1-means l i)^2+∑ j ∈ Finset.univ.erase i, vars l j)*s 0 i) / l 0 i)

def gaussianLeafMoments : Fin 3 → Leaves → ℝ := moments (gaussianReal 0 1) id leafTest
def gaussianSelectorMoments : Fin 3 → Leaves → ℝ := moments (gaussianReal 0 1) id selectorTest

@[simp] theorem gaussianLeaf_zero (i : Leaves) : gaussianLeafMoments 0 i = GaussianGain.beta i := by
  simp only [gaussianLeafMoments,moments,Fin.val_zero,pow_zero,mul_one,GaussianGain.beta,mass,id_eq]
@[simp] theorem gaussianLeaf_mean (i : Leaves) : means gaussianLeafMoments i = mu i := by
  simp only [means,gaussianLeafMoments,moments,Fin.val_zero,Fin.val_one,pow_zero,pow_one,mul_one,
    mu,mean,mass,id_eq]
@[simp] theorem gaussianLeaf_var (i : Leaves) : vars gaussianLeafMoments i = sigma i := by
  rw [vars,gaussianLeaf_mean]
  simp only [gaussianLeafMoments,moments,Fin.val_zero,pow_zero,mul_one,
    sigma,SmoothGaussian.variance,mass,id_eq,mu]
  rfl

def eta : ℝ := gain gaussianLeafMoments gaussianSelectorMoments / 2

end MomentTransfer
end SquareRootDegree

end

end OAI


