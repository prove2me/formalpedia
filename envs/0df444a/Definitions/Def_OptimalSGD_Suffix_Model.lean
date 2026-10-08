-- Prove2me | Definitions.Def_OptimalSGD_Suffix_Model
-- name    : OptimalSGD_Suffix_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:17.517919+00:00
-- url     : https://prove2.me/theorems/8edd86a9-3d02-46da-b666-7ae40a8e7027
-- title:
--   Relative stochastic subgradient oracle, oracle mean, and the α-suffix average of SGD (§2, p. 2; §5, p. 6)
-- statement:
--   Let $W\subseteq\mathbb R^d$, let $F:\mathbb R^d\to\mathbb R$, and let $D$ be a probability law on a measurable space $\mathcal Z$ of samples. A **stochastic gradient oracle** is a map $g:\mathbb R^d\times\mathcal Z\to\mathbb R^d$: queried at $w$, it returns the random vector $\hat g=g(w,z)$ with $z\sim D$.
--
--   1. **Oracle mean.** The mean of the oracle at $w$ is
--   $$\bar g(w)=\mathbb E_{z\sim D}\big[g(w,z)\big]=\int g(w,z)\,dD(z).$$
--   2. **Subgradient oracle relative to $W$.** The oracle $g$ is a stochastic subgradient oracle for $F$ relative to $W$ if, for every $w\in W$, the random vector $g(w,z)$ is integrable and its mean is a subgradient of $F$ at $w$ relative to $W$:
--   $$F(u)\ \ge\ F(w)+\langle u-w,\ \bar g(w)\rangle\qquad\text{for all } u\in W.$$
--   3. **α-suffix average.** Let $w_1=0,\ w_2,\dots$ be the iterates of projected stochastic gradient descent with step sizes $\eta_t=1/(\lambda t)$ run on a sample $S=(z_1,\dots,z_T)$, i.e. $w_{t+1}=\Pi_W\big(w_t-\eta_t\, g(w_t,z_t)\big)$. For an integer $k$ with $k<T$, the suffix average of the last $T-k$ iterates is
--   $$\bar w=\frac{w_{k+1}+\dots+w_T}{T-k}.$$
--   With $k=(1-\alpha)T$ this is the paper's α-suffix average $\bar w^{\alpha}_T=\big(w_{(1-\alpha)T+1}+\dots+w_T\big)/(\alpha T)$.
--
--   These are the objects of Theorem 5 and of the steps of its proof: the oracle model of §2 and the averaging scheme of §5.
--
--   **Formalization Note** The space is $\mathbb R^d$ with the Euclidean inner product (`UnderstandingML.Vec d`); the paper allows any Hilbert space. The iterates are the published `UnderstandingML.sgdStrongIterates lam W g S`, whose index $t$ is the paper's $w_{t+1}$, so the average runs over the indices $k,\dots,T-1$. The parameter $\alpha$ does not appear in the definition; theorems tie it to $k$ by $k=(1-\alpha)T$. The subgradient condition is relative to $W$ (only points $u\in W$), as the paper's $F$ is only considered on $W$. The definitions do not require $D$ to be a probability measure, $W$ to be convex or $0\in W$, or $k<T$ (for $k\ge T$ the average is the zero vector); the theorems that use them state these hypotheses.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 2, §2 (stochastic gradient oracle); p. 3, SGD algorithm; p. 6, §5 (α-suffix averaging)

import Definitions.Def_UnderstandingML_SGD

namespace OptimalSGD.Suffix

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

/-- The mean `E_{z ∼ D}[g(w, z)]` of the stochastic gradient oracle at `w` (Rakhlin, Shamir,
Sridharan, arXiv:1109.5647v7, §2, p. 2): the vector the paper calls `g = E[ĝ]`. -/
noncomputable def oracleMean (D : MeasureTheory.Measure Z) (g : Vec d → Z → Vec d) (w : Vec d) :
    Vec d :=
  ∫ z, g w z ∂D

/-- `g` is a **stochastic subgradient oracle for `F` relative to `W`** under the law `D`
(arXiv:1109.5647v7, §2, p. 2): for every `w ∈ W`, the random vector `ĝ = g(w, z)`, `z ∼ D`, is
integrable and its expectation `E[ĝ]` is a subgradient of `F` at `w` relative to `W`, i.e.
`F(u) ≥ F(w) + ⟨u − w, E[ĝ]⟩` for every `u ∈ W`. -/
def IsSubgradientOracleOn (W : Set (Vec d)) (F : Vec d → ℝ) (D : MeasureTheory.Measure Z)
    (g : Vec d → Z → Vec d) : Prop :=
  ∀ w ∈ W, MeasureTheory.Integrable (g w) D ∧
    ∀ u ∈ W, F w + ⟪u - w, oracleMean D g w⟫_ℝ ≤ F u

/-- The **α-suffix average** (arXiv:1109.5647v7, §5, p. 6) of the projected SGD iterates with
step sizes `η_t = 1/(λt)` run on the sample `S = (z_1, …, z_T)`:
`w̄ᵅ_T = (w_{k+1} + … + w_T)/(T − k)` with `k = (1 − α)T`. In `sgdStrongIterates` the paper's
`w_t` has index `t − 1`, so the averaged indices are `k, …, T − 1`. -/
noncomputable def suffixAverage (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d) {T : ℕ}
    (S : Fin T → Z) (k : ℕ) : Vec d :=
  ((T - k : ℕ) : ℝ)⁻¹ • ∑ t ∈ Finset.Ico k T, sgdStrongIterates lam W g S t

end OptimalSGD.Suffix


