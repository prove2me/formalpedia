-- Prove2me | Definitions.Def_VRAccelCLT_Assumption2ii
-- name    : VRAccelCLT_Assumption2ii
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:12.288982+00:00
-- url     : https://prove2.me/theorems/9f346e20-9398-4f26-8390-47177b972987
-- title:
--   Assumption 2 (ii): noise covariance limit (30) and uniform integrability (31)
-- statement:
--   Let $w_k=w_{k,N_k}$ be gradient noise on a probability space with filtration $(\mathcal F_k)$ and batch sizes $N_k$, and let $S_0\in\mathbb R^{m\times m}$. **Assumption 2 (ii)** requires
--
--   $$
--   \lim_{k\to\infty}N_k\,\mathbb E\big[w_kw_k^T\mid\mathcal F_k\big]=\lim_{k\to\infty}N_k\,\mathbb E\big[w_kw_k^T\big]=S_0\quad\text{a.s.},\tag{30}
--   $$
--
--   $$
--   \lim_{r\to\infty}\ \sup_{k}\ \mathbb E\Big[\big\|\sqrt{N_k}\,w_k\big\|^2\,\mathbf 1\big[\|\sqrt{N_k}\,w_k\|>r\big]\Big]=0.\tag{31}
--   $$
--
--   So the rescaled noise $\sqrt{N_k}w_k$ has an asymptotically constant covariance $S_0$, conditionally and unconditionally, and its squared norms are uniformly integrable. This is what makes the limit in the CLTs Gaussian with covariance built from $S_0$. The paper assumes it on top of (5).
--
--   **Formalization Note** The matrix limits of (30) are stated entrywise. (31) is stated as: for every $\varepsilon>0$ there is $R$ with $\mathbb E[\|\sqrt{N_k}w_k\|^2\mathbf 1[\|\sqrt{N_k}w_k\|>r]]\le\varepsilon$ for all $r\ge R$ and all $k$, which avoids a real supremum (a real supremum of an unbounded family is $0$ in Lean); its expectation is a lower Lebesgue integral of a nonnegative function.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Assumption 2 (ii), eqs. (30)–(31), p.14

import Mathlib

open MeasureTheory Filter
open scoped Topology ENNReal

namespace VRAccelCLT

/-- **Assumption 2 (ii)**: the noise covariance condition (30) and the uniform integrability
condition (31). Lei, Shanbhag, arXiv:2006.07769v3, Assumption 2, p.14:
"(ii) The noise sequence {wk,Nk} further satisfies
lim_{k→∞} (Nk E[wk,Nk wk,Nk^T | Fk]) = lim_{k→∞} (Nk E[wk,Nk wk,Nk^T]) = S0, a.s., (30)
and lim_{r→∞} sup_k E[∥√Nk wk,Nk∥² I[∥√Nk wk,Nk∥>r]] = 0, (31)".

`Assumption2ii μ ℱ w N S0` states:
1. (30), conditional part: for all `i, j`, almost surely `N_k · E[w_{k,i} w_{k,j} | ℱ_k] → (S₀)_{ij}`;
2. (30), unconditional part: for all `i, j`, `N_k · E[w_{k,i} w_{k,j}] → (S₀)_{ij}`;
3. (31): for every `ε > 0` there is `R` such that for all `r ≥ R` and all `k`,
   `E[‖√N_k w_k‖² 1{‖√N_k w_k‖ > r}] ≤ ε`.

**Formalization Note.** The matrix limits of (30) are stated entrywise (equivalent, the space of
matrices being finite-dimensional). (31) is stated with `∀ ε > 0, ∃ R, ∀ r ≥ R, ∀ k`, which is
`lim_{r→∞} sup_k (…) = 0` without a real `⨆` (a real supremum of an unbounded family is `0` in
Lean); its expectation is a lower Lebesgue integral of a nonnegative function, so it carries no
integrability side condition. "Further" in the paper: this is assumed on top of (5) (`IsVRNoise`),
which makes the integrals of (30) finite. -/
def Assumption2ii {m : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (w : ℕ → Ω → EuclideanSpace ℝ (Fin m)) (N : ℕ → ℕ)
    (S0 : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  (∀ i j : Fin m, ∀ᵐ ω ∂μ,
      Tendsto (fun k => (N k : ℝ) * (μ[fun ω' => w k ω' i * w k ω' j | ℱ k]) ω) atTop
        (𝓝 (S0 i j))) ∧
    (∀ i j : Fin m,
      Tendsto (fun k => (N k : ℝ) * ∫ ω, w k ω i * w k ω j ∂μ) atTop (𝓝 (S0 i j))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ r : ℝ, R ≤ r → ∀ k : ℕ,
      ∫⁻ ω, Set.indicator {ω' | r < ‖Real.sqrt (N k) • w k ω'‖}
          (fun ω' => ENNReal.ofReal (‖Real.sqrt (N k) • w k ω'‖ ^ 2)) ω ∂μ
        ≤ ENNReal.ofReal ε

end VRAccelCLT


