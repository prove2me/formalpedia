-- Prove2me | Definitions.Def_OverlapRouting_DemandLaw
-- name    : OverlapRouting_DemandLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:18.197756+00:00
-- url     : https://prove2.me/theorems/022953b7-8b18-4855-834c-ee8f2b3f0767
-- title:
--   Demand law $D$ on $\{0,\dots,u\}$, its mean $\mu$ and expectations over i.i.d. demands
-- statement:
--   The daily demand of each customer is an integer random variable $D$ with values in $\{0,1,\dots,u\}$, given by a probability mass function $p_k=\mathbb P[D=k]$, $k=0,\dots,u$ ($p_k\ge0$, $\sum_k p_k=1$). Its mean is
--   $$\mu=\sum_{k=0}^{u}k\,p_k .$$
--   Demands of different customers are independent and identically distributed, so a demand vector $d=(d_1,\dots,d_n)\in\{0,\dots,u\}^n$ has probability $\prod_{i=1}^n p_{d_i}$, and the expectation of a function $f$ of the daily demand is the finite sum
--   $$\mathbb E[f(\mathbf D)]=\sum_{d\in\{0,\dots,u\}^n}\Big(\prod_{i=1}^n p_{d_i}\Big)f(d).$$
--
--   Every expected cost and expected trip count of the paper is an expectation of this form.
--
--   **Formalization Note** Any pmf on $\{0,\dots,u\}$ is allowed, including values of mass $0$; positivity of $\mu$ is a hypothesis of the statements that need it.
-- source:
--   Ledvina, Qin, Simchi-Levi & Wei, A New Approach for Vehicle Routing with Stochastic Demand: Combining Route Assignment with Process Flexibility, SSRN 3656374 (PDF of 2022-03-11), https://ssrn.com/abstract=3656374, §2.1, p.5 (i.i.d. demands Dᵢ ∼ D with support {0} ∪ [u], mean µ)

import Mathlib

namespace OverlapRouting

/-- The **demand distribution** `D` of a single customer (SSRN 3656374, §2.1, p.5: "we assume
that `D` can only take non-negative integer values and has finite support `{0} ∪ [u]`"): a
probability mass function `p` on `{0, 1, …, u}`.

**Formalization Note.** Any pmf on `{0, …, u}` is allowed (values may have zero mass); this is the
authors' own usage in Appendix A, p.34. Positivity of the mean is a hypothesis of the statements
that need it. -/
structure DemandLaw where
  /-- the upper bound `u` on a single customer's demand -/
  u : ℕ
  /-- `p k = ℙ[D = k]` for `k = 0, …, u` -/
  p : Fin (u + 1) → ℝ
  nonneg : ∀ k, 0 ≤ p k
  sum_eq_one : ∑ k, p k = 1

namespace DemandLaw

/-- The mean `µ = E[D] = ∑ₖ k·p k` (p.5). -/
noncomputable def mean (D : DemandLaw) : ℝ := ∑ k : Fin (D.u + 1), ((k : ℕ) : ℝ) * D.p k

/-- Probability of the demand vector `d` of `n` customers with i.i.d. demands `Dᵢ ∼ D` (p.5):
`∏ᵢ p (dᵢ)`. -/
noncomputable def prob (D : DemandLaw) {n : ℕ} (d : Fin n → Fin (D.u + 1)) : ℝ :=
  ∏ i, D.p (d i)

/-- Expectation over the daily demand vector of `n` customers with i.i.d. demands `Dᵢ ∼ D`:
`E[f(D)] = ∑_d (∏ᵢ p (dᵢ)) · f d`, a finite sum over `{0, …, u}ⁿ`. -/
noncomputable def expect (D : DemandLaw) (n : ℕ) (f : (Fin n → Fin (D.u + 1)) → ℝ) : ℝ :=
  ∑ d, D.prob d * f d

end DemandLaw

end OverlapRouting


