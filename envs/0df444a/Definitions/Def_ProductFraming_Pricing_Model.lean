-- Prove2me | Definitions.Def_ProductFraming_Pricing_Model
-- name    : ProductFraming_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:35.098179+00:00
-- url     : https://prove2.me/theorems/a87a28da-35f4-450d-b5d8-53dae14eeacc
-- title:
--   Product framing with MNL pricing: page-count law, feasible framings, $S(x)$, $E[R(r\mid S(X))]$ and the optimal value $R(a)$
-- statement:
--   This file sets up the joint pricing-and-framing problem of Gallego, Li, Truong and Wang on top of the MNL choice model.
--
--   **Pages and the page-count law.** Products are displayed on $m$ virtual pages, each holding at most $p$ products. A consumer views the first $X$ pages, where $X \in [m]=\{1,\dots,m\}$ is random with law $\lambda(x) = \mathbf P[X=x]$; thus $\lambda(x)\ge 0$ for $x\in[m]$ and $\sum_{x=1}^m \lambda(x) = 1$.
--
--   **Framings.** A framing assigns each product $i$ either a page $x(i)\in[m]$ or "not displayed". It is **feasible** when every page holds at most $p$ products (each product is on at most one page by construction). These are exactly the constraints of problem (1).
--
--   **Consideration sets.** A consumer who views $x$ pages considers $S(x)$, the set of products displayed on pages $1,\dots,x$.
--
--   **Total expected revenue.** For a framing and a price vector $r$,
--   $$
--   \mathbf E\big[R(r\mid S(X))\big] = \sum_{x=1}^m \lambda(x)\,R\big(r\mid S(x)\big).
--   $$
--
--   **Optimal pricing value.** For a fixed framing and quality vector $a$,
--   $$
--   R(a) = \sup_{r\in\mathbb R^n} \sum_{x=1}^m \lambda(x)\,R\big(r\mid S(x)\big),
--   $$
--   the optimal expected revenue over all price vectors (the paper writes $\max$).
--
--   **Formalization Note.** A framing is `f : Fin n → ℕ`: product $i$ is on page `f i` when $1\le$ `f i` $\le m$, and `f i = 0` means "not displayed" (the paper's $x(i)=m+1$). Feasibility also requires `f i ≤ m`. The law $\lambda$ is `lam : ℕ → ℝ`; only its values on $\{1,\dots,m\}$ are used. $R(a)$ is a real supremum `⨆ r`, which Lean evaluates to $0$ on an unbounded set; every statement that uses it also asserts that the revenues are bounded above.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §3, pp. 5–6 (pages, X, λ, problem (1)); §7.1, p. 16 (pricing problem); A.5, Proof of Theorem 6, p. 44 (R(a))

import Mathlib
import Definitions.Def_ProductFraming_Pricing_MNL
import Definitions.Def_ProductFraming_Nest_Model
import Definitions.Def_ProductFraming_Trunc_Framing
open Finset

namespace ProductFraming.Pricing

/-- Total expected revenue `E[R(r|S(X))] = ∑_{x=1}^m λ(x) R(r|S(x))` of the framing `f` and
the price vector `r` (§7.1, p. 16; A.5, p. 43). -/
noncomputable def totalRevenue {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (f : Fin n → ℕ) (r : Fin n → ℝ) : ℝ :=
  ∑ x ∈ Icc 1 m, lam x * revenue a β r (ProductFraming.Nest.consideration f x)

/-- Optimal pricing value of a fixed framing as a function of the qualities
(A.5, Proof of Theorem 6, p. 44): `R(a) = sup_r E[R(r|S(X))]`. This is the real supremum;
statements using it also assert that the set of revenues is bounded above. -/
noncomputable def optRevenue {n : ℕ} (m : ℕ) (a : Fin n → ℝ) (β : ℝ) (lam : ℕ → ℝ)
    (f : Fin n → ℕ) : ℝ :=
  ⨆ r : Fin n → ℝ, totalRevenue m a β lam f r

end ProductFraming.Pricing


