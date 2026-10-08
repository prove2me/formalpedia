-- Prove2me | Definitions.Def_GVRPricing_StoppingTime_Menu
-- name    : GVRPricing_StoppingTime_Menu
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:04:38.525338+00:00
-- url     : https://prove2.me/theorems/16e43a85-1ba6-4f0e-a4ed-dfc446da7afe
-- title:
--   §4 — discrete price menu $p_1<\dots<p_K$ with rates $\lambda_1>\dots>\lambda_K$ and decreasing revenue rates on a concave curve
-- statement:
--   The firm may charge only one of finitely many prices $\mathcal P=\{p_1,\dots,p_K,p_\infty\}$, where $p_\infty$ is the null price (demand rate $0$). At price $p_k$ demand arrives as a Poisson process with known rate $\lambda_k$. A **menu** with $K\ge 2$ prices consists of prices $p_1,\dots,p_K\ge 0$ and rates $\lambda_1,\dots,\lambda_K>0$ such that
--
--   1. $p_1<p_2<\dots<p_K$ and $\lambda_1>\lambda_2>\dots>\lambda_K$;
--   2. the revenue rates $r_k=p_k\lambda_k$ satisfy $r_1>r_2>\dots>r_K$;
--   3. the points $(\lambda_k,r_k)$ lie on a concave function $f$ on $[0,\infty)$ with $f(0)=0$.
--
--   Indices are also extended by the conventions $\lambda_{K+1}=0$ and $r_{K+1}=0$ of §4.0.1.
--
--   The menu is the data of the discrete-price model of §4: Proposition 4, the stopping-time heuristic and Theorem 5 are all stated for it.
--
--   **Formalization Note** Lean indexes the menu by `Fin K`, so Lean index $k$ is the paper's price number $k+1$; `lamN`, `pN`, `rN` extend the sequences to all of $\mathbb N$ with value $0$ beyond $K$. Condition 3 is not printed on p. 1010. It is the reading of "corresponding to price $p_k$, we have a known demand rate $\lambda_k$", where $\lambda_k$ comes from a regular demand function whose revenue rate $r(\cdot)$ is concave (§2.1); the page's own justification of $r_1>\dots>r_K$ appeals to $r(\cdot)$. Without condition 3 Proposition 4 and Theorem 5 are false: for $\lambda=(3,2,1)$, $p=(1,1.01,1.5)$, $t=1$, $n=1.5$, Proposition 4's allocation earns $1.76$, while $p_1$ for $0.25$ and $p_3$ for $0.75$ time units earns $1.875$. Positivity of the rates is the reading that each $p_k$ is a non-null price.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1010 (PDF 12), §4; concavity from §2.1, pp. 1003–1004 (PDF 5–6)

import Mathlib

namespace GVRPricing.StoppingTime

/-- The discrete price menu of Gallego–van Ryzin (1994), §4, p. 1010.
Prices `p k` and Poisson demand rates `lam k`, indexed by `k : Fin K`; index `k` is the paper's
price number `k + 1`.  The paper's conditions: `p₁ < ⋯ < p_K`, `λ₁ > ⋯ > λ_K`,
revenue rates `r_k = p_k λ_k` strictly decreasing.  Prices lie in `ℝ⁺`, rates are positive
(`p_k` is not the null price `p_∞`).  `concave` is the reading of "corresponding to price `p_k`,
we have a known demand rate `λ_k`" with a concave revenue rate `r(·)`, `r(0) = 0`: the points
`(λ_k, r_k)` lie on a concave function on `[0, ∞)` vanishing at `0`. -/
structure Menu (K : ℕ) where
  /-- prices `p_1, …, p_K` (0-based) -/
  p : Fin K → ℝ
  /-- demand rates `λ_1, …, λ_K` (0-based) -/
  lam : Fin K → ℝ
  two_le : 2 ≤ K
  p_nonneg : ∀ k, 0 ≤ p k
  lam_pos : ∀ k, 0 < lam k
  p_strictMono : StrictMono p
  lam_strictAnti : StrictAnti lam
  r_strictAnti : StrictAnti (fun k => p k * lam k)
  concave : ∃ f : ℝ → ℝ, ConcaveOn ℝ (Set.Ici 0) f ∧ f 0 = 0 ∧ ∀ k, f (lam k) = p k * lam k

namespace Menu

variable {K : ℕ} (M : Menu K)

/-- Revenue rate `r_k = p_k λ_k`. -/
def r (k : Fin K) : ℝ := M.p k * M.lam k

/-- `λ` indexed by `ℕ` (0-based); `lamN k = 0` for `k ≥ K`, i.e. the paper's `λ_{K+1} = 0`. -/
def lamN (k : ℕ) : ℝ := if h : k < K then M.lam ⟨k, h⟩ else 0

/-- `p` indexed by `ℕ` (0-based); `0` out of range (never used out of range). -/
def pN (k : ℕ) : ℝ := if h : k < K then M.p ⟨k, h⟩ else 0

/-- `r` indexed by `ℕ` (0-based); `rN k = 0` for `k ≥ K`, the paper's `r_{K+1} = 0`. -/
def rN (k : ℕ) : ℝ := M.pN k * M.lamN k

end Menu

end GVRPricing.StoppingTime


