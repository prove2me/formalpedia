-- Prove2me | Definitions.Def_RiskBalancingMNL_Params
-- name    : RiskBalancingMNL_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:44.291218+00:00
-- url     : https://prove2.me/theorems/718efcf0-e692-402c-998a-75f5538c95d6
-- title:
--   MNL model with symmetric price sensitivity: shares $q_i$, $q_0$, profit $\pi$, $g$, objective $L=\pi^2-\lambda g$, and optimality in problem (6)
-- statement:
--   A firm sells $n\ge1$ products. Product $i$ has quality parameter $a_i$ and unit cost $c_i$, and all products share one price coefficient $b>0$. At the markup vector $m=(m_1,\dots,m_n)$ the nominal utility of product $i$ is $v_i(m_i)=a_i-bc_i-bm_i$, and the multinomial logit choice probabilities (7)–(8) are
--   $$
--   q_i(m)=\frac{e^{a_i-bc_i-bm_i}}{1+\sum_j e^{a_j-bc_j-bm_j}},\qquad q_0(m)=\frac{1}{1+\sum_j e^{a_j-bc_j-bm_j}} .
--   $$
--   The expected profit per customer, the second moment and the risk-balancing objective with risk weight $\lambda$ are
--   $$
--   \pi(m)=\sum_i m_iq_i(m),\qquad g(m)=\sum_i m_i^2q_i(m),\qquad L_\lambda(m)=\pi(m)^2-\lambda\,g(m).
--   $$
--   A markup vector is **feasible** for problem (6) when $\pi(m)\ge0$, and it is **optimal** for risk weight $\lambda$ when it is feasible and $L_\lambda(m)\ge L_\lambda(m')$ for every feasible $m'\in\mathbb R^n$. Finally $(t,\dots,t)$ denotes the equal markup $t$.
--
--   These are the objects of every statement of the mission: Lemma 1, equations (9)–(13), Lemma 3, Theorem 1 and Corollary 1.
--
--   **Formalization Note** The shares are the platform's finite logit share (`FlagshipMEA.Monopoly.logitShare`) applied to the attractions $e^{v_i(m_i)}$; products are indexed by $\{0,\dots,n-1\}$. Problem (6) is printed over share vectors $q\ge0$ with $\sum_iq_i\le1$; it is stated over markups, through the paper's one-to-one map between $m$ and $q$ (p.9). Shares with some $q_i=0$ have no markup and are not represented. $b>0$ is the paper's assumption that $v_i$ decreases in the markup (p.7).
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §3, p.7 ($v_i$ decreasing), p.9 ($\pi$, $g$, $L$, problem (6)); §4, p.10 ($v_i=a_i-bc_i-bm_i$, (7), (8))

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_LogitChoice

namespace RiskBalancingMNL

/-- Data of the MNL model with symmetric price sensitivity, Li & Webster, *Optimizing
Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), §4, p.10:
`n` products with quality parameters `a i`, unit costs `c i`, and one price coefficient `b`, so
that the nominal utility of product `i` at markup `m i` is `v i = a i − b c i − b m i`.

**Formalization Note** `b > 0` is the paper's standing assumption that `vᵢ(·)` is a decreasing
function of the markup (§3, p.7). The products are indexed by `Fin n`; `a` and `c` carry no sign
assumption, as on p.10. -/
structure Params (n : ℕ) where
  a : Fin n → ℝ
  c : Fin n → ℝ
  b : ℝ
  hb : 0 < b

variable {n : ℕ}

/-- The attraction `e^{vᵢ(mᵢ)} = e^{aᵢ − bcᵢ − bmᵢ}` of product `i` under the markup vector `m`
(SSRN 3959428, §4, p.10). -/
noncomputable def attraction (P : Params n) (m : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (P.a i - P.b * P.c i - P.b * m i)

/-- The MNL choice probability (7), SSRN 3959428, p.10:
`qᵢ = e^{vᵢ(mᵢ)} / (1 + Σⱼ e^{vⱼ(mⱼ)})`, the platform's finite logit share applied to the
attractions. -/
noncomputable def share (P : Params n) (m : Fin n → ℝ) (i : Fin n) : ℝ :=
  FlagshipMEA.Monopoly.logitShare (attraction P m) i

/-- The no-purchase probability (8), SSRN 3959428, p.10: `q₀ = 1 / (1 + Σⱼ e^{vⱼ(mⱼ)})`. -/
noncomputable def noPurchase (P : Params n) (m : Fin n → ℝ) : ℝ :=
  1 / (1 + ∑ j, attraction P m j)

/-- The expected profit per customer `π = Σᵢ mᵢ qᵢ` (SSRN 3959428, §3, p.9, and (2), p.8). -/
noncomputable def profit (P : Params n) (m : Fin n → ℝ) : ℝ :=
  ∑ i, m i * share P m i

/-- `g = Σᵢ mᵢ² qᵢ` (SSRN 3959428, §3, p.9). -/
noncomputable def spread (P : Params n) (m : Fin n → ℝ) : ℝ :=
  ∑ i, m i ^ 2 * share P m i

/-- The risk-balancing objective `L = π² − λ g` (SSRN 3959428, §3, p.9), with risk weight
`lam` (the paper's `λ ∈ [0, 1)` of (5)). -/
noncomputable def objective (P : Params n) (lam : ℝ) (m : Fin n → ℝ) : ℝ :=
  profit P m ^ 2 - lam * spread P m

/-- Feasibility in problem (6), SSRN 3959428, p.9: nonnegative expected profit `π ≥ 0`.

**Formalization Note** (6) is written over share vectors `q ≥ 0` with `Σ qᵢ ≤ 1`; through the
paper's one-to-one map between markups and shares (p.9) it is stated over markup vectors
`m ∈ ℝⁿ`, which produce exactly the shares with every `qᵢ > 0` and `Σ qᵢ < 1`. Share vectors
with some `qᵢ = 0` have no markup `mᵢ(q)` (the formula on p.10 takes `log qᵢ`), so they are not
represented. -/
def Feasible (P : Params n) (m : Fin n → ℝ) : Prop :=
  0 ≤ profit P m

/-- `m` is an optimal solution of problem (6) with risk weight `lam`, SSRN 3959428, p.9: it is
feasible and its objective is at least that of every feasible markup vector.

**Formalization Note** The comparison is over all of `ℝⁿ` under `π ≥ 0`, not over equal-markup
vectors, so the equal-markup property is a theorem, not an assumption. Optimality is attainment. -/
def IsOptimal (P : Params n) (lam : ℝ) (m : Fin n → ℝ) : Prop :=
  Feasible P m ∧ ∀ m' : Fin n → ℝ, Feasible P m' → objective P lam m' ≤ objective P lam m

/-- The equal-markup vector `(t, …, t)` (SSRN 3959428, Lemma 1 and (9), pp.10–11). -/
def constM (t : ℝ) : Fin n → ℝ := fun _ => t

end RiskBalancingMNL


