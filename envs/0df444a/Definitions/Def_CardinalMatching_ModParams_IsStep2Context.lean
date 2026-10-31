-- Prove2me | Definitions.Def_CardinalMatching_ModParams_IsStep2Context
-- name    : CardinalMatching_ModParams_IsStep2Context
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:56.603002+00:00
-- url     : https://prove2.me/theorems/5f5bad2f-582d-44cb-be63-523b75c4b8f2
-- title:
--   Step 2 context: EF+PO allocation, welfare weights, optimal dual, budgets
-- statement:
--   Fix admissible parameters of the modified instance $I'$. The **Step 2 context** consists of
--
--   1. an allocation $x\in P_{\mathrm{PM}}(I')$ that is envy-free and Pareto-optimal for $u'$;
--   2. weights $\alpha_i>0$ ($i\in A'$) such that $x$ maximizes $\varphi(y)=\sum_{i\in A'}\alpha_i u'_i\cdot y_i$ over $P_{\mathrm{PM}}(I')$ (they exist by Lemma 6);
--   3. an optimal solution $(p,q)$ with $p,q\ge 0$ of the dual linear program
--   $$
--   \min \sum_{i\in A'} q_i+\sum_{j\in G'}p_j\quad\text{s.t.}\quad q_i+p_j\ge \alpha_i u'_{ij}\ \ \forall i\in A', j\in G'.
--   $$
--
--   The **budget** of agent $i$ is $b_i = \alpha_i\, u'_i\cdot x_i - q_i$. After Lemma 16, all of $\alpha,p,q,b$ are **rescaled** so that the maximum budget of a non-dummy agent is exactly $1$ (`IsRescaled`).
--
--   Every such $x$, $\alpha$ and $(p,q)$ is allowed; Lemmas 13–24 are stated for all of them.
--
--   **Formalization Note** The dual's optimality is against all feasible $(p',q')$ of any sign, as in the printed dual. The paper's $x$ is rational; here any real EF+PO allocation is allowed.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Step 2, pp.8–9; rescaling after Lemma 16, p.10

import Mathlib
import Definitions.Def_CardinalMatching_ModParams
import Definitions.Def_CardinalMatching_IsFracPerfectMatching
import Definitions.Def_CardinalMatching_IsEnvyFree
import Definitions.Def_CardinalMatching_IsParetoOptimal
import Definitions.Def_CardinalMatching_weightedWelfare

namespace CardinalMatching

namespace ModParams

variable {n : ℕ} (P : ModParams n)

/-- **Optimal dual solution** `(p, q)` of the weighted-welfare LP on `I′` (Tröbst–Vazirani,
*Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, Step 2, p.9): it is feasible for
`min ∑_{i∈A′} q_i + ∑_{j∈G′} p_j  s.t.  q_i + p_j ≥ α_i u_ij  ∀ i ∈ A′, j ∈ G′` and its objective
is at most that of every feasible `(p', q')` (of any sign, as in the printed dual). -/
def IsOptimalDual (α : P.Agent → ℝ) (p : P.Good → ℝ) (q : P.Agent → ℝ) : Prop :=
  (∀ i j, α i * P.util i j ≤ q i + p j) ∧
  ∀ (p' : P.Good → ℝ) (q' : P.Agent → ℝ), (∀ i j, α i * P.util i j ≤ q' i + p' j) →
    ∑ i, q i + ∑ j, p j ≤ ∑ i, q' i + ∑ j, p' j

/-- The **budget** `b_i := α_i u_i · x_i − q_i` of agent `i` (Step 2, p.9). -/
noncomputable def budget (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ) (q : P.Agent → ℝ) (i : P.Agent) : ℝ :=
  α i * ∑ j, P.util i j * x i j - q i

/-- **The running context of Steps 2–5** (Tröbst–Vazirani, arXiv:2402.08851v6, pp.8–9):
admissible parameters of `I′` (with correction C1, see `Admissible`); an EF+PO allocation `x` of
`I′` ("assume that we are given a rational EF+PO allocation x on I′", p.8); positive weights
`α` such that `x` maximizes `φ(y) = ∑_{i∈A′} α_i u_i · y_i` over `P_PM(I′)` (Lemma 6, p.9); and an
optimal dual solution `(p, q)` with `p, q ≥ 0` ("we may assume p, q ≥ 0", p.9).

**Formalization Note** Every such `x`, `α`, `(p, q)` is allowed (nothing is fixed by choice).
`x` may be any real EF+PO allocation; the paper's is rational. -/
def IsStep2Context (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ) (p : P.Good → ℝ)
    (q : P.Agent → ℝ) : Prop :=
  P.Admissible ∧ IsFracPerfectMatching x ∧ IsEnvyFree P.util x ∧ IsParetoOptimal P.util x ∧
    (∀ i, 0 < α i) ∧
    (∀ y, IsFracPerfectMatching y → weightedWelfare α P.util y ≤ weightedWelfare α P.util x) ∧
    P.IsOptimalDual α p q ∧ (∀ j, 0 ≤ p j) ∧ ∀ i, 0 ≤ q i

/-- **The rescaling after Lemma 16** (p.10): "we can rescale all α, p, q, and b so that the
maximum budget of any non-dummy agent is exactly 1. In the remainder of this section, we assume
that this is the case." -/
def IsRescaled (x : P.Agent → P.Good → ℝ) (α : P.Agent → ℝ) (q : P.Agent → ℝ) : Prop :=
  (∀ i, ¬ P.IsDummy i → P.budget x α q i ≤ 1) ∧ ∃ i, ¬ P.IsDummy i ∧ P.budget x α q i = 1

end ModParams

end CardinalMatching


