-- Prove2me | Definitions.Def_HetExponomial_ChoiceProb_Supplement_Model
-- name    : HetExponomial_ChoiceProb_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T17:34:49.542738+00:00
-- url     : https://prove2.me/theorems/88347667-669d-4b43-a75e-1242b30948f3
-- title:
--   §2.2–§6, pp. 8–32 — partial derivatives, adjacency, consumer surplus, outside option, monopoly and oligopoly pricing, τ_i (12)–(13), equilibrium procedures
-- statement:
--   **Objects of the supplement to the HEC mission.** This file builds on the published HEC model (the error law, the choice probability $Q_i(\mathbf u,\boldsymbol\lambda)$, $B_i$, $W_i^-$, $L_i$, $L_i^+$, $G_i$) and defines the objects that the paper's later results use.
--
--   1. The **partial derivative** $\partial f/\partial u_j$ at $\mathbf u$: the derivative of $t\mapsto f(u_1,\dots,u_{j-1},t,u_{j+1},\dots,u_n)$ at $t=u_j$.
--   2. The non-strict **worse set** $W_i=\{k\in N: u_k\le u_i\}$ (p. 6) and **adjacency** (Definition 1, p. 9): distinct $i\ne j$ with $u_i\le u_j$ are adjacent if no other choice $k$ has $u_i<u_k<u_j$.
--   3. The **expected consumer surplus** (§3.2, p. 11)
--   $$
--   CS(\mathbf u,\boldsymbol\lambda)=E\Big[\max_{i\in N}(u_i-z_i)\Big].
--   $$
--   4. The **deterministic outside option** of §3.4 (p. 14) with utility $u_0$: $Q_i(\mathbf u^+,\boldsymbol\lambda)=P\{u_i-z_i\ge u_0\text{ and }u_i-z_i\ge u_j-z_j\ \forall j\ne i\}$, $Q_0(\mathbf u^+,\boldsymbol\lambda)=P\{u_0\ge u_j-z_j\ \forall j\in N\}$, $G_0=\exp[-\sum_{j\in N}\lambda_j(u_j-u_0)]$, and the total error rate $L=\sum_{k\in N}\lambda_k$.
--   5. **Pricing** (§5, §6): ideal utilities $u_i=\alpha_i-\beta p_i$; the monopolist's revenue $R(\mathbf p)=\sum_{i=1}^n p_iQ_i(\mathbf p)$ (10) and its optimal price vectors (maximizers of $R$ over all real price vectors with $p_l=0$ for the outside option $l$); firm $i$'s oligopoly revenue $R_i=p_iQ_i$; and a **Nash equilibrium in prices**: all $p_i\ge 0$, and no firm gains by a unilateral change to another nonnegative price.
--   6. The ratio (12) $\tau_i(\mathbf u)=Q_i(\mathbf u)\big/\tfrac{\partial Q_i(\mathbf u)}{\partial u_i}$; $M=\max_j\alpha_j$; the conditional ratio (13) $\tau_i(u_i\mid u(S))$, which is $\tau_i$ at the vector whose coordinate $i$ is $u_i$, whose solved coordinates $k\in S$ are $u^*_k$, and whose other coordinates are $M$; and the prices $p^*_i=(\alpha_i-u^*_i)/\beta$.
--   7. The three equilibrium procedures: a **run of the algorithm of Theorem 10** (a solving order $k_1,\dots,k_n$ with values $u^*_{k_t}$: at step 1 the product minimizing $\alpha_i-1/(L-\lambda_i)$ is fixed at that value; at each later step every unsolved product has a candidate solving $\alpha_i-u=\tau_i(u\mid u(S))$ and a minimizing candidate is fixed); the **one-pass procedure of Theorem 11** along a given order (first product at $\alpha-1/(L-\lambda)$, each later product solving its conditional FOC (13) given the earlier ones); and **solving (12) in a given order** (Theorem 12), where every product, the first included, solves its conditional FOC (13) given the earlier ones.
--
--   **Formalization Note** Choices are `Fin n` (0-based). The partial derivative is Mathlib's `deriv` of the coordinate restriction (which is $0$ where the derivative does not exist; Theorem 2 shows it exists everywhere). $CS$ is the Bochner integral of `⨆ i, u i - z i` under the published error law. $M$ is the real supremum `⨆ j, α j` over the finite nonempty index set (every theorem assumes $n\ge 2$). A solving order is an equivalence `σ : Fin n ≃ Fin n`, with `σ s` the product solved at step $s+1$; the solved set before step $s+1$ is `solvedBefore σ s` $=\{\sigma 0,\dots,\sigma(s-1)\}$.
-- source:
--   Alptekinoğlu & Semple, Heteroscedastic Exponomial Choice, SSRN 3232788 (version of August 8, 2020; forthcoming in Operations Research), p. 6 (W_i, L); p. 9, Definition 1; p. 11, §3.2 (CS); p. 14, §3.4; p. 24, (10); p. 27, (12); p. 29, (13); pp. 30–32, Theorems 10–12 (procedures)

import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb.Supplement

open MeasureTheory ProbabilityTheory HetExponomial.ChoiceProb

variable {n : ℕ}

/-! ## Choice-level objects (§2.2–§3.4) -/

/-- The partial derivative `∂f/∂u_j` at `u`: the derivative of `t ↦ f(u_1, …, t, …, u_n)`
(`t` in coordinate `j`) at `t = u_j` (Theorem 2, p. 8; (12), p. 27). -/
noncomputable def partialU (f : (Fin n → ℝ) → ℝ) (j : Fin n) (u : Fin n → ℝ) : ℝ :=
  deriv (fun t => f (Function.update u j t)) (u j)

/-- `W_i = {k ∈ N : u_k ≤ u_i}` (p. 6), the non-strict "worse" set used in (5). -/
noncomputable def worse (u : Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => u k ≤ u i)

/-- Definition 1 (p. 9): two distinct choices `i ≠ j` with `u_i ≤ u_j` are adjacent if no other
choice `k ∉ {i, j}` has `u_i < u_k < u_j`. -/
def Adjacent (u : Fin n → ℝ) (i j : Fin n) : Prop :=
  i ≠ j ∧ u i ≤ u j ∧ ¬ ∃ k, k ≠ i ∧ k ≠ j ∧ u i < u k ∧ u k < u j

/-- Expected consumer surplus `CS(u, λ) = E[max_{i ∈ N} (u_i − z_i)]` under the error law
(§3.2, p. 11). -/
noncomputable def consumerSurplus (u lam : Fin n → ℝ) : ℝ :=
  ∫ z, (⨆ i, (u i - z i)) ∂(errorLaw lam)

/-- With a deterministic outside option of utility `u₀` (§3.4, p. 14):
`Q_i(u⁺, λ) = P{u_i − z_i ≥ u₀ and u_i − z_i ≥ u_j − z_j ∀ j ∈ N, j ≠ i}`. -/
noncomputable def choiceProbOut (u₀ : ℝ) (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  (errorLaw lam {z | u₀ ≤ u i - z i ∧ ∀ j, j ≠ i → u j - z j ≤ u i - z i}).toReal

/-- `Q_0(u⁺, λ) = P{u₀ ≥ u_j − z_j ∀ j ∈ N}`, the probability of the outside option (p. 14). -/
noncomputable def outsideProb (u₀ : ℝ) (u lam : Fin n → ℝ) : ℝ :=
  (errorLaw lam {z | ∀ j, u j - z j ≤ u₀}).toReal

/-- `G_0(u⁺, λ) = exp[−∑_{j ∈ N} λ_j (u_j − u₀)]` (p. 14). -/
noncomputable def G0 (u₀ : ℝ) (u lam : Fin n → ℝ) : ℝ :=
  Real.exp (-(∑ j, lam j * (u j - u₀)))

/-- The total error rate `L = ∑_{k ∈ N} λ_k` (pp. 6, 14, 27). -/
noncomputable def Ltot (lam : Fin n → ℝ) : ℝ :=
  ∑ k, lam k

/-! ## Pricing (§5, §6, Appendix A) -/

/-- Linear ideal utilities `u_i(p_i) = α_i − β p_i` (pp. 24, 27). -/
def util (α : Fin n → ℝ) (β : ℝ) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => α i - β * p i

/-- The monopolist's expected revenue `R(p) = ∑_{i=1}^n p_i Q_i(p)`, (10), p. 24
(the sum includes the outside option, whose price is `0`). -/
noncomputable def revenue (α : Fin n → ℝ) (β : ℝ) (lam p : Fin n → ℝ) : ℝ :=
  ∑ i, p i * choiceProb (util α β p) lam i

/-- `p` is an optimal monopoly price vector (§5, p. 24): `p_l = 0` for the outside option `l`, and
`R(q) ≤ R(p)` for every real price vector `q` with `q_l = 0`. -/
def IsOptimalMonopolyPrice (α : Fin n → ℝ) (β : ℝ) (lam : Fin n → ℝ) (l : Fin n)
    (p : Fin n → ℝ) : Prop :=
  p l = 0 ∧ ∀ q : Fin n → ℝ, q l = 0 → revenue α β lam q ≤ revenue α β lam p

/-- Firm `i`'s expected revenue in the oligopoly, `R_i = p_i · Q_i` (p. 27). -/
noncomputable def firmRevenue (α : Fin n → ℝ) (β : ℝ) (lam p : Fin n → ℝ) (i : Fin n) : ℝ :=
  p i * choiceProb (util α β p) lam i

/-- A Nash equilibrium in prices of the `n`-firm oligopoly (§6, p. 27): every price is
nonnegative (`u_i ≤ α_i`), and no firm can raise its revenue by a unilateral change to another
nonnegative price. -/
def IsPriceNE (α : Fin n → ℝ) (β : ℝ) (lam p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧
    ∀ i (q : ℝ), 0 ≤ q → firmRevenue α β lam (Function.update p i q) i ≤ firmRevenue α β lam p i

/-- The ratio `τ_i(u) = Q_i(u) / (∂Q_i(u)/∂u_i)`, (12), p. 27. -/
noncomputable def tau (u lam : Fin n → ℝ) (i : Fin n) : ℝ :=
  choiceProb u lam i / partialU (fun v => choiceProb v lam i) i u

/-- `M = max_{j ∈ N} α_j` (Step 1 of Theorem 10, p. 30; p. 29). -/
noncomputable def maxAlpha (α : Fin n → ℝ) : ℝ :=
  ⨆ j, α j

/-- The vector at which `τ_i(u_i | u(S))` is evaluated, (13), p. 29: coordinate `i` is `x`, a
solved product `k ∈ S` has its solved value `u*_k`, every other product has `M`. -/
noncomputable def condVec (α : Fin n → ℝ) (S : Finset (Fin n)) (ustar : Fin n → ℝ) (i : Fin n)
    (x : ℝ) : Fin n → ℝ :=
  fun j => if j = i then x else if j ∈ S then ustar j else maxAlpha α

/-- `τ_i(x | u(S))`, (13), p. 29. -/
noncomputable def tauCond (α lam : Fin n → ℝ) (S : Finset (Fin n)) (ustar : Fin n → ℝ) (i : Fin n)
    (x : ℝ) : ℝ :=
  tau (condVec α S ustar i x) lam i

/-- The products solved before step `t` (0-based) of an order `σ`: `{σ s : s < t}`. -/
def solvedBefore (σ : Fin n ≃ Fin n) (t : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun s : Fin n => s.val < t)).image σ

/-- The prices `p*_i = (α_i − u*_i)/β` of Step 4 (pp. 30, 32). -/
noncomputable def eqPrices (α : Fin n → ℝ) (β : ℝ) (ustar : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (α i - ustar i) / β

/-- A run of the algorithm of Theorem 10 (p. 30). The product fixed at step `s + 1` is `σ s`,
with value `u*_{σ s}`. Step 2 (`s = 0`): `σ 0` minimises `u¹_i = α_i − 1/(L − λ_i)` over `N` and
`u*_{σ 0} = u¹_{σ 0}`. Step 3 (`s ≥ 1`, `S = {σ 0, …, σ (s−1)}`): there are candidates `u^t_i`,
`i ∉ S`, solving `α_i − u^t_i = τ_i(u^t_i | u(S))`, `σ s` minimises them over `N ∖ S`, and
`u*_{σ s} = u^t_{σ s}`. -/
def IsGeneralRun (α lam : Fin n → ℝ) (σ : Fin n ≃ Fin n) (ustar : Fin n → ℝ) : Prop :=
  ∀ s : Fin n,
    (s.val = 0 →
        (∀ i, α (σ s) - 1 / (Ltot lam - lam (σ s)) ≤ α i - 1 / (Ltot lam - lam i)) ∧
          ustar (σ s) = α (σ s) - 1 / (Ltot lam - lam (σ s))) ∧
      (0 < s.val →
        ∃ c : Fin n → ℝ,
          (∀ i, i ∉ solvedBefore σ s.val →
              α i - c i = tauCond α lam (solvedBefore σ s.val) ustar i (c i)) ∧
            (∀ i, i ∉ solvedBefore σ s.val → c (σ s) ≤ c i) ∧ ustar (σ s) = c (σ s))

/-- The one-pass procedure of Theorem 11 (pp. 31–32) along the order `σ` (`σ 0` is the paper's
product 1): `u*_{σ 0} = α_{σ 0} − 1/(L − λ_{σ 0})` (Step 2), and for `s ≥ 1`, `u*_{σ s}` solves
`α_{σ s} − u = τ_{σ s}(u | u(S))` with `S = {σ 0, …, σ (s−1)}` (Step 3). -/
def IsOnePass (α lam : Fin n → ℝ) (σ : Fin n ≃ Fin n) (ustar : Fin n → ℝ) : Prop :=
  ∀ s : Fin n,
    (s.val = 0 → ustar (σ s) = α (σ s) - 1 / (Ltot lam - lam (σ s))) ∧
      (0 < s.val →
        α (σ s) - ustar (σ s) = tauCond α lam (solvedBefore σ s.val) ustar (σ s) (ustar (σ s)))

/-- "Solving (12) in that order" (Theorem 12, p. 32): along `σ`, each `u*_{σ s}` solves the
conditional first-order condition (13), `α_{σ s} − u = τ_{σ s}(u | u(S))` with
`S = {σ 0, …, σ (s−1)}` (for `s = 0`, `S = ∅`). -/
def IsSequentialFOC (α lam : Fin n → ℝ) (σ : Fin n ≃ Fin n) (ustar : Fin n → ℝ) : Prop :=
  ∀ s : Fin n,
    α (σ s) - ustar (σ s) = tauCond α lam (solvedBefore σ s.val) ustar (σ s) (ustar (σ s))

end HetExponomial.ChoiceProb.Supplement


