-- Prove2me | Definitions.Def_ProgHedging_Nonconvex_Algorithm
-- name    : ProgHedging_Nonconvex_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:18.920275+00:00
-- url     : https://prove2.me/theorems/af4961d9-4367-4270-8187-b58e910e5571
-- title:
--   Locally optimal progressive hedging, the optimality conditions of Theorem 4.1, and the objects F^ν, δ′, f̃_s of §6 (pp. 9, 14–15, 30–31)
-- statement:
--   This file defines the objects of the nonconvex analysis of progressive hedging. Throughout, $\partial g(x)$ is **Clarke's generalized gradient** of $g:\mathbb R^n\to\mathbb R$ at $x$ and $N_C(x)$ is **Clarke's normal cone** to a closed set $C$ at $x$; $\langle\cdot,\cdot\rangle$, $\|\cdot\|$, $J$, $K$, $\mathcal N$, $\mathcal M$, $\mathcal C$, $F$ are those of the scenario model, the shared definition `ProgHedging.Convex.Problem` (§§1–3, with the standing assumptions of §3 and no convexity), which this file names `Problem` in its own namespace by an abbreviation.
--
--   1. **Optimality conditions of Theorem 4.1.** A pair of policies $(X^*,W^*)$ satisfies them when $X^*\in\mathcal N$, $X^*\in\mathcal C$, $W^*\in\mathcal M$ and
--   $$-W^*(s)\in\partial f_s(X^*(s))+N_{C_s}(X^*(s))\qquad\text{for all } s\in S .$$
--   2. **Locally optimal progressive hedging.** Fix $r>0$ and $\delta>0$. Sequences $(X^\nu)_{\nu\ge0}$, $(W^\nu)_{\nu\ge0}$ of policies are a run of the algorithm with $\delta$-locally optimal subproblem solutions when $X^0\in\mathcal C$, $W^0\in\mathcal M$ and, for every $\nu$:
--      - for every $s$, $X^{\nu+1}(s)\in C_s$ and $X^{\nu+1}(s)$ is optimal for
--      $$(P^\nu_s)\qquad \text{minimize } f_s(x)+x\cdot W^\nu(s)+\tfrac12 r|x-\hat X^\nu(s)|^2 \text{ over } x\in C_s,\qquad \hat X^\nu=JX^\nu,$$
--      relative to all $x\in C_s$ with $|x-X^{\nu+1}(s)|\le\delta$;
--      - $W^{\nu+1}=W^\nu+rKX^{\nu+1}$.
--   3. The objective of $(P^\nu)$: $F^\nu(X)=F(X)+\langle X,W^\nu\rangle+\tfrac12 r\|X-\hat X^\nu\|^2$ (6.3).
--   4. The radius $\delta'=\delta\min_{s\in S}p_s^{1/2}$ (6.4).
--   5. The modified scenario costs $\tilde f_s(x)=f_s(x)+\tfrac12 r|x-X^*(s)|^2$ (6.1).
--
--   These are the hypotheses and conclusions of Theorem 6.1, which asserts that a limit of such a run satisfies the optimality conditions.
--
--   **Formalization Note** The $\delta$-neighbourhood in $(P^\nu_s)$ is the closed Euclidean ball of $\mathbb R^n$. $X^0\in\mathcal C$ and $W^0\in\mathcal M$ come from the statement of the algorithm on p. 9. The condition $-W^*(s)\in\dots$ is the paper's decomposed form (4.4) of (4.3); `+` is the pointwise (Minkowski) sum of sets. In $\delta'$ the minimum over the finite, nonempty set $S$ is written as an infimum. The Clarke objects are the published definitions `ClarkeGradients.Shared.generalizedGradient` and `ClarkeGradients.FlowInvariance.normalCone`.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 9 (Progressive Hedging Algorithm), pp. 14–15 (Theorem 4.1, (4.1), (4.4)), pp. 30–31 ((6.1), (6.3), (6.4))

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_FlowInvariance_normalCone

open scoped RealInnerProductSpace Pointwise

namespace ProgHedging.Nonconvex

/-- The scenario model of §§1–3 (pp. 2–11) with the standing assumptions of §3 (p. 10): the shared
structure `ProgHedging.Convex.Problem` (no convexity is part of it). Its operators `ip`, `pnorm`,
`J`, `K`, `N`, `M`, `adm`, `F`, `ConvexCase`, `subObj` are reached by dot notation. -/
abbrev Problem (S : Type*) [Fintype S] (n T : ℕ) := ProgHedging.Convex.Problem S n T

/-- Theorem 4.1, pp. 14–15, in its decomposed form (4.1), (4.4): `X* ∈ 𝒩`, `X* ∈ 𝒞`, `W* ∈ ℳ` and
`−W*(s) ∈ ∂f_s(X*(s)) + N_{C_s}(X*(s))` for all `s ∈ S`, where `∂` is Clarke's generalized gradient
and `N_{C_s}` Clarke's normal cone (p. 14), `+` the pointwise sum of sets. -/
def Problem.OptCond41 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (Xs Ws : ProgHedging.Convex.Policy S n) : Prop :=
  Xs ∈ pr.N ∧ Xs ∈ pr.adm ∧ Ws ∈ pr.M ∧
    ∀ s, -Ws s ∈ ClarkeGradients.Shared.generalizedGradient (pr.f s) (Xs s) +
      ClarkeGradients.FlowInvariance.normalCone (pr.C s) (Xs s)

/-- The progressive hedging algorithm (p. 9) implemented as in Theorem 6.1 (p. 30): `X⁰ ∈ 𝒞`,
`W⁰ ∈ ℳ`, and in iteration `ν` the vector `X^{ν+1}(s) ∈ C_s` is `δ`-locally optimal for
`(P^ν_s)`: minimize `f_s(x) + x·W^ν(s) + ½r|x − X̂^ν(s)|²` over `x ∈ C_s`, with `X̂^ν = J X^ν`,
i.e. optimal relative to the closed Euclidean `δ`-ball around `X^{ν+1}(s)`; then
`W^{ν+1} = W^ν + r K X^{ν+1}` (Step 3). -/
def Problem.IsLocalPHSeq {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r δ : ℝ)
    (X W : ℕ → ProgHedging.Convex.Policy S n) : Prop :=
  X 0 ∈ pr.adm ∧ W 0 ∈ pr.M ∧ ∀ ν,
    (∀ s, X (ν + 1) s ∈ pr.C s ∧ ∀ z ∈ pr.C s, ‖z - X (ν + 1) s‖ ≤ δ →
      pr.subObj s (pr.J (X ν) s) (W ν s) r (X (ν + 1) s) ≤
        pr.subObj s (pr.J (X ν) s) (W ν s) r z) ∧
    W (ν + 1) = W ν + r • pr.K (X (ν + 1))

/-- (6.3), p. 31: the objective of `(P^ν)`, `F^ν(X) = F(X) + ⟨X, W⟩ + ½r‖X − V‖²` with `V = X̂^ν`,
`W = W^ν`, and `‖·‖` the norm (2.3). -/
noncomputable def Problem.Fnu {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r : ℝ)
    (V W X : ProgHedging.Convex.Policy S n) : ℝ :=
  pr.F X + pr.ip X W + r / 2 * pr.pnorm (X - V) ^ 2

/-- (6.4), p. 31: `δ′ = δ min_{s∈S} p_s^{1/2}` (`S` is finite and nonempty, so the infimum is the
minimum). -/
noncomputable def Problem.deltaPrime {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (δ : ℝ) : ℝ :=
  δ * ⨅ s, Real.sqrt (pr.p s)

/-- (6.1), p. 30: `f̃_s(x) = f_s(x) + ½r|x − X*(s)|²`. -/
noncomputable def Problem.fTilde {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) (r : ℝ)
    (Xs : ProgHedging.Convex.Policy S n) (s : S) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  pr.f s x + r / 2 * ‖x - Xs s‖ ^ 2

end ProgHedging.Nonconvex


