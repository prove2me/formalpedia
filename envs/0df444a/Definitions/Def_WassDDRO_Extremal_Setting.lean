-- Prove2me | Definitions.Def_WassDDRO_Extremal_Setting
-- name    : WassDDRO_Extremal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:44:13.701338+00:00
-- url     : https://prove2.me/theorems/a45dd182-4e44-4fe8-bb3c-1ff039fb0897
-- title:
--   Notation p. 5, (10), Assumption 4.1, (12f), (13), Theorem 4.4 — extended expectation, worst-case expectation, conjugate, program (13) and the distributions Q_r
-- statement:
--   This file fixes the objects of Mohajerin Esfahani and Kuhn's analysis of worst-case distributions over a Wasserstein ball.
--
--   Let $E$ be a finite-dimensional real normed space (the paper's $\mathbb R^m$ with an arbitrary norm $\|\cdot\|$), equipped with its Borel $\sigma$-algebra, and write $\overline{\mathbb R} = [-\infty, +\infty]$. Fix samples $\hat\xi_1, \dots, \hat\xi_N \in E$, a closed set $\Xi \subseteq E$, a radius $\varepsilon$, and functions $\ell_1, \dots, \ell_K : E \to \overline{\mathbb R}$.
--
--   1. **Extended expectation** (Notation, p. 5). For a measure $\mathbb Q$ and $\ell : E \to \overline{\mathbb R}$,
--   $$\mathbb E^{\mathbb Q}[\ell(\xi)] = \mathbb E^{\mathbb Q}[\max\{\ell(\xi),0\}] + \mathbb E^{\mathbb Q}[\min\{\ell(\xi),0\}],$$
--   with the convention $\infty - \infty = \infty$: the value is $+\infty$ whenever the positive part has infinite integral. This is the published definition `DupacovaWets.Consistency.expect`, which is used here and not redefined.
--   2. **Worst-case expectation** (10): $\sup_{\mathbb Q \in \mathbb B_\varepsilon(\widehat{\mathbb P}_N)} \mathbb E^{\mathbb Q}[\ell(\xi)]$, where $\mathbb B_\varepsilon(\widehat{\mathbb P}_N)$ is the ball (6) of probability measures supported on $\Xi$ at type-1 Wasserstein distance at most $\varepsilon$ from the empirical distribution $\widehat{\mathbb P}_N = \frac1N\sum_i \delta_{\hat\xi_i}$.
--   3. **Piecewise loss** (p. 11): $\ell(\xi) = \max_{k \le K} \ell_k(\xi)$.
--   4. **Conjugate restricted to a set** (p. 5): $f^*_S(z) = \sup_{\xi \in S} \langle z, \xi\rangle - f(\xi)$ for a linear functional $z$; with $S = E$ this is the conjugate $f^*$, and with $S = \Xi$ it is $[f + \chi_\Xi]^*$. Also the support function $\sigma_\Xi(z) = \sup_{\xi\in\Xi}\langle z,\xi\rangle$.
--   5. **Assumption 4.1** (p. 11): $\Xi$ is convex and closed; each $-\ell_k$ is proper, convex and lower semicontinuous; and each $\ell_k$ is not identically $-\infty$ on $\Xi$.
--   6. **Program (12f)** (p. 13): the value of
--   $$\inf_{\lambda, s_i, z_{ik}} \lambda\varepsilon + \frac1N\sum_{i=1}^N s_i \quad\text{s.t.}\quad [-\ell_k + \chi_\Xi]^*(z_{ik}) - \langle z_{ik}, \hat\xi_i\rangle \le s_i,\quad \|z_{ik}\|_* \le \lambda .$$
--   7. **Program (13)** (p. 14): the value of
--   $$\sup_{\alpha_{ik}, q_{ik}} \frac1N\sum_{i=1}^N\sum_{k=1}^K \alpha_{ik}\,\ell_k\Big(\hat\xi_i - \frac{q_{ik}}{\alpha_{ik}}\Big)\quad\text{s.t.}\quad \frac1N\sum_{i,k}\|q_{ik}\| \le \varepsilon,\ \ \sum_{k}\alpha_{ik} = 1,\ \ \alpha_{ik}\ge 0,\ \ \hat\xi_i - \frac{q_{ik}}{\alpha_{ik}} \in \Xi,$$
--   read with the paper's conventions: if $\alpha_{ik} = 0$ the constraint $\hat\xi_i - q_{ik}/\alpha_{ik} \in \Xi$ forces $q_{ik} = 0$, and the $ik$-th objective term is $0$.
--   8. **The discrete distributions** of Theorem 4.4: $\mathbb Q = \frac1N\sum_{i=1}^N\sum_{k=1}^K \alpha_{ik}\,\delta_{\xi_{ik}}$ with $\xi_{ik} = \hat\xi_i - q_{ik}/\alpha_{ik}$.
--
--   These objects are the vocabulary of Theorem 4.4: the worst-case expectation (10) equals the value of (13), and near-optimal points of (13) give near-worst-case distributions.
--
--   **Formalization Note** The dual space is `StrongDual ℝ E`, $\langle z, \xi\rangle$ is `z ξ`, and the dual norm $\|z\|_*$ is the operator norm. All values are in `EReal`; program values are infima/suprema over feasibility predicates, so an empty feasible set gives $+\infty$ (infimum) or $-\infty$ (supremum). Program (12f) uses real epigraph variables $s_i$ so its objective is real. The atom $\hat\xi_i - q_{ik}/\alpha_{ik}$ is `ξh - α⁻¹ • q` and is only used when $\alpha_{ik} \neq 0$; the $\alpha_{ik} = 0$ case is handled by the explicit clauses `α = 0 → q = 0` and `term13 = 0`. The objective of (13) adds `EReal` terms that are never $+\infty$ when no $\ell_k$ takes the value $+\infty$ (as under Assumption 4.1), so Mathlib's $\top + \bot = \bot$ never arises. The Wasserstein distance, the ball (6) and $\widehat{\mathbb P}_N$ are the published `WassersteinDRO.Duality` definitions with $p = 1$; the expectation is the published `DupacovaWets.Consistency.expect`.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Notation p. 5; (3) p. 6; Definition 3.1 and (6) p. 7; (10) and Assumption 4.1 p. 11; (12f) p. 13; Theorem 4.4 and (13) p. 14

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory

namespace WassDDRO.Extremal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- (10): sup_{Q ∈ B_ε(P̂_N)} E^Q[ℓ(ξ)], with the expectation of p. 5
(E^Q[max{ℓ,0}] + E^Q[min{ℓ,0}], ∞ − ∞ = ∞), which is the published `DupacovaWets.Consistency.expect`. -/
noncomputable def worstCaseExpectation (ε : ℝ) (Ξ : Set E) {N : ℕ} (ξhat : Fin N → E)
    (ℓ : E → EReal) : EReal :=
  ⨆ Q ∈ WassersteinDRO.Duality.ambiguitySet ε 1 Ξ
      (WassersteinDRO.Duality.empiricalDistribution ξhat), DupacovaWets.Consistency.expect Q ℓ

/-- p. 11: ℓ(ξ) := max_{k≤K} ℓ_k(ξ). -/
noncomputable def maxLoss {K : ℕ} (ℓ : Fin K → E → EReal) : E → EReal := fun ξ => ⨆ k, ℓ k ξ

/-- p. 5: f*(z) := sup_ξ ⟨z, ξ⟩ − f(ξ), restricted to ξ ∈ S. With S = Ξ this is [f + χ_Ξ]*(z)
under the paper's convention f + ∞ = ∞ (pp. 13–14); with S = univ it is f*. -/
noncomputable def conjOn (S : Set E) (f : E → EReal) (z : StrongDual ℝ E) : EReal :=
  ⨆ ξ ∈ S, ((z ξ : ℝ) : EReal) - f ξ

/-- p. 5: σ_Ξ(z) := sup_{ξ ∈ Ξ} ⟨z, ξ⟩. -/
noncomputable def supportFun (Ξ : Set E) (z : StrongDual ℝ E) : EReal :=
  ⨆ ξ ∈ Ξ, ((z ξ : ℝ) : EReal)

/-- Assumption 4.1 (p. 11). -/
structure Assumption41 {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal) : Prop where
  convex : Convex ℝ Ξ
  closed : IsClosed Ξ
  ne_top : ∀ k ξ, ℓ k ξ ≠ ⊤                            -- −ℓ_k > −∞ (proper)
  convex_epigraph : ∀ k, Convex ℝ {p : E × ℝ | -ℓ k p.1 ≤ (p.2 : EReal)}   -- −ℓ_k convex
  lsc : ∀ k, LowerSemicontinuous (fun ξ => -ℓ k ξ)      -- −ℓ_k lsc
  not_bot_on : ∀ k, ∃ ξ ∈ Ξ, ℓ k ξ ≠ ⊥                -- ℓ_k not identically −∞ on Ξ

/-- (12f) (p. 13): inf λε + (1/N) Σ sᵢ s.t. [−ℓ_k + χ_Ξ]*(z_ik) − ⟨z_ik, ξ̂ᵢ⟩ ≤ sᵢ, ‖z_ik‖_* ≤ λ. -/
noncomputable def program12fValue {K N : ℕ} (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E)
    (ℓ : Fin K → E → EReal) : EReal :=
  ⨅ (lam : ℝ) (s : Fin N → ℝ) (z : Fin N → Fin K → StrongDual ℝ E)
    (_ : ∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k) - ((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal))
    (_ : ∀ i k, ‖z i k‖ ≤ lam),
    ((lam * ε + (1 / (N : ℝ)) * ∑ i, s i : ℝ) : EReal)

/-- The atom ξ̂ᵢ − q_ik/α_ik of (13) (used only when α_ik ≠ 0). -/
noncomputable def atom13 (ξh : E) (α : ℝ) (q : E) : E := ξh - α⁻¹ • q

/-- The ik-th objective term α_ik ℓ_k(ξ̂ᵢ − q_ik/α_ik) of (13), = 0 when α_ik = 0 (p. 14). -/
noncomputable def term13 (ℓk : E → EReal) (ξh : E) (α : ℝ) (q : E) : EReal :=
  if α = 0 then 0 else (α : EReal) * ℓk (atom13 ξh α q)

/-- The constraints of (13), with the α_ik = 0 convention of p. 14. -/
def Feasible13 {K N : ℕ} (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) : Prop :=
  (1 / (N : ℝ)) * ∑ i, ∑ k, ‖q i k‖ ≤ ε ∧ (∀ i, ∑ k, α i k = 1) ∧ (∀ i k, 0 ≤ α i k) ∧
    ∀ i k, (α i k = 0 → q i k = 0) ∧ (α i k ≠ 0 → atom13 (ξhat i) (α i k) (q i k) ∈ Ξ)

/-- The objective of (13): (1/N) Σᵢ Σ_k α_ik ℓ_k(ξ̂ᵢ − q_ik/α_ik). -/
noncomputable def objective13 {K N : ℕ} (ξhat : Fin N → E) (ℓ : Fin K → E → EReal)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) : EReal :=
  ((1 / (N : ℝ) : ℝ) : EReal) * ∑ i, ∑ k, term13 (ℓ k) (ξhat i) (α i k) (q i k)

/-- The optimal value of (13). -/
noncomputable def program13Value {K N : ℕ} (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E)
    (ℓ : Fin K → E → EReal) : EReal :=
  ⨆ (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) (_ : Feasible13 ε Ξ ξhat α q),
    objective13 ξhat ℓ α q

/-- Q_r := (1/N) Σᵢ Σ_k α_ik δ_{ξ_ik} (Theorem 4.4). -/
noncomputable def discreteQ {K N : ℕ} (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ)
    (q : Fin N → Fin K → E) : Measure E :=
  (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (α i k) • Measure.dirac (atom13 (ξhat i) (α i k) (q i k))

end WassDDRO.Extremal


