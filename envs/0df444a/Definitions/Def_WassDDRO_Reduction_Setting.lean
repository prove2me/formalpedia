-- Prove2me | Definitions.Def_WassDDRO_Reduction_Setting
-- name    : WassDDRO_Reduction_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:57:05.058733+00:00
-- url     : https://prove2.me/theorems/3a0e18e6-952e-4ff0-9ed0-87e297874829
-- title:
--   Notation p. 5, (10), (11), (12c), (12f), Assumption 4.1 — extended expectation, worst-case expectation, conjugate, support function, program values
-- statement:
--   This file fixes the objects of §4.1 of Mohajerin Esfahani and Kuhn. Throughout, $E$ is a finite-dimensional real normed space with its Borel σ-algebra (the paper's $(\mathbb R^m,\|\cdot\|)$ with an arbitrary norm), $\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}$ are the extended reals, and a linear functional $z\in E^*$ acts by $\langle z,\xi\rangle = z(\xi)$; its dual norm is $\|z\|_*=\sup_{\|\xi\|\le 1}\langle z,\xi\rangle$.
--
--   1. **Expectation of an extended-valued function** (Notation, p. 5). For a measure $\mathbb Q$ and $\ell:E\to\overline{\mathbb R}$,
--   $$\mathbb E^{\mathbb Q}[\ell(\xi)] = \mathbb E^{\mathbb Q}[\max\{\ell(\xi),0\}] + \mathbb E^{\mathbb Q}[\min\{\ell(\xi),0\}],$$
--   with the convention $\infty-\infty=+\infty$: the expectation is $+\infty$ whenever the positive part has infinite integral. This is the published extended expectation `DupacovaWets.Consistency.expect`, which this file uses.
--   2. **Worst-case expectation** (10). For samples $\hat\xi_1,\dots,\hat\xi_N$, a radius $\varepsilon$ and a support set $\Xi$,
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)],$$
--   where $\mathbb B_\varepsilon(\widehat{\mathbb P}_N)$ is the set of probability measures $\mathbb Q$ with $\mathbb Q(\Xi^{\mathrm c})=0$ and 1-Wasserstein distance $d_W(\mathbb Q,\widehat{\mathbb P}_N)\le\varepsilon$ to the empirical distribution $\widehat{\mathbb P}_N=\frac1N\sum_i\delta_{\hat\xi_i}$.
--   3. **Piecewise loss** (p. 11): $\ell(\xi)=\max_{k\le K}\ell_k(\xi)$.
--   4. **Conjugate restricted to a set** (p. 5): $f^*_S(z)=\sup_{\xi\in S}\,\langle z,\xi\rangle-f(\xi)$. For $S=E$ this is the conjugate $f^*$; for $S=\Xi$ it is $[f+\chi_\Xi]^*$ under the paper's convention $f+\infty=\infty$.
--   5. **Support function** (p. 5): $\sigma_\Xi(z)=\sup_{\xi\in\Xi}\langle z,\xi\rangle$.
--   6. **Assumption 4.1** (p. 11): $\Xi$ is convex and closed; each $-\ell_k$ is proper, convex and lower semicontinuous; each $\ell_k$ is not identically $-\infty$ on $\Xi$.
--   7. **Optimal values of the programs** (12c), (12f) and (11), each an infimum of the real objective $\lambda\varepsilon+\frac1N\sum_{i=1}^N s_i$ over its feasible set:
--      - (12c): over $\lambda\ge 0$, $s\in\mathbb R^N$ with $\sup_{\xi\in\Xi}\big(\ell(\xi)-\lambda\|\xi-\hat\xi_i\|\big)\le s_i$ for all $i$;
--      - (12f): over $\lambda$, $s$ and $z_{ik}\in E^*$ with $[-\ell_k+\chi_\Xi]^*(z_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i$ and $\|z_{ik}\|_*\le\lambda$ for all $i,k$;
--      - (11): over $\lambda$, $s$, $z_{ik},\nu_{ik}\in E^*$ with $[-\ell_k]^*(z_{ik}-\nu_{ik})+\sigma_\Xi(\nu_{ik})-\langle z_{ik},\hat\xi_i\rangle\le s_i$ and $\|z_{ik}\|_*\le\lambda$ for all $i,k$.
--
--   These are the objects compared by Theorem 4.2 and its proof.
--
--   **Formalization Note** All extended values live in `EReal`. The program values are infima over a feasibility predicate, so an empty feasible set gives $+\infty$, never a junk $0$. Because Mathlib's `EReal` has $\top+\bot=\bot$ while the paper has $\infty-\infty=\infty$, the expectation (the referenced `DupacovaWets.Consistency.expect`) treats the case of an infinite positive part separately, and the objectives are real (epigraph variables $s_i$). Assumption 4.1's convexity of $-\ell_k$ is stated through its real epigraph $\{(\xi,t):-\ell_k(\xi)\le t\}$; properness is the pair "$\ell_k$ never $+\infty$" and "$\ell_k$ not identically $-\infty$ on $\Xi$". The dual norm is the operator norm on `StrongDual ℝ E`. The Wasserstein ball and empirical distribution are the published `WassersteinDRO.Duality` definitions with $p=1$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Notation p. 5, (3) p. 6, Definition 3.1 and (6) p. 7, (10) and Assumption 4.1 p. 11, (11) and (12c) p. 12, (12f) p. 13

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_ambiguitySet
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory

namespace WassDDRO.Reduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

/-- (10), p. 11: the worst-case expectation `sup_{Q ∈ B_ε(P̂_N)} E^Q[ℓ(ξ)]` over the
1-Wasserstein ball (6) of radius `ε` around the empirical distribution (3) of the samples
`ξhat`, restricted to distributions supported on `Ξ`. The expectation is the p. 5 one,
`E^Q[ℓ(ξ)] = E^Q[max{ℓ(ξ),0}] + E^Q[min{ℓ(ξ),0}]` with `∞ − ∞ = ∞`: the published
`DupacovaWets.Consistency.expect`, which is `+∞` when the positive part has infinite integral and
positive part minus negative part otherwise. -/
noncomputable def worstCaseExpectation (ε : ℝ) (Ξ : Set E) {N : ℕ} (ξhat : Fin N → E)
    (ℓ : E → EReal) : EReal :=
  ⨆ Q ∈ WassersteinDRO.Duality.ambiguitySet ε 1 Ξ
      (WassersteinDRO.Duality.empiricalDistribution ξhat),
      DupacovaWets.Consistency.expect Q ℓ

/-- p. 11: the loss `ℓ(ξ) := max_{k≤K} ℓ_k(ξ)`, the pointwise maximum of the pieces. -/
noncomputable def maxLoss {K : ℕ} (ℓ : Fin K → E → EReal) : E → EReal := fun ξ => ⨆ k, ℓ k ξ

/-- p. 5: the conjugate `f*(z) := sup_ξ ⟨z, ξ⟩ − f(ξ)`, with the supremum restricted to
`ξ ∈ S`. With `S = Ξ` this is `[f + χ_Ξ]*(z)` under the paper's convention `f + ∞ = ∞`
(pp. 13–14); with `S = univ` it is `f*`. -/
noncomputable def conjOn (S : Set E) (f : E → EReal) (z : StrongDual ℝ E) : EReal :=
  ⨆ ξ ∈ S, ((z ξ : ℝ) : EReal) - f ξ

/-- p. 5: the support function `σ_Ξ(z) := sup_{ξ ∈ Ξ} ⟨z, ξ⟩`. -/
noncomputable def supportFun (Ξ : Set E) (z : StrongDual ℝ E) : EReal :=
  ⨆ ξ ∈ Ξ, ((z ξ : ℝ) : EReal)

/-- Assumption 4.1 (Convexity), p. 11: `Ξ` is convex and closed; each `−ℓ_k` is proper,
convex and lower semicontinuous; and each `ℓ_k` is not identically `−∞` on `Ξ`. -/
structure Assumption41 {K : ℕ} (Ξ : Set E) (ℓ : Fin K → E → EReal) : Prop where
  convex : Convex ℝ Ξ
  closed : IsClosed Ξ
  ne_top : ∀ k ξ, ℓ k ξ ≠ ⊤
  convex_epigraph : ∀ k, Convex ℝ {p : E × ℝ | -ℓ k p.1 ≤ (p.2 : EReal)}
  lsc : ∀ k, LowerSemicontinuous (fun ξ => -ℓ k ξ)
  not_bot_on : ∀ k, ∃ ξ ∈ Ξ, ℓ k ξ ≠ ⊥

/-- (12c), p. 12, the epigraph form of (12b): `inf λε + (1/N) Σ sᵢ` subject to
`sup_{ξ∈Ξ} (ℓ(ξ) − λ‖ξ − ξ̂ᵢ‖) ≤ sᵢ` for all `i` and `λ ≥ 0`. An empty feasible set gives `⊤`. -/
noncomputable def program12cValue {N : ℕ} (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E)
    (ℓ : E → EReal) : EReal :=
  ⨅ (lam : ℝ) (s : Fin N → ℝ)
    (_ : ∀ i, (⨆ ξ ∈ Ξ, ℓ ξ - ((lam * ‖ξ - ξhat i‖ : ℝ) : EReal)) ≤ (s i : EReal))
    (_ : 0 ≤ lam),
    ((lam * ε + (1 / (N : ℝ)) * ∑ i, s i : ℝ) : EReal)

/-- (12f), p. 13: `inf λε + (1/N) Σ sᵢ` subject to `[−ℓ_k + χ_Ξ]*(z_ik) − ⟨z_ik, ξ̂ᵢ⟩ ≤ sᵢ`
and `‖z_ik‖_* ≤ λ` for all `i, k`. An empty feasible set gives `⊤`. -/
noncomputable def program12fValue {K N : ℕ} (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E)
    (ℓ : Fin K → E → EReal) : EReal :=
  ⨅ (lam : ℝ) (s : Fin N → ℝ) (z : Fin N → Fin K → StrongDual ℝ E)
    (_ : ∀ i k, conjOn Ξ (fun ξ => -ℓ k ξ) (z i k) - ((z i k (ξhat i) : ℝ) : EReal)
        ≤ (s i : EReal))
    (_ : ∀ i k, ‖z i k‖ ≤ lam),
    ((lam * ε + (1 / (N : ℝ)) * ∑ i, s i : ℝ) : EReal)

/-- (11), p. 12: `inf λε + (1/N) Σ sᵢ` subject to
`[−ℓ_k]*(z_ik − ν_ik) + σ_Ξ(ν_ik) − ⟨z_ik, ξ̂ᵢ⟩ ≤ sᵢ` and `‖z_ik‖_* ≤ λ` for all `i, k`.
An empty feasible set gives `⊤`. -/
noncomputable def program11Value {K N : ℕ} (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E)
    (ℓ : Fin K → E → EReal) : EReal :=
  ⨅ (lam : ℝ) (s : Fin N → ℝ) (z : Fin N → Fin K → StrongDual ℝ E)
    (nu : Fin N → Fin K → StrongDual ℝ E)
    (_ : ∀ i k, conjOn Set.univ (fun ξ => -ℓ k ξ) (z i k - nu i k) + supportFun Ξ (nu i k)
        - ((z i k (ξhat i) : ℝ) : EReal) ≤ (s i : EReal))
    (_ : ∀ i k, ‖z i k‖ ≤ lam),
    ((lam * ε + (1 / (N : ℝ)) * ∑ i, s i : ℝ) : EReal)

end WassDDRO.Reduction


