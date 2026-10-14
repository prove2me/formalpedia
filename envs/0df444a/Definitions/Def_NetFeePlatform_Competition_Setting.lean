-- Prove2me | Definitions.Def_NetFeePlatform_Competition_Setting
-- name    : NetFeePlatform_Competition_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:25.115452+00:00
-- url     : https://prove2.me/theorems/93e9d058-4fd3-408a-8474-ed07085e5478
-- title:
--   §2, (8), (13), (19), (32) — Logit demand with an outside-option weight, platform profit with network effects and interoperability, Nash equilibrium in net fees, the diversion ratio
-- statement:
--   The one-sided platform game of Ekmekci, White and Wu in its Logit specification.
--
--   There are $J$ platforms, indexed by $j$. Platform $j$ charges users a **net fee** $t^j\in\mathbb R$; write $t=(t^1,\dots,t^J)$. The outside option has weight $w=e^{z}\ge 0$, with $w=0$ meaning that there is no outside option.
--
--   1. **Logit demand** (13). The market share of platform $j$ is
--   $$n^j(t)=\frac{e^{-t^j}}{w+\sum_{k}e^{-t^k}}.$$
--   2. **Profit** ((8) with one side, plus the interoperability term of (19)). With common marginal cost $c$, common interaction value $\gamma$ and interoperability $\lambda$,
--   $$\pi^j(t)=\Big(t^j+\gamma n^j(t)+\lambda\gamma\sum_{k\ne j}n^k(t)-c\Big)\,n^j(t).$$
--   The bracket is the total price $p^j$ the platform collects per user: the net fee plus the interaction value it extracts.
--   3. **Equilibrium** (§2). A profile $t$ is a pure-strategy Nash equilibrium in net fees when no platform gains from any unilateral change of its own net fee: $\pi^j(t^j{=}s,\,t^{-j})\le\pi^j(t)$ for every $j$ and every $s\in\mathbb R$.
--   4. **Diversion ratio** (32): $\varphi^j(t)=\sum_{k\ne j}n^k(t)/(1-n^j(t))$.
--
--   These objects are the common setting of the paper's §5–6 results on competition and interoperability; with $\lambda=0$ they are the baseline model of §2–5.
--
--   **Formalization Note** The interoperability parameter $\lambda$ is called `lam` (a Lean keyword clash). Parameter restrictions ($w\ge0$, $\lambda\in[0,1]$, ranges of $\gamma$) are hypotheses of the theorems, not part of the definitions. This one setting is shared by the three missions of the series; the diversion ratio is used by the third (Proposition 7). Outside the model's domain Lean's total arithmetic returns default values: for $w\ge 0$ and at least one platform the Logit denominator is positive, and the only junk value is $\varphi^j=0/0=0$ for a monopoly without outside option ($w=0$, $J=1$, where $n^j=1$), a case excluded by the hypotheses of every result of the series.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), pp. 7–9 (§2, (4)–(8)), p. 13 ((13)), pp. 17–18 (§5), p. 23 ((19)), p. 39 ((32)), pp. 46–47 (Appendix E.1.3)

import Mathlib

namespace NetFeePlatform.Competition

/-- Logit demand (13), one side. `w = e^z` is the weight of the outside option; `w = 0` means
no outside option (the paper's "e^z = 0", p. 44). -/
noncomputable def demand {J : ℕ} (w : ℝ) (t : Fin J → ℝ) (j : Fin J) : ℝ :=
  Real.exp (-t j) / (w + ∑ k, Real.exp (-t k))

/-- Platform j's profit: (8) with S = 1, plus the interoperability term of (19) as written in
Appendix E.1.3, πʲ = (tʲ + γnʲ + γλn⁻ʲ − cʲ)nʲ with n⁻ʲ = Σ_{k≠j} nᵏ. -/
noncomputable def profit {J : ℕ} (w c γ lam : ℝ) (t : Fin J → ℝ) (j : Fin J) : ℝ :=
  (t j + γ * demand w t j + lam * γ * ∑ k ∈ Finset.univ.erase j, demand w t k - c) * demand w t j

/-- Pure-strategy Nash equilibrium in net fees (§2, p. 9): no platform gains from any
unilateral change of its net fee. -/
def IsEquilibrium {J : ℕ} (w c γ lam : ℝ) (t : Fin J → ℝ) : Prop :=
  ∀ (j : Fin J) (s : ℝ), profit w c γ lam (Function.update t j s) j ≤ profit w c γ lam t j

/-- Diversion ratio (32): φʲ = Σ_{k≠j} nᵏ / (1 − nʲ). -/
noncomputable def diversion {J : ℕ} (w : ℝ) (t : Fin J → ℝ) (j : Fin J) : ℝ :=
  (∑ k ∈ Finset.univ.erase j, demand w t k) / (1 - demand w t j)

end NetFeePlatform.Competition


