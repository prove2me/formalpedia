-- Prove2me | Definitions.Def_WassDDRO_Consistency_Setting
-- name    : WassDDRO_Consistency_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:34.895335+00:00
-- url     : https://prove2.me/theorems/7fb33218-b344-4611-b3be-4115ae464b4c
-- title:
--   (1), (5), (7), (8), P^∞ — true value, DRO value, concentration inequality, radius ε_N(β), law of the sample sequence
-- statement:
--   This module fixes the objects of Sections 2–3 of Mohajerin Esfahani and Kuhn (arXiv:1505.05116v3) that the consistency results are stated about. Throughout, $E$ is a finite-dimensional real normed space (the space $\mathbb R^m$ with an arbitrary norm $\|\cdot\|$) with its Borel $\sigma$-algebra, $m=\dim E$, $P$ is a probability distribution on $E$, $\Xi\subseteq E$ is the uncertainty set, $X\subseteq\mathbb R^n$ is the feasible set and $h:\mathbb R^n\times E\to\mathbb R$ is the loss. The Wasserstein distance $d_W$, the empirical distribution $\widehat P_N=\frac1N\sum_{i=1}^N\delta_{\hat\xi_i}$, the Wasserstein ball $\mathbb B_\varepsilon(\widehat P_N)$ and the worst-case expectation are the published WassersteinDRO.Duality definitions.
--
--   1. **Radius (8).** For constants $c_1,c_2>0$, an exponent $a>1$, $m,N\in\mathbb N$ and $\beta$,
--   $$
--   \varepsilon_N(\beta)=\begin{cases}\Big(\dfrac{\log(c_1\beta^{-1})}{c_2N}\Big)^{1/\max\{m,2\}} & \text{if } N\ge \dfrac{\log(c_1\beta^{-1})}{c_2},\\[2mm] \Big(\dfrac{\log(c_1\beta^{-1})}{c_2N}\Big)^{1/a} & \text{if } N< \dfrac{\log(c_1\beta^{-1})}{c_2}.\end{cases}
--   $$
--   2. **Concentration inequality (7).** The property that for all $N\ge1$ and $\varepsilon>0$,
--   $$
--   P^N\big\{d_W(P,\widehat P_N)\ge\varepsilon\big\}\le\begin{cases}c_1\exp(-c_2N\varepsilon^{\max\{m,2\}}) & \text{if }\varepsilon\le1,\\ c_1\exp(-c_2N\varepsilon^{a}) & \text{if }\varepsilon>1,\end{cases}
--   $$
--   where $P^N$ is the $N$-fold product of $P$ and $\widehat P_N$ is the empirical distribution of the $N$ samples. Theorem 3.4 (Fournier and Guillin) guarantees constants $c_1,c_2>0$ with this property under Assumption 3.3 when $m\ne2$.
--   3. **The sample sequence.** $P^\infty$ is the law of an i.i.d. sequence $\hat\xi_1,\hat\xi_2,\dots$ with distribution $P$; the first $N$ samples of a realization $\omega$ are $(\omega_1,\dots,\omega_N)$.
--   4. **Distributionally robust value (5)** with the ambiguity set $\mathbb B_\varepsilon(\widehat P_N)$:
--   $$
--   \widehat J_N=\inf_{x\in X}\ \sup_{Q\in\mathbb B_\varepsilon(\widehat P_N)}\mathbb E^{Q}[h(x,\xi)].
--   $$
--   5. **True optimal value (1):**
--   $$
--   J^\star=\inf_{x\in X}\mathbb E^{P}[h(x,\xi)]=\inf_{x\in X}\int_\Xi h(x,\xi)\,P(d\xi).
--   $$
--
--   These are the quantities that the finite sample guarantee (Theorem 3.5) and asymptotic consistency (Theorem 3.6) relate.
--
--   **Formalization Note** Both optimal values are extended reals; an infimum over an empty $X$ is $+\infty$. The probability in (7) is the outer measure of the set of samples, so no measurability of $d_W(P,\widehat P_N)$ in the samples is assumed. The worst-case expectation counts only distributions $Q$ in the ball under which $h(x,\cdot)$ is integrable, and $\mathbb E^P$ is the Bochner integral; every theorem of the mission carries the integrability or growth hypothesis that makes these the paper's expectations. When $\log(c_1\beta^{-1})\le0$ the base in (8) is non-positive and Lean's real power returns a conventional value; the paper uses (8) only for $c_1>\beta$, and the theorems either do not depend on this case or concern limits along $\beta_N\to0$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, (1) p. 5, (5) p. 6, Theorem 3.4 (7) and (8) p. 8, P^∞ p. 8

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk

open MeasureTheory

namespace WassDDRO.Consistency

/-- (8), p. 8: the radius `ε_N(β)` obtained by equating the right-hand side of (7) to `β`,
built from the constants `c₁, c₂` of (7), the exponent `a` of Assumption 3.3 and `m = dim E`:
`(log(c₁β⁻¹)/(c₂N))^{1/max{m,2}}` if `N ≥ log(c₁β⁻¹)/c₂`, and
`(log(c₁β⁻¹)/(c₂N))^{1/a}` if `N < log(c₁β⁻¹)/c₂`. -/
noncomputable def radius (c₁ c₂ a : ℝ) (m N : ℕ) (β : ℝ) : ℝ :=
  if Real.log (c₁ / β) / c₂ ≤ (N : ℝ) then
    (Real.log (c₁ / β) / (c₂ * N)) ^ (1 / (max m 2 : ℝ))
  else (Real.log (c₁ / β) / (c₂ * N)) ^ (1 / a)

/-- The measure concentration inequality (7) of Theorem 3.4, p. 8, for the distribution `P`,
the exponent `a` and the constants `c₁, c₂`, with `m = finrank ℝ E`: for all `N ≥ 1` and
`ε > 0`, `P^N{d_W(P, P̂_N) ≥ ε} ≤ c₁ exp(−c₂ N ε^{max{m,2}})` if `ε ≤ 1` and
`≤ c₁ exp(−c₂ N ε^a)` if `ε > 1`. The left-hand side is the (outer) measure of the set of
samples `ω ∈ E^N` whose empirical distribution is at distance at least `ε` from `P`. -/
def Concentration7 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (a c₁ c₂ : ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ ε : ℝ, 0 < ε →
    (Measure.pi fun _ : Fin N => P)
        {ω | ENNReal.ofReal ε ≤ WassersteinDRO.Duality.wassersteinDistance 1 P
              (WassersteinDRO.Duality.empiricalDistribution ω)} ≤
      ENNReal.ofReal (if ε ≤ 1 then c₁ * Real.exp (-c₂ * N * ε ^ (max (Module.finrank ℝ E) 2 : ℝ))
        else c₁ * Real.exp (-c₂ * N * ε ^ a))

/-- `P^∞`, the law of the whole i.i.d. sample sequence `ξ̂₁, ξ̂₂, …` drawn from `P` (p. 8);
the first `N` samples of `ω : ℕ → E` are `fun i : Fin N => ω i`. -/
noncomputable def P_inf {E : Type*} [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P] :
    Measure (ℕ → E) :=
  Measure.infinitePi (fun _ : ℕ => P)

/-- (5), p. 6, with the Wasserstein ambiguity set (6) of radius `ε` around `P̂_N`:
`Ĵ = inf_{x ∈ X} sup_{Q ∈ B_ε(P̂_N)} E^Q[h(x, ξ)]`, in `EReal` (`⊤` if `X = ∅`). -/
noncomputable def droValue {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {D : Type*} {N : ℕ} (X : Set D) (h : D → E → ℝ) (ε : ℝ) (Ξ : Set E)
    (ξhat : Fin N → E) : EReal :=
  ⨅ x ∈ X, WassersteinDRO.Duality.worstCaseRisk ε 1 Ξ
    (WassersteinDRO.Duality.empiricalDistribution ξhat) (h x)

/-- (1), p. 5: `J⋆ = inf_{x ∈ X} E^P[h(x, ξ)]`, in `EReal` (`⊤` if `X = ∅`). -/
noncomputable def trueValue {E : Type*} [MeasurableSpace E] {D : Type*} (X : Set D)
    (h : D → E → ℝ) (P : Measure E) : EReal :=
  ⨅ x ∈ X, ((∫ ξ, h x ξ ∂P : ℝ) : EReal)

end WassDDRO.Consistency


