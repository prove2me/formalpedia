-- Prove2me | Definitions.Def_SAARate_SharpLD_Setting
-- name    : SAARate_SharpLD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:07.703361+00:00
-- url     : https://prove2.me/theorems/361c7511-ac9e-4ea2-9042-fea067eb5573
-- title:
--   §1–§3, pp. 1–11 — (1.1), (1.2), optimal sets, directional derivatives, Assumptions (A), (B), η of (3.1), Z = C(S^{m−1}), I of (3.4), F of (3.9)
-- statement:
--   This file fixes the objects of Shapiro and Homem-de-Mello's analysis of the exponential rate at which the sample average approximation (SAA) of a convex stochastic program recovers a sharp optimal solution exactly.
--
--   1. **Decision space and objectives.** $E_m=\mathbb R^m$ (Euclidean). For a probability measure $P$ on $(\Omega,\mathcal F)$ and $h:\mathbb R^m\times\Omega\to\mathbb R$, the true objective is $f(x)=\int_\Omega h(x,\omega)\,P(d\omega)$ (1.1). For a sample path $s=(s_0,s_1,\dots)$ in $\Omega$ the SAA objective is
--   $$\hat f_N(x)=\frac1N\sum_{j=0}^{N-1}h(x,s_j),$$
--   so the paper's $\omega^1,\dots,\omega^N$ are the first $N$ terms of one sequence (1.2).
--   2. **Optimal sets.** $\operatorname{argmin}_\Theta g=\{x\in\Theta: g(x)\le g(y)\ \forall y\in\Theta\}$; this gives $A$ (for $f$) and $A_N$ (for $\hat f_N$).
--   3. **Directional derivative.** $g'(x,d)=\lim_{t\downarrow0}\,(g(x+td)-g(x))/t$, which exists for every finite convex $g$.
--   4. **i.i.d. sample.** A sequence $\omega_j:S\to\Omega$ on a probability space $(S,Q)$ of measurable, mutually independent maps, each with law $P$.
--   5. **Assumption (A)** (p. 4): $\bar x\in\Theta$, $A=\{\bar x\}$, and there is $c>0$ with $f(x)\ge f(\bar x)+c\|x-\bar x\|$ for all $x\in\Theta$ (2.2).
--   6. **$\eta$** (3.1): $\eta(d,\omega)=h'_\omega(\bar x,d)$, the directional derivative of $h(\cdot,\omega)$ at $\bar x$.
--   7. **Assumption (B)** (p. 9): $\kappa>0$ and, for $P$-almost every $\omega$, $|\eta(d,\omega)|\le\kappa$ for all $d\in S^{m-1}=\{d:\|d\|=1\}$, i.e. $\|\eta(\cdot,\omega)\|_Z\le\kappa$.
--   8. **The space $Z$** (p. 9): $Z=C(S^{m-1})$ with the sup norm, and the random element $\eta(\cdot,\omega)\in Z$.
--   9. **Rate function** (3.4): for a $Z$-valued random element $Y$,
--   $$I(z)=\sup_{z^*\in Z^*}\bigl\{z^*(z)-\log M(z^*)\bigr\},\qquad M(z^*)=\mathbb E_P\,e^{z^*(Y(\omega))},$$
--   with values in $(-\infty,+\infty]$.
--   10. **The set $F$** (3.9): $F=\{z\in Z:\inf_{d\in T_\Theta(\bar x)\cap S^{m-1}}z(d)\le0\}$, where $T_\Theta(\bar x)$ is the tangent cone.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The directional derivative is `limUnder` of the difference quotient along $t\downarrow0$; it is the true limit whenever $g$ is finite and convex, which every statement guarantees by assuming (i). Assumption (B) is stated pointwise in $d$ under the almost-sure quantifier, which avoids a real supremum. $\eta(\cdot,\omega)$ is turned into an element of $Z$ only when its restriction to the sphere is continuous (always the case under (i)); otherwise a placeholder $0$ is used. $\log M(z^*)$ is the published extended-real log-MGF `logMGF` evaluated at $1$ on $z^*\circ Y$. $F$ is written as "some $d\in T_\Theta(\bar x)\cap S^{m-1}$ has $z(d)\le0$": the infimum of a continuous $z$ over the compact set $T_\Theta(\bar x)\cap S^{m-1}$ is attained, and when that set is empty both forms give $F=\emptyset$. The tangent cone is Mathlib's `tangentConeAt`, which for convex $\Theta$ is the closure of the cone of feasible directions.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), pp. 1, 4, 9–11, (1.1), (1.2), (2.2), Assumption (A), (3.1), Assumption (B), (3.4), (3.9)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.SharpLD

open MeasureTheory ProbabilityTheory Filter Topology

/-- `ω : ℕ → S → Ω` is an i.i.d. sequence of `Ω`-valued random variables on `(S, Q)`, each with
law `P`. -/
def IsIIDSample {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] (Q : Measure S)
    (P : Measure Ω) (ω : ℕ → S → Ω) : Prop :=
  (∀ j, Measurable (ω j)) ∧ iIndepFun ω Q ∧ ∀ j, Q.map (ω j) = P

/-- (3.1), p. 9: `η(d, ω) := h′_ω(x̄, d)`, the directional derivative of `h(·, ω)` at `x̄`. -/
noncomputable def eta {m : ℕ} {Ω : Type*} (h : SAARate.Sharp.E m → Ω → ℝ) (xbar d : SAARate.Sharp.E m) (ω : Ω) : ℝ :=
  SAARate.Sharp.dirDeriv (fun y => h y ω) xbar d

/-- Assumption (B), p. 9: `κ > 0` and, for `P`-almost every `ω`,
`‖η(·, ω)‖_Z = sup_{d ∈ S^{m−1}} |h′_ω(x̄, d)| ≤ κ`, stated pointwise in `d ∈ S^{m−1}`. -/
def AssumptionB {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : SAARate.Sharp.E m → Ω → ℝ) (xbar : SAARate.Sharp.E m) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ᵐ ω ∂P, ∀ d ∈ Metric.sphere (0 : SAARate.Sharp.E m) 1, |eta h xbar d ω| ≤ κ

/-- p. 9: the Banach space `Z := C(S^{m−1})` of real continuous functions on the unit sphere
`S^{m−1} = {d ∈ ℝ^m : ‖d‖ = 1}`, with the sup norm. -/
abbrev Z (m : ℕ) := C(Metric.sphere (0 : SAARate.Sharp.E m) 1, ℝ)

open Classical in
/-- p. 9: the random element `η(·, ω) ∈ Z`, the restriction of `d ↦ η(d, ω)` to `S^{m−1}`.
When `h(·, ω)` is convex (the standing hypothesis (i)) this restriction is continuous and the
first branch is taken; the `0` branch is a placeholder that is never used under (i). -/
noncomputable def etaZ {m : ℕ} {Ω : Type*} (h : SAARate.Sharp.E m → Ω → ℝ) (xbar : SAARate.Sharp.E m) (ω : Ω) : Z m :=
  if hc : Continuous (fun d : Metric.sphere (0 : SAARate.Sharp.E m) 1 => eta h xbar (d : SAARate.Sharp.E m) ω) then
    ⟨fun d => eta h xbar (d : SAARate.Sharp.E m) ω, hc⟩
  else 0

/-- (3.4), p. 10: the large deviations rate function
`I(z) = sup_{z* ∈ Z*} {z*(z) − log M(z*)}`, where `M(z*) = E_P e^{z*(Y(ω))}` is the moment
generating function of the law of the `Z`-valued random element `Y` (the paper's `𝙿`, law of
`η(·, ω)`). `log M(z*)` is `logMGF P (z* ∘ Y) 1 ∈ (−∞, +∞]`, so `I` takes values in `EReal`. -/
noncomputable def cramerRate {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → Z m) (z : Z m) : EReal :=
  ⨆ zs : StrongDual ℝ (Z m),
    ((zs z : ℝ) : EReal) - BellWilliams2001.ThresholdPolicy.logMGF P (fun ω => zs (Y ω)) 1

/-- (3.9), p. 11: the set `F = {z ∈ Z : inf_{d ∈ T_Θ(x̄) ∩ S^{m−1}} z(d) ≤ 0}`, written as
"some `d ∈ T_Θ(x̄) ∩ S^{m−1}` has `z(d) ≤ 0`" (the infimum of the continuous `z` over the compact
set `T_Θ(x̄) ∩ S^{m−1}` is attained; if that set is empty both forms give `F = ∅`). -/
def failureSetF {m : ℕ} (Θ : Set (SAARate.Sharp.E m)) (xbar : SAARate.Sharp.E m) : Set (Z m) :=
  {z | ∃ d : Metric.sphere (0 : SAARate.Sharp.E m) 1, (d : SAARate.Sharp.E m) ∈ tangentConeAt ℝ Θ xbar ∧ z d ≤ 0}

end SAARate.SharpLD


