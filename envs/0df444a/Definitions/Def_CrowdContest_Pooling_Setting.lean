-- Prove2me | Definitions.Def_CrowdContest_Pooling_Setting
-- name    : CrowdContest_Pooling_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:41.820678+00:00
-- url     : https://prove2.me/theorems/9eeb5217-f752-4671-9cfb-2a05e5cb37e3
-- title:
--   §3–§4.3, Assumption (R), pp. 11–17 — winning probability, h(ξ;n), costs, WTA payoffs, symmetric equilibria of the separate and joint contests, C°, Δξ_n, (R)
-- statement:
--   The contest model of Hu and Wang. There are $n\ge 2$ identical contestants. A contestant's performance in attribute $l\in\{1,2\}$ is $e^l+\xi^l$: effort $e^l\ge 0$ plus a random factor, the random factors being independent across attributes and contestants with a common density $\psi$ and cdf $\Psi$. Let $\psi^\circ$, $\Psi^\circ$ be the density and cdf of $\xi^\circ=\xi^1+\xi^2$.
--
--   1. **Winning probability.** A contestant whose effort exceeds the common effort of the other $n-1$ by $x$ wins (has the best performance) with probability
--   $$W_\psi(x)=\int_{-\infty}^{+\infty}\Psi(x+\xi)^{n-1}\psi(\xi)\,d\xi .$$
--   The joint contest uses $W_{\psi^\circ}$.
--   2. **The function $h$.** $h(\xi;n)=\int_{-\infty}^{+\infty}(n-1)\Psi(\xi)^{n-2}\psi(\xi)^2\,d\xi$, and $h^\circ(\xi^\circ;n)$ is the same expression for $\psi^\circ$.
--   3. **Costs.** A cost function $C$ is continuous on $[0,\infty)$, twice continuously differentiable on $(0,\infty)$, with $C'>0$ and $C''>0$ there.
--   4. **Separate contest.** In a sub-contest with prize $B$ and cost $C$, a contestant making effort $e$ against others making $s$ earns the expected winner-take-all payoff $B\,W_\psi(e-s)-C(e)$. An effort $s\ge 0$ is a **symmetric equilibrium** if no effort $e\ge 0$ earns more against $s$ than $s$ itself. The firm uses prizes $A^1=wA$ and $A^2=(1-w)A$.
--   5. **Joint contest.** With grand prize $A$ and costs $C_1,C_2$, a contestant choosing efforts $(e_1,e_2)$ against others choosing $(s_1,s_2)$ earns
--   $$A\,W_{\psi^\circ}\big((e_1+e_2)-(s_1+s_2)\big)-C_1(e_1)-C_2(e_2).$$
--   A pair $(s_1,s_2)$ of nonnegative efforts is a **symmetric equilibrium** if no nonnegative pair earns more against it.
--   6. **Aggregate cost.** $C^\circ(e)=\min\{C_1(e_1)+C_2(e_2) : e_1,e_2\ge 0,\ e_1+e_2=e\}$ (Lemma 2).
--   7. **Combination term.** $\Delta^\xi_n=\mathsf E(\xi^1_{(n)})+\mathsf E(\xi^2_{(n)})-\mathsf E(\xi^\circ_{(n)})=2\,\mathsf E(\xi_{(n)})-\mathsf E(\xi^\circ_{(n)})$.
--   8. **Assumption (R).** There is $u_0$ such that $2\Psi^{-1}(u)-\Psi^{\circ-1}(u)<0$ for $u\in(0,u_0)$ and $2\Psi^{-1}(u)-\Psi^{\circ-1}(u)>0$ for $u\in(u_0,1)$.
--
--   These are the objects compared by Proposition 1: the separate contest's advantage in random factors ($\Delta^\xi_n$) against the joint contest's advantage in equilibrium effort.
--
--   **Formalization Note** The winning probability is the paper's displayed integral (it equals the probability that the contestant's performance exceeds the maximum of the others', ties having probability zero; that derivation is not part of the formalization). Equilibria are pure symmetric Nash equilibria over nonnegative efforts, and joint-contest strategies are pairs; the paper's aggregate effort $e^{\circ*}$ is $s_1+s_2$. The cost condition "$C'>0$, $C''>0$" is read on positive efforts, with $C$ continuous at $0$, which admits the polynomial costs $ae^b$ of the paper. $C^\circ$ is a real `sInf`: for $e\ge 0$ it is the minimum of a continuous function on a compact segment; at $e<0$ it is a junk value $0$ and is never used. Because $\xi^1,\xi^2$ are identically distributed, one density $\psi$ is used and $\Psi^{1-1}=\Psi^{2-1}=\Psi^{-1}$ in (R), which is stated with "there exists $u_0$" as printed. Integrals are Bochner integrals; under the paper's assumptions every integrand is integrable.
-- source:
--   Hu & Wang, Joint vs. Separate Crowdsourcing Contests, authors' accepted manuscript (TSpace; SSRN 2892683; Manag. Sci. doi:10.1287/mnsc.2020.3683), §3, pp. 11–14 (model, WTA payoffs); §4.1, pp. 14–15 (winning probability, h(ξ;n)); Lemma 2, p. 15 (C°); §4.2, p. 16 (h°); §4.3, p. 16 (Δξ_n); Assumption (R), p. 17; proof of Lemma 1, OA p. 1 (expected payoff)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_CrowdContest_Pooling_Density

open MeasureTheory

namespace CrowdContest.Pooling

/-- The winning probability of a contestant whose effort exceeds the common effort of the other
`n - 1` contestants by `x`, when performances are effort plus an independent random factor with
density `ψ` (Hu & Wang, §4.1, p. 14):
`∫ Ψ(x + ξ)^{n-1} ψ(ξ) dξ`. The joint contest uses `winProb (convDensity ψ) n`. -/
noncomputable def winProb (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ ξ, cdf ψ (x + ξ) ^ (n - 1) * ψ ξ

/-- `h(ξ; n) = ∫ (n - 1) Ψ(ξ)^{n-2} ψ(ξ)² dξ` (§4.1, p. 15); `h°(ξ°; n)` is
`hFun (convDensity ψ) n` (§4.2, p. 16). -/
noncomputable def hFun (ψ : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ ξ, ((n : ℝ) - 1) * cdf ψ ξ ^ (n - 2) * ψ ξ ^ 2

/-- A cost of effort (§3, p. 12): continuous on `[0, ∞)`, twice continuously differentiable on
`(0, ∞)`, with `C' > 0` and `C'' > 0` there. -/
def IsCost (C : ℝ → ℝ) : Prop :=
  ContinuousOn C (Set.Ici 0) ∧ ContDiffOn ℝ 2 C (Set.Ioi 0) ∧
    ∀ e, 0 < e → 0 < deriv C e ∧ 0 < deriv (deriv C) e

/-- The expected winner-take-all payoff `B · P(win) - C(e)` in a sub-contest with prize `B` and
cost `C`, to a contestant making effort `e` while the other `n - 1` make effort `s`
(proof of Lemma 1, OA p. 1). -/
noncomputable def subPayoff (ψ : ℝ → ℝ) (n : ℕ) (B : ℝ) (C : ℝ → ℝ) (e s : ℝ) : ℝ :=
  B * winProb ψ n (e - s) - C e

/-- `s` is a symmetric pure-strategy Nash equilibrium effort of the sub-contest with prize `B` and
cost `C`: `s ≥ 0`, and when the other `n - 1` contestants make effort `s`, no effort `e ≥ 0`
gives a higher expected payoff than `s`. -/
def IsSymEqSub (ψ : ℝ → ℝ) (n : ℕ) (B : ℝ) (C : ℝ → ℝ) (s : ℝ) : Prop :=
  0 ≤ s ∧ ∀ e, 0 ≤ e → subPayoff ψ n B C e s ≤ subPayoff ψ n B C s s

/-- The expected winner-take-all payoff in the joint contest with grand prize `A`, to a contestant
making efforts `(e₁, e₂)` on the two attributes while the other `n - 1` make `(s₁, s₂)`: the
performance is `e₁ + e₂ + ξ¹ + ξ²`, whose random part has density `ψ° = convDensity ψ`
(§3, p. 14; §4.2, p. 16). -/
noncomputable def jointPayoff (ψ : ℝ → ℝ) (n : ℕ) (A : ℝ) (C₁ C₂ : ℝ → ℝ)
    (e₁ e₂ s₁ s₂ : ℝ) : ℝ :=
  A * winProb (convDensity ψ) n ((e₁ + e₂) - (s₁ + s₂)) - C₁ e₁ - C₂ e₂

/-- `(s₁, s₂)` is a symmetric pure-strategy Nash equilibrium of the joint contest: both efforts are
nonnegative, and against `(s₁, s₂)` played by the others no pair `(e₁, e₂)` of nonnegative efforts
gives a higher expected payoff. -/
def IsSymEqJoint (ψ : ℝ → ℝ) (n : ℕ) (A : ℝ) (C₁ C₂ : ℝ → ℝ) (s₁ s₂ : ℝ) : Prop :=
  0 ≤ s₁ ∧ 0 ≤ s₂ ∧ ∀ e₁ e₂, 0 ≤ e₁ → 0 ≤ e₂ →
    jointPayoff ψ n A C₁ C₂ e₁ e₂ s₁ s₂ ≤ jointPayoff ψ n A C₁ C₂ s₁ s₂ s₁ s₂

/-- The cost of an aggregate effort under the optimal allocation over the two attributes,
`C°(e) = min {C₁(e₁) + C₂(e₂) | e₁, e₂ ≥ 0, e₁ + e₂ = e}` (Lemma 2, p. 15). For `e ≥ 0` the set
is the continuous image of a compact segment, so the infimum is attained; it is only used there. -/
noncomputable def aggCost (C₁ C₂ : ℝ → ℝ) (e : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ e₁ e₂, 0 ≤ e₁ ∧ 0 ≤ e₂ ∧ e₁ + e₂ = e ∧ c = C₁ e₁ + C₂ e₂}

/-- `Δξ_n = E(ξ¹_(n)) + E(ξ²_(n)) - E((ξ¹ + ξ²)_(n))` (§4.3, p. 16), with `ξ¹, ξ²` identically
distributed with density `ψ`, so that `E(ξ¹_(n)) = E(ξ²_(n))`. -/
noncomputable def deltaXi (ψ : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 * expMax ψ n - expMax (convDensity ψ) n

/-- Assumption (R), the regularity condition (p. 17), for identically distributed `ξ¹, ξ²` with
density `ψ`: there is `u₀` such that `2Ψ⁻¹(u) - Ψ°⁻¹(u) < 0` for `u ∈ (0, u₀)` and
`2Ψ⁻¹(u) - Ψ°⁻¹(u) > 0` for `u ∈ (u₀, 1)`. -/
def AssumptionR (ψ : ℝ → ℝ) : Prop :=
  ∃ u₀ : ℝ,
    (∀ u ∈ Set.Ioo 0 u₀, 2 * quantile (cdf ψ) u - quantile (cdf (convDensity ψ)) u < 0) ∧
    (∀ u ∈ Set.Ioo u₀ 1, 0 < 2 * quantile (cdf ψ) u - quantile (cdf (convDensity ψ)) u)

end CrowdContest.Pooling


