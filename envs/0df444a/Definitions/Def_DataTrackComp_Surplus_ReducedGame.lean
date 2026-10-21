-- Prove2me | Definitions.Def_DataTrackComp_Surplus_ReducedGame
-- name    : DataTrackComp_Surplus_ReducedGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:42.015432+00:00
-- url     : https://prove2.me/theorems/3ccedb52-7c08-49d9-8597-771095af8941
-- title:
--   App. B, pp. OA-2–OA-18 — the reduced pricing game G(m): X̄, θ̄, x̃, g, ψ, ξ, φ, its PSNE, the regime m < m_L (B.32), ψ_x and Z (B.29)
-- statement:
--   This file defines the reduced simultaneous-move pricing game $\mathbf G(m)$ of Appendix B and the objects of Lemma 1 and Claim 12.
--
--   For product-1 prices $p^A_1,p^B_1$ and $m>0$, the following objects are defined.
--
--   1. The price dispersion
--   $$\bar X(p^A_1,p^B_1)=\max\{0,\min\{p^B_1-p^A_1+1/2,\,1\}\}.\qquad(B.1)$$
--   2. The cutoff
--   $$\tilde x(m)=\tfrac13\left(\sqrt{(m-1)^2+3}-(m-1)\right).\qquad(B.3)$$
--   3. The indifference type
--   $$\bar\theta(x,m)=\begin{cases}\frac1m\left(2x+m-\sqrt{2x(2x+m)}\right),& x\le\tilde x(m),\\[2pt] \frac{1}{1+x}\left[1-\frac{1}{2m}(1-x)^2\right],& x>\tilde x(m).\end{cases}\qquad(B.2)$$
--   4. The indifference boundary
--   $$g(t\mid p^A_1,p^B_1)=p^B_1-p^A_1+\tfrac12+m\left(t-\bar\theta(\bar X(p^A_1,p^B_1),m)\right)^+.\qquad(B.4)$$
--   5. Three auxiliary functions: $\psi(x,m)=2x\bar\theta(x,m)$ (B.7), $\xi(x,m)=\mathbb E_{\mu_0}\left[\theta;\ s\ge x+m(\theta-\bar\theta(x,m))^+\right]$ (B.8) and $\phi(x,m)=\xi(x,m)+\tfrac12\psi(x,m)\bar\theta(x,m)$ (B.9).
--
--   **Definition 1.** $\mathbf G(m)$ is the two-player game with action spaces $S_A=[0,1]$ and $S_B=[-1/2,1]$ and profits
--   $$\pi^A=p^A_1\,\psi(\bar X,m),\qquad \pi^B=(1-\psi(\bar X,m))\,p^B_1+m\,\phi(\bar X,m),\qquad(B.5)\text{–}(B.6)$$
--   with $\bar X=\bar X(p^A_1,p^B_1)$. A pure-strategy Nash equilibrium (PSNE) is a price pair in $S_A\times S_B$ from which neither firm gains by a unilateral deviation within its action space. A PSNE is **interior** if $p^A_1>0$, $p^B_1>-1/2$ and $p^B_1>p^A_1-1/2$.
--
--   **The interior regime.** Let $\mathcal E$ be the set of $m>0$ for which $\mathbf G(m)$ admits an interior PSNE, and let
--   $$m_L=\sup\{m'>0:(0,m']\subseteq\mathcal E\}.\qquad(B.32)$$
--   The predicate "$m<m_L$" is defined as: there is $m'>m$ such that $\mathbf G(\mu)$ has an interior PSNE for every $\mu\in(0,m']$. Because the set in (B.32) is downward closed, this is equivalent to $m<m_L$ whenever that set is nonempty, and it is never satisfied otherwise.
--
--   **Firm A's best response and $Z$.** $a$ is a best response of firm A to $p^B_1$ if $a\in S_A$ maximizes $\pi^A(\cdot,p^B_1,m)$ over $S_A$. With $\psi_x$ the partial derivative of $\psi$ in $x$, extended by $\psi_x(0,m)=\lim_{t\to0^+}\psi_x(t,m)=2$ (footnote 34), set
--   $$Z(x,m)=\frac{\psi(x,m)}{\psi_x(x,m)}.\qquad(B.29)$$
--
--   **Formalization Note.** The PSNE is the platform's generic feasible-set Nash predicate `CarbonDoubleCount.Planner.IsPureNash`, with player 0 being firm A and player 1 firm B. (B.32) writes $[0,m']$, but $\mathbf G(0)$ is undefined ($m\in\mathbb R_{++}$), so $(0,m']$ is used. The regime is not written as $m<\sup(\dots)$ because Lean's `sSup` of an unbounded or empty set of reals is $0$. $\psi_x$ is Lean's `deriv` for $x\neq0$. On $(0,1]$, $\psi$ is differentiable (Claim 10; the two branches of (B.2) join with equal value and slope at $\tilde x(m)$), so this is the true partial derivative.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), pp. OA-2–OA-4 (PDF 37–39), (B.1)–(B.9) and Definition 1; p. OA-17 (PDF 52), (B.29) and footnote 34; p. OA-18 (PDF 53), interior PSNE and (B.32)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

open MeasureTheory

namespace DataTrackComp.Surplus

/-- (B.1): `X̄(p^A_1, p^B_1) = max{0, min{p^B_1 − p^A_1 + 1/2, 1}}`. -/
noncomputable def Xbar (pA pB : ℝ) : ℝ := max 0 (min (pB - pA + 1 / 2) 1)

/-- (B.3): `x̃(m) = (1/3)(√((m − 1)² + 3) − (m − 1))`. -/
noncomputable def xtilde (m : ℝ) : ℝ := (Real.sqrt ((m - 1) ^ 2 + 3) - (m - 1)) / 3

/-- (B.2): the indifference type `θ̄(x, m)`. -/
noncomputable def thetaBar (x m : ℝ) : ℝ :=
  if x ≤ xtilde m then (1 / m) * (2 * x + m - Real.sqrt (2 * x * (2 * x + m)))
  else (1 / (1 + x)) * (1 - (1 / (2 * m)) * (1 - x) ^ 2)

/-- (B.4): `g(t | p^A_1, p^B_1) = p^B_1 − p^A_1 + 1/2 + m (t − θ̄(X̄(p^A_1, p^B_1), m))⁺`. -/
noncomputable def gfun (m pA pB t : ℝ) : ℝ :=
  pB - pA + 1 / 2 + m * max (t - thetaBar (Xbar pA pB) m) 0

/-- (B.7): `ψ(x, m) = 2 x θ̄(x, m)`. -/
noncomputable def psi (x m : ℝ) : ℝ := 2 * x * thetaBar x m

/-- (B.8): `ξ(x, m) = E_{μ0}[θ ; s ≥ x + m (θ − θ̄(x, m))⁺]`. -/
noncomputable def xi (x m : ℝ) : ℝ :=
  ∫ τ, (if x + m * max (τ.2 - thetaBar x m) 0 ≤ τ.1 then τ.2 else 0) ∂μ0

/-- (B.9): `φ(x, m) = ξ(x, m) + (1/2) ψ(x, m) θ̄(x, m)`. -/
noncomputable def phi (x m : ℝ) : ℝ := xi x m + (1 / 2) * psi x m * thetaBar x m

/-- (B.5): firm A's profit in `G(m)`. -/
noncomputable def piA (m pA pB : ℝ) : ℝ := pA * psi (Xbar pA pB) m

/-- (B.6): firm B's profit in `G(m)`. -/
noncomputable def piB (m pA pB : ℝ) : ℝ :=
  (1 - psi (Xbar pA pB) m) * pB + m * phi (Xbar pA pB) m

/-- Definition 1: `(p^A_1, p^B_1)` is a pure-strategy Nash equilibrium of `G(m)`
(player `0` is firm A with action space `S_A`, player `1` is firm B with `S_B`). -/
def IsPSNE (m pA pB : ℝ) : Prop :=
  CarbonDoubleCount.Planner.IsPureNash (ι := Fin 2) (strategy := fun _ => ℝ)
    (fun i => if i = 0 then SA else SB)
    (fun i s => if i = 0 then piA m (s 0) (s 1) else piB m (s 0) (s 1))
    ![pA, pB]

/-- An interior PSNE (p. OA-18): `p^A_1 > 0`, `p^B_1 > −1/2` and `p^B_1 > p^A_1 − 1/2`. -/
def IsInteriorPSNE (m pA pB : ℝ) : Prop :=
  IsPSNE m pA pB ∧ 0 < pA ∧ -1 / 2 < pB ∧ pA - 1 / 2 < pB

/-- `m ∈ 𝓔`: `G(m)` admits an interior PSNE. -/
def HasInteriorPSNE (m : ℝ) : Prop := ∃ pA pB, IsInteriorPSNE m pA pB

/-- `m < m_L` for `m_L = sup{m′ > 0 : (0, m′] ⊆ 𝓔}` (B.32), stated without `sSup`:
some `m′ > m` has `G(μ)` admitting an interior PSNE for every `μ ∈ (0, m′]`. -/
def InInteriorRegime (m : ℝ) : Prop :=
  ∃ m', m < m' ∧ ∀ μ ∈ Set.Ioc (0 : ℝ) m', HasInteriorPSNE μ

/-- `a` is a best response of firm A to `pB` in `G(m)`. -/
def IsBestRespA (m pB a : ℝ) : Prop := a ∈ SA ∧ ∀ a' ∈ SA, piA m a' pB ≤ piA m a pB

/-- `ψ_x(x, m)`, the partial derivative of `ψ` in `x`, with `ψ_x(0, m) := 2` (footnote 34). -/
noncomputable def psix (x m : ℝ) : ℝ := if x = 0 then 2 else deriv (fun y => psi y m) x

/-- (B.29): `Z(x, m) = ψ(x, m) / ψ_x(x, m)`. -/
noncomputable def Z (x m : ℝ) : ℝ := psi x m / psix x m

end DataTrackComp.Surplus


