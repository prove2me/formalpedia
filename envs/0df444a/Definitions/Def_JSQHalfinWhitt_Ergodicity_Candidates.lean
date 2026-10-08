-- Prove2me | Definitions.Def_JSQHalfinWhitt_Ergodicity_Candidates
-- name    : JSQHalfinWhitt_Ergodicity_Candidates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:39:14.68261+00:00
-- url     : https://prove2.me/theorems/544cc030-2887-4a41-b060-5bdc1abe49f6
-- title:
--   App. B.1, §4.1, App. C — Lambert W, the hitting times τ̃^{(κ)} and τ, the curves Γ^{(κ)}, the regions S₀–S₃ and the candidate solutions f^{(1)}, f^{(2)}
-- statement:
--   This file defines the explicit functions from which the Lyapunov function of Theorem 4 is assembled. Fix an integer $n\ge1$, $\beta>0$, and write $b=\beta/\sqrt n$.
--
--   1. **Lambert W.** $W$ is the principal branch of the Lambert W function: for $x\ge -e^{-1}$, $W(x)$ is the unique $w\ge-1$ with $we^{w}=x$.
--
--   2. **Hitting time of $\{x_1=-\kappa/\sqrt n\}$ (C.1).** For $\kappa>\beta$, $x_1\le-\kappa/\sqrt n$ and $x_2>0$,
--   $$\tilde\tau^{(\kappa)}(x)=\frac{-(x_1+b)}{x_2}-W\Big(\frac{(\kappa-\beta)/\sqrt n}{x_2}\,e^{-(x_1+b)/x_2}\Big),$$
--   and at $x_2=0$ it takes the value $\log\big((-\sqrt n x_1-\beta)/(\kappa-\beta)\big)$, the limit (C.3) of Lemma 10. It is the time at which the fluid path $v_1(t)=-b+(x_1+b)e^{-t}+x_2te^{-t}$ reaches $-\kappa/\sqrt n$.
--
--   3. **The curve $\Gamma^{(\kappa)}$ (Lemma 5).** For $\kappa\ge\beta$ and $x_1\le0$, $(\nu^*(x_1),\eta^*(x_1))$ is the unique solution $(\nu,\eta)$ of
--   $$-b+(x_1+b)e^{-\eta}+\eta\nu e^{-\eta}=0,\qquad \nu e^{-\eta}=\kappa/\sqrt n,\qquad \nu\ge\kappa/\sqrt n,\ \eta\ge0,$$
--   and $\Gamma^{(\kappa)}=\{x\in\Omega: x_2=\nu^*(x_1)\}$. One writes $x\ge\Gamma^{(\kappa)}$ when $x_2\ge\nu^*(x_1)$ and $x\le\Gamma^{(\kappa)}$ when $x_2\le\nu^*(x_1)$.
--
--   4. **The time $\tau(x)$ (Lemma 6).** $\tau(x)$ is the smallest $\eta\ge0$ with $b-(x_1+b)e^{-\eta}-\eta x_2e^{-\eta}=0$, and $\tau(x)=\infty$ if there is none.
--
--   5. **$f^{(1)}$ (Lemma 11).** With $\phi=\phi^{(\kappa_1/\sqrt n,\kappa_2/\sqrt n)}$ for $\beta<\kappa_1<\kappa_2$ and $g(x,t)=b-(x_1+b)e^{-t}-x_2te^{-t}$,
--   $$f^{(1)}(x)=\begin{cases}\tilde\tau^{(\kappa_2)}(x)+\int_{\tilde\tau^{(\kappa_2)}(x)}^{\tilde\tau^{(\kappa_1)}(x)}\phi(g(x,t))\,dt,& x_1\le-\kappa_2/\sqrt n,\\ \int_0^{\tilde\tau^{(\kappa_1)}(x)}\phi(g(x,t))\,dt,& x_1\in[-\kappa_2/\sqrt n,-\kappa_1/\sqrt n],\\ 0,& x_1\in[-\kappa_1/\sqrt n,0].\end{cases}$$
--
--   6. **Regions.** $S_0=\{x\in\Omega: x_2\le\kappa_1/\sqrt n\}$, $S_1=\{x\in\Omega: x_2\ge\kappa_1/\sqrt n,\ x\le\Gamma^{(\kappa_1)}\}$, $S_2=\{x\in\Omega:\Gamma^{(\kappa_1)}\le x\le\Gamma^{(\kappa_2)}\}$, $S_3=\{x\in\Omega: x\ge\Gamma^{(\kappa_2)}\}$.
--
--   7. **$f^{(2)}$ (Lemma 12).** With $\tau=\tau(x)$,
--   $$f^{(2)}(x)=\begin{cases}0,& x\in S_0,\\ \int_0^{\log(\sqrt n x_2/\kappa_1)}\phi(x_2e^{-t})\,dt,& x_2\le\kappa_2/\sqrt n,\ x\in S_1,\\ \log(\sqrt n x_2/\kappa_2)+\int_0^{\log(\kappa_2/\kappa_1)}\phi\big(\tfrac{\kappa_2}{\sqrt n}e^{-t}\big)dt,& x_2\ge\kappa_2/\sqrt n,\ x\in S_1,\\ \int_0^{\tau}\phi(x_2e^{-t})\,dt+\frac{\sqrt n}{\beta}\int_{\kappa_1/\sqrt n}^{x_2e^{-\tau}}\phi(t)\,dt,& x_2\le\kappa_2/\sqrt n,\ x\in S_2,\\ \log(\sqrt n x_2/\kappa_2)+\int_{\log(\sqrt n x_2/\kappa_2)}^{\tau}\phi(x_2e^{-t})\,dt+\frac{\sqrt n}{\beta}\int_{\kappa_1/\sqrt n}^{x_2e^{-\tau}}\phi(t)\,dt,& x_2\ge\kappa_2/\sqrt n,\ x\in S_2,\\ \tau+\dfrac{x_2e^{-\tau}-\kappa_2/\sqrt n}{\beta/\sqrt n}+\frac{\sqrt n}{\beta}\int_{\kappa_1/\sqrt n}^{\kappa_2/\sqrt n}\phi(t)\,dt,& x\in S_3.\end{cases}$$
--
--   The functions $f^{(1)}$ and $f^{(2)}$ are the solutions of the PDEs (5.9)–(5.10) used in Lemma 8; $V(x)=\exp\big(\alpha(f^{(1)}+f^{(2)})(x/\sqrt n)\big)$ is the Lyapunov function of Theorem 4.
--
--   **Formalization Note** $W$ is `Classical.choose` of $\exists w\ge-1,\ we^w=x$, with junk value $0$ when $x<-e^{-1}$; only positive arguments occur. $\tilde\tau^{(\kappa)}$ is defined by an explicit case split at $x_2=0$ (the value of the limit (C.3)); Lemma 10 states that this is the limit. $\nu^*$ is the $\nu$-part of the unique solution of the system when it is unique (Lemma 5, mission 1 of this series), junk $0$ otherwise. $\tau$ takes values in `WithTop ℝ`, with $\top$ for "no solution", so a missing solution is never read as $0$; `tauReal` is its real value, used only on $S_2\cup S_3$, where Lemma 12 states $\tau<\infty$. Interval integrals are oriented (`∫ t in a..b`), as printed. $f^{(1)}$ and $f^{(2)}$ are `if` cascades that take the first matching formula on shared boundaries; $f^{(2)}$ is built from the indexed lists `f2Region` and `f2Branch` (the six printed cases in order), so that Lemma 12 can state that overlapping formulas agree. The Lambert W, $\Gamma^{(\kappa)}$ and $\tau$ also appear in mission 1 of this series; they are redefined here because the two missions are drafted independently.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), pp. 24–25, App. B.1, (B.1); p. 12, Lemma 5, (4.8)–(4.9); p. 13, Lemma 6; p. 35, (C.1); p. 36, Lemma 11; p. 41, S_0–S_3 and Lemma 12

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Ergodicity_Operators

namespace JSQHalfinWhitt.Ergodicity

open Real
open scoped Classical

/-- The principal branch `W = W₀` of the Lambert W function (App. B.1, pp. 24–25): for
`x ≥ −e^{−1}`, the unique `w ≥ −1` with `w e^w = x`. Outside that domain the value `0` is a junk
value; it is never used (all arguments below are positive). -/
noncomputable def lambertW (x : ℝ) : ℝ :=
  if h : ∃ w : ℝ, -1 ≤ w ∧ w * Real.exp w = x then Classical.choose h else 0

/-- `β/√n − (x₁ + β/√n) e^{−t} − x₂ t e^{−t}`, the argument of `φ` in Lemma 11, p. 36
(minus the first fluid coordinate at time `t` started from `x`). -/
noncomputable def fluidArg (n : ℕ) (β : ℝ) (x : ℝ × ℝ) (t : ℝ) : ℝ :=
  β / Real.sqrt n - (x.1 + β / Real.sqrt n) * Real.exp (-t) - x.2 * t * Real.exp (-t)

/-- `τ̃^{(κ)}(x)` of (C.1), p. 35, for `x₁ ≤ −κ/√n`, `x₂ > 0`:
`−(x₁ + β/√n)/x₂ − W( ((κ − β)/√n)/x₂ · e^{−(x₁+β/√n)/x₂} )`, extended to `x₂ = 0` by the value of the
limit (C.3), `log((−√n x₁ − β)/(κ − β))` (Lemma 10). Off `{x₁ ≤ −κ/√n, x₂ ≥ 0}` the value is not used. -/
noncomputable def tauTilde (n : ℕ) (β κ : ℝ) (x : ℝ × ℝ) : ℝ :=
  if x.2 = 0 then Real.log ((-Real.sqrt n * x.1 - β) / (κ - β))
  else -(x.1 + β / Real.sqrt n) / x.2
    - lambertW ((κ - β) / Real.sqrt n / x.2 * Real.exp (-(x.1 + β / Real.sqrt n) / x.2))

/-- The nonlinear system (4.8) of Lemma 5, p. 12, in the unknowns `p = (ν, η)`:
`−β/√n + (x₁ + β/√n)e^{−η} + ηνe^{−η} = 0`, `νe^{−η} = κ/√n`, `ν ≥ κ/√n`, `η ≥ 0`. -/
def FluidSystem (n : ℕ) (β κ x1 : ℝ) (p : ℝ × ℝ) : Prop :=
  -β / Real.sqrt n + (x1 + β / Real.sqrt n) * Real.exp (-p.2) + p.2 * p.1 * Real.exp (-p.2) = 0 ∧
    p.1 * Real.exp (-p.2) = κ / Real.sqrt n ∧ κ / Real.sqrt n ≤ p.1 ∧ 0 ≤ p.2

/-- `ν^*(x₁)` (Lemma 5, p. 12): the `ν`-part of the unique solution of (4.8). The curve
`Γ^{(κ)} = {x ∈ Ω | x₂ = ν^*(x₁)}`, and (4.9) `x ≥ Γ^{(κ)}` iff `x₂ ≥ ν^*(x₁)`, `x ≤ Γ^{(κ)}` iff
`x₂ ≤ ν^*(x₁)`. Lemma 5 (`κ ≥ β`, `x₁ ≤ 0`) says the solution exists and is unique; otherwise the value
`0` is a junk value. -/
noncomputable def nuStar (n : ℕ) (β κ x1 : ℝ) : ℝ :=
  if h : ∃! p : ℝ × ℝ, FluidSystem n β κ x1 p then (Classical.choose h.exists).1 else 0

/-- The solutions `η ≥ 0` of `β/√n − (x₁ + β/√n)e^{−η} − ηx₂e^{−η} = 0` (Lemma 6, p. 13). -/
def tauSet (n : ℕ) (β : ℝ) (x : ℝ × ℝ) : Set ℝ :=
  {η | 0 ≤ η ∧ β / Real.sqrt n - (x.1 + β / Real.sqrt n) * Real.exp (-η) - η * x.2 * Real.exp (-η) = 0}

/-- `τ(x)` of Lemma 6, p. 13: the smallest solution in `tauSet`, and `τ(x) = ∞` (`⊤`) if there is no
smallest solution (the solution set is closed, so this happens exactly when it is empty). -/
noncomputable def tau (n : ℕ) (β : ℝ) (x : ℝ × ℝ) : WithTop ℝ :=
  if h : ∃ η, IsLeast (tauSet n β x) η then ((Classical.choose h : ℝ) : WithTop ℝ) else ⊤

/-- The real value of `τ(x)`, used only where `τ(x) < ∞` (on `S₂ ∪ S₃`, Lemma 6.1); `0` at `τ = ∞`. -/
noncomputable def tauReal (n : ℕ) (β : ℝ) (x : ℝ × ℝ) : ℝ :=
  (tau n β x).untopD 0

/-- `φ = φ^{(κ₁/√n, κ₂/√n)}`, the smoothed indicator used throughout App. C (p. 35). -/
noncomputable def phiK (n : ℕ) (κ1 κ2 : ℝ) : ℝ → ℝ :=
  smoothInd (κ1 / Real.sqrt n) (κ2 / Real.sqrt n)

/-- `f^{(1)}` of Lemma 11, p. 36:
* `x₁ ≤ −κ₂/√n`: `τ̃^{(κ₂)}(x) + ∫_{τ̃^{(κ₂)}(x)}^{τ̃^{(κ₁)}(x)} φ(β/√n − (x₁+β/√n)e^{−t} − x₂te^{−t}) dt`;
* `x₁ ∈ [−κ₂/√n, −κ₁/√n]`: `∫_0^{τ̃^{(κ₁)}(x)} φ(⋯) dt`;
* `x₁ ∈ [−κ₁/√n, 0]`: `0`.
The `if` cascade takes the first matching branch on the shared boundaries. -/
noncomputable def f1 (n : ℕ) (β κ1 κ2 : ℝ) (x : ℝ × ℝ) : ℝ :=
  if x.1 ≤ -κ2 / Real.sqrt n then
    tauTilde n β κ2 x +
      ∫ t in tauTilde n β κ2 x..tauTilde n β κ1 x, phiK n κ1 κ2 (fluidArg n β x t)
  else if x.1 ≤ -κ1 / Real.sqrt n then
    ∫ t in (0 : ℝ)..tauTilde n β κ1 x, phiK n κ1 κ2 (fluidArg n β x t)
  else 0

/-- `S₀ = {x ∈ Ω | x₂ ≤ κ₁/√n}` (p. 41). -/
def S0 (n : ℕ) (κ1 : ℝ) : Set (ℝ × ℝ) := {x | x ∈ JSQHalfinWhitt.Tightness.Omega ∧ x.2 ≤ κ1 / Real.sqrt n}

/-- `S₁ = {x ∈ Ω | x₂ ≥ κ₁/√n, x ≤ Γ^{(κ₁)}}` (p. 41). -/
def S1 (n : ℕ) (β κ1 : ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ JSQHalfinWhitt.Tightness.Omega ∧ κ1 / Real.sqrt n ≤ x.2 ∧ x.2 ≤ nuStar n β κ1 x.1}

/-- `S₂ = {x ∈ Ω | Γ^{(κ₁)} ≤ x ≤ Γ^{(κ₂)}}` (p. 41). -/
def S2 (n : ℕ) (β κ1 κ2 : ℝ) : Set (ℝ × ℝ) :=
  {x | x ∈ JSQHalfinWhitt.Tightness.Omega ∧ nuStar n β κ1 x.1 ≤ x.2 ∧ x.2 ≤ nuStar n β κ2 x.1}

/-- `S₃ = {x ∈ Ω | x ≥ Γ^{(κ₂)}}` (p. 41). -/
def S3 (n : ℕ) (β κ2 : ℝ) : Set (ℝ × ℝ) := {x | x ∈ JSQHalfinWhitt.Tightness.Omega ∧ nuStar n β κ2 x.1 ≤ x.2}

/-- The six regions of the piecewise definition of `f^{(2)}` in Lemma 12, p. 41, in the printed order:
`S₀`; `S₁ ∩ {x₂ ≤ κ₂/√n}`; `S₁ ∩ {x₂ ≥ κ₂/√n}`; `S₂ ∩ {x₂ ≤ κ₂/√n}`; `S₂ ∩ {x₂ ≥ κ₂/√n}`; `S₃`. -/
def f2Region (n : ℕ) (β κ1 κ2 : ℝ) : Fin 6 → Set (ℝ × ℝ)
  | 0 => S0 n κ1
  | 1 => S1 n β κ1 ∩ {x | x.2 ≤ κ2 / Real.sqrt n}
  | 2 => S1 n β κ1 ∩ {x | κ2 / Real.sqrt n ≤ x.2}
  | 3 => S2 n β κ1 κ2 ∩ {x | x.2 ≤ κ2 / Real.sqrt n}
  | 4 => S2 n β κ1 κ2 ∩ {x | κ2 / Real.sqrt n ≤ x.2}
  | 5 => S3 n β κ2

/-- The six formulas of `f^{(2)}` in Lemma 12, p. 41, in the printed order (`φ = φ^{(κ₁/√n,κ₂/√n)}`,
`τ = τ(x)`):
0. `0`;
1. `∫_0^{log(√n x₂/κ₁)} φ(x₂e^{−t}) dt`;
2. `log(√n x₂/κ₂) + ∫_0^{log(κ₂/κ₁)} φ((κ₂/√n)e^{−t}) dt`;
3. `∫_0^{τ} φ(x₂e^{−t}) dt + (√n/β) ∫_{κ₁/√n}^{x₂e^{−τ}} φ(t) dt`;
4. `log(√n x₂/κ₂) + ∫_{log(√n x₂/κ₂)}^{τ} φ(x₂e^{−t}) dt + (√n/β) ∫_{κ₁/√n}^{x₂e^{−τ}} φ(t) dt`;
5. `τ + (x₂e^{−τ} − κ₂/√n)/(β/√n) + (√n/β) ∫_{κ₁/√n}^{κ₂/√n} φ(t) dt`. -/
noncomputable def f2Branch (n : ℕ) (β κ1 κ2 : ℝ) : Fin 6 → ℝ × ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun x => ∫ t in (0 : ℝ)..Real.log (Real.sqrt n * x.2 / κ1),
      phiK n κ1 κ2 (x.2 * Real.exp (-t))
  | 2 => fun x => Real.log (Real.sqrt n * x.2 / κ2) +
      ∫ t in (0 : ℝ)..Real.log (κ2 / κ1), phiK n κ1 κ2 (κ2 / Real.sqrt n * Real.exp (-t))
  | 3 => fun x => (∫ t in (0 : ℝ)..tauReal n β x, phiK n κ1 κ2 (x.2 * Real.exp (-t))) +
      Real.sqrt n / β *
        ∫ t in κ1 / Real.sqrt n..x.2 * Real.exp (-tauReal n β x), phiK n κ1 κ2 t
  | 4 => fun x => Real.log (Real.sqrt n * x.2 / κ2) +
      (∫ t in Real.log (Real.sqrt n * x.2 / κ2)..tauReal n β x,
        phiK n κ1 κ2 (x.2 * Real.exp (-t))) +
      Real.sqrt n / β *
        ∫ t in κ1 / Real.sqrt n..x.2 * Real.exp (-tauReal n β x), phiK n κ1 κ2 t
  | 5 => fun x => tauReal n β x +
      (x.2 * Real.exp (-tauReal n β x) - κ2 / Real.sqrt n) / (β / Real.sqrt n) +
      Real.sqrt n / β * ∫ t in κ1 / Real.sqrt n..κ2 / Real.sqrt n, phiK n κ1 κ2 t

/-- `f^{(2)}` of Lemma 12, p. 41: on the `k`-th region of `f2Region` it is the `k`-th formula of
`f2Branch`, taking the first matching region where regions overlap (Lemma 12 asserts that the
formulas agree there); `0` off `Ω`. -/
noncomputable def f2 (n : ℕ) (β κ1 κ2 : ℝ) (x : ℝ × ℝ) : ℝ :=
  if x ∈ f2Region n β κ1 κ2 0 then f2Branch n β κ1 κ2 0 x
  else if x ∈ f2Region n β κ1 κ2 1 then f2Branch n β κ1 κ2 1 x
  else if x ∈ f2Region n β κ1 κ2 2 then f2Branch n β κ1 κ2 2 x
  else if x ∈ f2Region n β κ1 κ2 3 then f2Branch n β κ1 κ2 3 x
  else if x ∈ f2Region n β κ1 κ2 4 then f2Branch n β κ1 κ2 4 x
  else if x ∈ f2Region n β κ1 κ2 5 then f2Branch n β κ1 κ2 5 x
  else 0

end JSQHalfinWhitt.Ergodicity


