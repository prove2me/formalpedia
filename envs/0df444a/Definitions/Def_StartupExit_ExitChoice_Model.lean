-- Prove2me | Definitions.Def_StartupExit_ExitChoice_Model
-- name    : StartupExit_ExitChoice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:03.412538+00:00
-- url     : https://prove2.me/theorems/14e5a966-83db-4d37-8ac9-a6aac3b73c6a
-- title:
--   §3.1–§3.4, pp. 7–14 — startup exit model: standing assumptions, auction payoffs (1), Π^E, Π^L, cutoff v̲*, Π^F (2), tie-broken choice, θ̃
-- statement:
--   A startup with execution capability $\theta\in[0,1]$ (its probability of reaching the late market) holds resources $R>0$. Trying the early market costs $c\in[0,R]$; the remaining $R-c$ is devoted to developing the invention, which realizes a fraction $\phi(R-c)$ of the late-market value, where $\phi(0)=0$ and $\phi(R)=1$. There are $m$ buyers in the early market and $n$ in the late market. Buyer $i$ values the startup at $w+v_i$, with common component $w>1$ and idiosyncratic $v_i$ uniform on $[-1,1]$. The parameters $(w,m,n,R,\phi)$ satisfy the **standing assumptions**
--
--   $$w>1,\quad 2\le m<n,\quad R>0,\quad \phi(0)=0,\quad \phi(R)=1,\quad \phi \text{ strictly increasing and continuous on } [0,R].$$
--
--   With $z$ buyers, a second-price auction gives a buyer $\pi_B(z)=\frac1z[X(1,z)-X(2,z)]$ and the seller $\pi_S(z)=w+X(2,z)$ (eq. (1)). The three exit strategies pay:
--
--   1. commit early: $\Pi^E=w+X(2,m)$;
--   2. commit late: $\Pi^L=\theta\,[w+X(2,n)]$;
--   3. flexibility (try the early market and develop): with $t=\phi(R-c)\,\theta$ and Lemma 4's bidding cutoff $\underline v^*(t)=\max\{t(\pi_B(n)+w+X(2,n))-w,\,-1\}$, eq. (2) reads
--
--   $$\Pi^F=\int_{\underline v^*(t)}^{1}(w+x)\,g(x,m)\,dx+G\bigl(\underline v^*(t),m\bigr)\,t\,\bigl(w+X(2,n)\bigr).$$
--
--   The startup's **choice** maximizes $\Pi^E,\Pi^L,\Pi^F$; on ties it prefers the less time-consuming strategy: early before late before flexible. Two thresholds are named: $\tilde\theta=\Pi^E/(w+X(2,n))$, the type at which $\Pi^E=\Pi^L$, and the kink $(w-1)/(w+X(2,n)+\pi_B(n))$, below which $\underline v^*(\theta)=-1$ when $c=0$.
--
--   This is the baseline model of §3 on which Lemma 5 and Proposition 1 are stated.
--
--   **Formalization Note** The page assumes $\phi'>0$; only strict monotonicity and continuity on $[0,R]$ are assumed here (differentiability is not), which is all the appendix proofs use. $2\le m$ is added: $X(2,m)$ is the second-highest of $m$ early bids (footnote 20, p. 22: two or more competing buyers are needed). $\theta$ ranges over $[0,1]$ (the paper's $b=0$, p. 7) and $n$ is finite; the paper's $n\to\infty$ branches are not formalized. Eq. (2) with Lemma 4's cutoff is taken as the definition of $\Pi^F$: Lemma 4 itself (the early-market bidding equilibrium, p. 13 and Online Appendix A1) is the paper's derivation of eq. (2) and is not formalized. Π^F is written as a function of $t=\phi(R-c)\theta$ (`PiFt`) and of $(c,\theta)$ (`PiF`). The tie rule follows p. 8 and PDF 34 ("the startup invests in seeking early offers and developing the invention if and only if Π^F is strictly greater than Π^E"). The choice is defined from the three profits only, never from the thresholds. All quantities are real numbers; $\pi_B(z)$ divides by $z$ and is only used at $z=n\ge3$.
-- source:
--   Arora, Fosfuri & Rønde, Waiting for the payday? The market for startups and the timing of entrepreneurial exit, SSRN 3611808 (forthcoming in Management Science), pp. 7–14 (PDF 8–15), §3.1–§3.4, eq. (1), Lemma 4, eq. (2); p. 8 (tie rule); p. 12 (θ̃); Online Appendix A2 (PDF 34, tie rule)

import Mathlib
import Definitions.Def_StartupExit_ExitChoice_OrderStats

namespace StartupExit.ExitChoice

/-- Parameters of the baseline model: common value `w`, number `m` of early buyers,
number `n` of late buyers, resources `R`, and the development function `φ`. -/
structure Params where
  w : ℝ
  m : ℕ
  n : ℕ
  R : ℝ
  φ : ℝ → ℝ

/-- Standing assumptions of §3.1: `w > 1`, `2 ≤ m < n`, `R > 0`, `φ(0) = 0`, `φ(R) = 1`,
`φ` strictly increasing and continuous on `[0, R]`. -/
def Params.Standing (P : Params) : Prop :=
  1 < P.w ∧ 2 ≤ P.m ∧ P.m < P.n ∧ 0 < P.R ∧ P.φ 0 = 0 ∧ P.φ P.R = 1 ∧
    StrictMonoOn P.φ (Set.Icc 0 P.R) ∧ ContinuousOn P.φ (Set.Icc 0 P.R)

/-- A buyer's expected profit in a second-price auction with `z` buyers,
`π_B(z) = (1/z) [X(1, z) - X(2, z)]`, eq. (1). -/
noncomputable def piB (z : ℕ) : ℝ := (X1 z - X2 z) / z

/-- The seller's expected profit in a second-price auction with `z` buyers,
`π_S(z) = w + X(2, z)`, eq. (1). -/
noncomputable def piS (w : ℝ) (z : ℕ) : ℝ := w + X2 z

/-- `Π^E = w + X(2, m)`: profit from committing to the early market. -/
noncomputable def PiE (P : Params) : ℝ := piS P.w P.m

/-- `Π^L = θ [w + X(2, n)]`: profit from committing to the late market. -/
noncomputable def PiL (P : Params) (θ : ℝ) : ℝ := θ * piS P.w P.n

/-- Lemma 4's cutoff `v*(t) = max{t (π_B(n) + w + X(2, n)) - w, -1}`, with `t = φ θ`. -/
noncomputable def vStar (P : Params) (t : ℝ) : ℝ :=
  max (t * (piB P.n + P.w + X2 P.n) - P.w) (-1)

/-- Eq. (2) as a function of `t = φ θ`:
`∫_{v*(t)}^{1} (w + x) g(x, m) dx + G(v*(t), m) t (w + X(2, n))`. -/
noncomputable def PiFt (P : Params) (t : ℝ) : ℝ :=
  (∫ x in (vStar P t)..1, (P.w + x) * gdens x P.m) +
    Gcdf (vStar P t) P.m * t * (P.w + X2 P.n)

/-- `Π^F`: profit from flexibility (trying the early market at cost `c` and developing the
invention with the remaining `R - c`), i.e. eq. (2) at `φ = φ(R - c)`. -/
noncomputable def PiF (P : Params) (c θ : ℝ) : ℝ := PiFt P (P.φ (P.R - c) * θ)

/-- The three exit strategies. -/
inductive Strategy
  | early
  | late
  | flexible
  deriving DecidableEq

/-- The startup's choice: a maximizer of `Π^E`, `Π^L`, `Π^F`, ties broken towards the less
time-consuming strategy (early before late before flexible). -/
noncomputable def choice (P : Params) (c θ : ℝ) : Strategy :=
  if PiL P θ ≤ PiE P ∧ PiF P c θ ≤ PiE P then Strategy.early
  else if PiF P c θ ≤ PiL P θ then Strategy.late
  else Strategy.flexible

/-- `θ̃ = Π^E / (w + X(2, n))`, the value of `θ` at which `Π^E = Π^L`. -/
noncomputable def thetaTilde (P : Params) : ℝ := PiE P / (P.w + X2 P.n)

/-- The kink `(w - 1) / (w + X(2, n) + π_B(n))`: below it `v*(θ) = -1` (at `c = 0`). -/
noncomputable def kink (P : Params) : ℝ := (P.w - 1) / (P.w + X2 P.n + piB P.n)

end StartupExit.ExitChoice


