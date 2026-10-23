-- Prove2me | Definitions.Def_NonconvexCost_Complexity_Algorithm
-- name    : NonconvexCost_Complexity_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:47.36233+00:00
-- url     : https://prove2.me/theorems/119be6ca-feac-4b5c-8c92-369dcbdf8ccc
-- title:
--   Algorithm 4.1, p. 8 — the run of nonsmooth minimization with bisection line search, one oracle call per step
-- statement:
--   This file encodes Algorithm 4.1 (nonsmooth minimization, p. 8) together with its line search, Algorithm 3.1 (bisection, p. 6), as a state machine in which every step from a state that has not stopped makes exactly one call to Oracle 2.5 (which returns $f(x)$, $f'(x;e)$ and $G(x,e)$ together).
--
--   Fix $\delta,\epsilon>0$, $f\colon X\to\mathbb R$ and $G\colon X\times X\to X$. For a current point $x$ and subgradient $g\ne0$ write $\hat g=g/|g|$ and, for $t\in[0,\delta]$,
--   $$x(t)=x+(t-\delta)\hat g,\qquad h(t)=f(x(t))-\frac{\epsilon t}{2},\qquad h'_+(t)=\langle G(x(t),\hat g),\hat g\rangle-\frac{\epsilon}{2}.$$
--   The trial point is $x'=x-\delta\hat g=x(0)$. A state consists of $x$, $g$ and a phase:
--
--   1. **Subgradient test.** If $|g|\le\epsilon$ the run has stopped and the state no longer changes. Otherwise one oracle call at $(x',\hat g)$ gives $f(x')$, $h'_+(0)$ and $G(x',\hat g)$. If $f(x)-f(x')\ge\delta\epsilon/3$ the point $x'$ is accepted (go to re-initialisation). Otherwise this call is the first evaluation of the bisection on $[0,\delta]$: if $h'_+(0)<0$ the subgradient is replaced by the shortest vector in $[g,G(x(0),\hat g)]$ and the run returns to the test; otherwise bisection starts on $[0,\delta]$.
--   2. **Re-initialisation at $x'$.** One oracle call at $(x',0)$; set $x:=x'$, $g:=G(x',0)$; return to the test.
--   3. **Bisection on $[l,r]$.** One oracle call at $(x(m),\hat g)$ with $m=(l+r)/2$. If $h'_+(m)<0$, replace $g$ by the shortest vector in $[g,G(x(m),\hat g)]$ and return to the test; otherwise continue on $[l,m]$ if $2h(m)<h(l)+h(r)$ and on $[m,r]$ otherwise.
--
--   The run from an initial point $x_0$ and an initial Goldstein subgradient $g_0$ is the sequence of states obtained by iterating this step; after $n$ steps at most $n$ oracle calls have been made. The file also names three predicates on states: *stopped* (at the test with $|g|\le\epsilon$), *re-initialising* (a reduction step has just been accepted), and *starts a line search* (at the test, $|g|>\epsilon$, and $f(x)-f(x')<\delta\epsilon/3$).
--
--   The goal theorem bounds the first $n$ at which the run has stopped, so this file is the precise meaning of "the number of calls to Oracle 2.5 required by Algorithm 4.1".
--
--   **Formalization Note** The step counts every oracle call: trial points, bisection midpoints and the re-initialising call $G(x',0)$. The values $h(l)$, $h(r)$ used in the bisection test were returned by earlier calls ($h(\delta)=f(x)-\epsilon\delta/2$ is known), so they cost nothing. The printed bisection test $2h(m)<f(l)+f(r)$ is read as $2h(m)<h(l)+h(r)$, as in (5.3), p. 11.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 8, Algorithm 4.1; p. 6, Algorithm 3.1; p. 4, Oracle 2.5

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting

namespace NonconvexCost.Complexity

open Set
open scoped RealInnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Algorithm 4.1, p. 8: the line-search point `x(t) = x + (t - δ) ĝ`, with `ĝ = g / ‖g‖`. -/
noncomputable def lsPoint (δ : ℝ) (x g : X) (t : ℝ) : X :=
  x + (t - δ) • (‖g‖⁻¹ • g)

/-- Algorithm 4.1, p. 8: the line-search function `h(t) = f(x(t)) - ε t / 2` on `[0, δ]`. -/
noncomputable def lsFun (f : X → ℝ) (δ ε : ℝ) (x g : X) (t : ℝ) : ℝ :=
  f (lsPoint δ x g t) - ε * t / 2

/-- Algorithm 4.1, p. 8: the oracle formula `h'₊(t) = ⟪G(x(t), ĝ), ĝ⟫ - ε / 2`. -/
noncomputable def lsDeriv (G : X → X → X) (δ ε : ℝ) (x g : X) (t : ℝ) : ℝ :=
  ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g), ‖g‖⁻¹ • g⟫ - ε / 2

/-- The control phase of a run of Algorithm 4.1: about to test the current subgradient (`trial`),
about to re-initialise the subgradient at the accepted point `x'` (`reinit x'`), or inside the
bisection of Algorithm 3.1 with current interval `[l, r]` (`bis l r`). -/
inductive Phase (X : Type*) where
  | trial : Phase X
  | reinit (x' : X) : Phase X
  | bis (l r : ℝ) : Phase X

/-- The state of a run of Algorithm 4.1: current point, current Goldstein subgradient, phase. -/
structure State (X : Type*) where
  x : X
  g : X
  ph : Phase X

/-- One step of Algorithm 4.1 (with Algorithm 3.1 as its line search). Every step from a state that
is not stopped makes exactly one call to Oracle 2.5; a stopped state (`trial` with `‖g‖ ≤ ε`) is
left unchanged.
* `trial`: if `‖g‖ ≤ ε`, stop. Otherwise call the oracle at `(x', ĝ)` with `x' = x - δ ĝ = x(0)`.
  If `f x - f x' ≥ δ ε / 3`, accept `x'` (go to `reinit x'`). Otherwise this call is the first
  evaluation `h'₊(0)` of Algorithm 3.1 on `[0, δ]`: if it is negative, replace `g` by the shortest
  vector in `[g, G(x(0), ĝ)]`; else start bisecting `[0, δ]`.
* `reinit x'`: call the oracle at `(x', 0)`; set `x := x'`, `g := G(x', 0)`.
* `bis l r`: call the oracle at `(x(m), ĝ)`, `m = (l + r) / 2`. If `h'₊(m) < 0`, replace `g` by the
  shortest vector in `[g, G(x(m), ĝ)]`; else keep `[l, m]` if `2 h(m) < h(l) + h(r)`, and `[m, r]`
  otherwise. -/
noncomputable def step (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (s : State X) : State X :=
  match s.ph with
  | .trial =>
    if ‖s.g‖ ≤ ε then s
    else if δ * ε / 3 ≤ f s.x - f (lsPoint δ s.x s.g 0) then
      ⟨s.x, s.g, .reinit (lsPoint δ s.x s.g 0)⟩
    else if lsDeriv G δ ε s.x s.g 0 < 0 then
      ⟨s.x, short s.g (G (lsPoint δ s.x s.g 0) (‖s.g‖⁻¹ • s.g)), .trial⟩
    else ⟨s.x, s.g, .bis 0 δ⟩
  | .reinit x' => ⟨x', G x' 0, .trial⟩
  | .bis l r =>
    let m := (l + r) / 2
    if lsDeriv G δ ε s.x s.g m < 0 then
      ⟨s.x, short s.g (G (lsPoint δ s.x s.g m) (‖s.g‖⁻¹ • s.g)), .trial⟩
    else if 2 * lsFun f δ ε s.x s.g m < lsFun f δ ε s.x s.g l + lsFun f δ ε s.x s.g r then
      ⟨s.x, s.g, .bis l m⟩
    else ⟨s.x, s.g, .bis m r⟩

/-- The run of Algorithm 4.1 from the initial point `x0` and initial Goldstein subgradient `g0`:
`run n` is the state after `n` steps, i.e. after at most `n` oracle calls. -/
noncomputable def run (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (x0 g0 : X) : ℕ → State X
  | 0 => ⟨x0, g0, .trial⟩
  | n + 1 => step f G δ ε (run f G δ ε x0 g0 n)

/-- The run has stopped: it is at the subgradient test and `‖g‖ ≤ ε`. -/
def IsDone (ε : ℝ) (s : State X) : Prop :=
  s.ph = .trial ∧ ‖s.g‖ ≤ ε

/-- The state is about to perform a reduction step's re-initialisation (a point was accepted). -/
def IsReinit (s : State X) : Prop :=
  ∃ x' : X, s.ph = .reinit x'

/-- A line search (Algorithm 3.1 on `[0, δ]`) starts at this state: it is at the subgradient test,
`‖g‖ > ε`, and the trial point fails the sufficient-decrease test. -/
def StartsLineSearch (f : X → ℝ) (δ ε : ℝ) (s : State X) : Prop :=
  s.ph = .trial ∧ ε < ‖s.g‖ ∧ f s.x - f (lsPoint δ s.x s.g 0) < δ * ε / 3

end NonconvexCost.Complexity


