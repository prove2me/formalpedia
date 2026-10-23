-- Prove2me | Definitions.Def_CTJMDP_MarkovSuff_Extension
-- name    : CTJMDP_MarkovSuff_Extension
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:42.42356+00:00
-- url     : https://prove2.me/theorems/cafeaf57-293c-4008-a1bb-2e88d4f4173c
-- title:
--   Proof of Theorem 1, (54)–(55), pp. 15–16 — the extended CTJMDP with an added state x′ and actions a′, a″, the policy σ̃ and the Markov policy ϕ̃
-- statement:
--   This file defines the extended model used in the proof of Theorem 1 to pass from an initial state to an arbitrary initial distribution $\gamma$.
--
--   1. **Extended CTJMDP (54).** Add a state $x'$ and two actions $a',a''$: $X'=X\cup\{x'\}$, $A'=A\cup\{a',a''\}$, $A'(x)=A(x)\cup\{a''\}$ for $x\in X$ and $A'(x')=\{a',a''\}$. The rates are
--   $$q'(x,a,Z)=\begin{cases}\tilde q(x,a,Z\setminus\{x'\}), & x\in X,\ a\in A(x),\\ \gamma(Z\setminus\{x'\})-\delta_{x'}(Z), & x=x',\ a=a',\\ 0, & x\in X',\ a=a''.\end{cases}$$
--   So $a'$ at $x'$ jumps into $X$ with intensity $\gamma$, and $a''$ makes every state absorbing.
--
--   2. **The policy $\tilde\sigma$ (55).** For a policy $\sigma$ of the original model and $u>0$: on $]0,u]$, $\tilde\sigma$ chooses $a'$ at $x'$ and $a''$ in $X$; on $]u,\infty[$ it chooses $a''$ at $x'$, and on the set $\Omega'(u)$ of paths that start at $x'$, jump into $X$ by time $u$ and stay put until $u$, it chooses $\sigma(\cdot\setminus\{a',a''\}\mid\omega'_{-u},t-u)$, where $\omega'_{-u}=(x'_1,t'_2-u,x'_2,t'_3-u,\dots)$ is the path from time $u$ on, shifted back by $u$.
--
--   3. **The Markov policy $\tilde\phi$** (p. 16):
--   $$\tilde\phi(B\mid z,t)=\delta_{a'}(B)I\{z=x',t\le u\}+\delta_{a''}(B)I\{\{z\in X,t\le u\}\cup\{z=x',t>u\}\}+\phi(B\setminus\{a',a''\}\mid z,t-u)I\{z\in X,t>u\}.$$
--
--   The original model is a sub-model of the extended one, and the marginals of $\tilde\sigma$ from $x'$ at time $t+u$ are those of $\sigma$ from $\gamma$ at time $t$, scaled by $1-e^{-u}$.
--
--   **Formalization Note** $X'$ is `X ⊕ Unit` with $x'$ = `Sum.inr ()`, and $A'$ is `A ⊕ Bool` with $a'$ = `Sum.inr true`, $a''$ = `Sum.inr false`; rates are given by off-diagonal jump measures, pushed into $X'$ by `Sum.inl`. Two readings of (55) are fixed: the two printed cases labelled "$t\in]u,+\infty[$" are summed (as the prose under (55) says); the indicator $I\{\omega'\in\Omega'(u)\}$ is evaluated on the part of the path observed up to the current jump (so that $\tilde\sigma$ is non-anticipating), and off $\Omega'(u)$, where the printed formula gives the zero measure, $\tilde\sigma$ chooses $a''$. Both changes concern a $\mathbb P^{\tilde\sigma}_{x'}$-null set of paths. Reading $\omega'_{-u}$ sends $x'$ to an arbitrary state of $X$, hence `[Nonempty X]`, which is never used on $\Omega'(u)$.
-- source:
--   Feinberg, Mandava, Shiryaev, Sufficiency of Markov Policies for Continuous-Time Jump Markov Decision Processes, arXiv:2003.01342v3, pp. 15–16, proof of Theorem 1, (54), (55), Definition 3, display defining ϕ̃ on p. 16

import Mathlib
import Definitions.Def_CTJMDP_MarkovSuff_Setting

namespace CTJMDP.MarkovSuff

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-! ### The extended CTJMDP of the proof of Theorem 1 ((54)–(55), p. 15; the display on p. 16)

`X′ = X ⊕ Unit` with the added state `x′ = Sum.inr ()`, and `A′ = A ⊕ Bool` with the added actions
`a′ = Sum.inr true`, `a″ = Sum.inr false`. -/

/-- The added state `x′`. -/
def xPrime : X ⊕ Unit := Sum.inr ()

/-- The added action `a′` (jump from `x′` into `X` with intensity `γ`). -/
def aPrime : A ⊕ Bool := Sum.inr true

/-- The added action `a″` (no jumps). -/
def aDPrime : A ⊕ Bool := Sum.inr false

/-- (54): the extended CTJMDP `{X′, A′, A′(·), q′}` with `A′(x) = A(x) ∪ {a″}` for `x ∈ X`,
`A′(x′) = {a′, a″}`, `q′(x, a, Z) = q̃(x, a, Z \ {x′})` for `x ∈ X, a ∈ A(x)`,
`q′(x′, a′, Z) = γ(Z \ {x′}) − δ_{x′}(Z)`, and `q′(·, a″, ·) = 0` (off-diagonal jump measures). -/
def extModel (M : Model X A) (gam : Measure X) : Model (X ⊕ Unit) (A ⊕ Bool) where
  Aset
    | Sum.inl x => Sum.inl '' M.Aset x ∪ {aDPrime}
    | Sum.inr _ => {aPrime, aDPrime}
  qJ
    | Sum.inl x, Sum.inl a => (M.qJ x a).map Sum.inl
    | Sum.inr _, Sum.inr true => gam.map Sum.inl
    | _, _ => 0

/-- The projection `X′ → X` used to read a shifted trajectory (`x′` is sent to an arbitrary state;
this never happens on `Ω′(u)`). -/
def projX [Nonempty X] : X ⊕ Unit → X :=
  Sum.elim id (fun _ => Classical.arbitrary X)

/-- `ω′_{−u} = (x′₁, t′₂ − u, x′₂, t′₃ − u, …)`: the path from time `u` on, shifted back by `u`. -/
def shiftTraj [Nonempty X] (u : ℝ) (ω : Traj (X ⊕ Unit)) : Traj X :=
  (projX (xn ω 1), fun k => (tn ω (k + 2) - ENNReal.ofReal u, projX (xn ω (k + 2))))

/-- The part of the event `ω′ ∈ Ω′(u)` observable up to the `n`th jump: `x′₀ = x′`, `t′₁ ∈ ]0, u]`,
`x′_k ∈ X` for `1 ≤ k ≤ n`, and `t′_k > u` for `2 ≤ k ≤ n`. -/
def inOmegaU (u : ℝ) (n : ℕ) (ω : Traj (X ⊕ Unit)) : Prop :=
  ω.1 = xPrime ∧ 0 < tn ω 1 ∧ tn ω 1 ≤ ENNReal.ofReal u ∧
    (∀ k, 1 ≤ k → k ≤ n → ∃ y : X, xn ω k = Sum.inl y) ∧
    (∀ k, 2 ≤ k → k ≤ n → ENNReal.ofReal u < tn ω k)

open Classical in
/-- (55): the policy `σ̃` of the extended model built from a policy `σ` and `u > 0`. At time
`t = t′_n + s`: for `t ≤ u` it chooses `a′` at `x′` and `a″` in `X`; for `t > u` it chooses `a″` at `x′`
and `σ(· | ω′_{−u}, t − u)` (mapped into `A′`) on `Ω′(u)`. Off `Ω′(u)` at `t > u` the printed
formula gives the zero measure; there `a″` is used (a `ℙ^{σ̃}_{x′}`-null set of paths). -/
def extPol [Nonempty X] (σ : Policy X A) (u : ℝ) : Policy (X ⊕ Unit) (A ⊕ Bool) :=
  fun n ω s =>
    if (tn ω n).toReal + s ≤ u then
      (if xn ω n = xPrime then Measure.dirac aPrime else Measure.dirac aDPrime)
    else if xn ω n = xPrime then Measure.dirac aDPrime
    else if 1 ≤ n ∧ inOmegaU u n ω then
      (σ (n - 1) (shiftTraj u ω)
        ((tn ω n).toReal + s - u - (tn (shiftTraj u ω) (n - 1)).toReal)).map Sum.inl
    else Measure.dirac aDPrime

open Classical in
/-- The Markov policy `ϕ̃` of p. 16:
`ϕ̃(B | z, t) = δ_{a′}(B) I{z = x′, t ≤ u} + δ_{a″}(B) I{{z ∈ X, t ≤ u} ∪ {z = x′, t > u}}
  + ϕ(B \ {a′, a″} | z, t − u) I{z ∈ X, t > u}`. -/
def extMarkov (phi : X → ℝ → Measure A) (u : ℝ) : X ⊕ Unit → ℝ → Measure (A ⊕ Bool)
  | Sum.inr _, t => if t ≤ u then Measure.dirac aPrime else Measure.dirac aDPrime
  | Sum.inl x, t => if t ≤ u then Measure.dirac aDPrime else (phi x (t - u)).map Sum.inl

end

end CTJMDP.MarkovSuff


