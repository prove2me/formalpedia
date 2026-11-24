-- Prove2me | Definitions.Def_ChenFarias_SimplePolicy_Supplement_HJB
-- name    : ChenFarias_SimplePolicy_Supplement_HJB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:59:03.44062+00:00
-- url     : https://prove2.me/theorems/e057d326-07c2-41e2-9a2f-c443c2400550
-- title:
--   §6.2, (11) — the HJB state, admissible controls and verification data
-- statement:
--   The state is $y=(s,p,x)\in\mathbb R\times\mathbb R\times\mathbb N$. A candidate $J(s,p,x)$ belongs to $\mathcal J$ if it is jointly differentiable in $(s,p)$ for each $x$, and $J(T,p,x)=J(s,p,0)=0$. No continuity of its derivatives is imposed.
--
--   A Markov control $a(y)=(a_0(y),a_1(y))$ is in $\Pi^M$ when, at every state,
--   $$
--   a_0(y)^-+\lambda\bar F(p)a_1(y)^-\le\underline\theta,\qquad |a_0(y)|,|a_1(y)|\le B,
--   $$
--   and both negative parts are zero at $p=0$. For $s<T$ and $x>0$, the operator is
--   $$
--   H_aJ(s,p,x)=\partial_sJ+\partial_pJ\,a_0(y)+[p+J(s,p+a_1(y),x-1)-J(s,p,x)]\lambda\bar F(p).
--   $$
--   It is zero outside that set. A solution satisfies
--   $$
--   \sup_{a\in\Pi^M}H_aJ(y)=0\quad\text{for every }y.
--   $$
--   A maximizing control belongs to $\Pi^M$ and attains zero at every state. These objects supply the HJB hypotheses, without assuming a solution or maximizing selector exists.
--
--   **Formalization Note** The supremum uses `IsLUB`, so an empty or unbounded real set cannot silently return zero. The full state space includes negative real $s,p$, exactly as printed. Natural subtraction is used only when $x>0$. The printed $\pi^M(s)$ is read as $\pi^M(y)$, since the declared domain is the state space. The bound $B$ is the same parameter used in regularity.
-- source:
--   Chen and Farias, Robust Dynamic Pricing with Strategic Customers, Mathematics of Operations Research 43(4) (2018), pp. 1133–1134, §6.2, (11), Assumption 3

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Supplement_RegularPricing

namespace ChenFarias.SimplePolicy.Supplement

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The paper's full real state space; `((s,p),x)` keeps the two differentiable coordinates together. -/
abbrev State := (ℝ × ℝ) × ℕ
abbrev ValueFunction := ℝ → ℝ → ℕ → ℝ
abbrev MarkovControl := State → ℝ × ℝ

/-- The class `𝒥`: joint differentiability, terminal value zero and zero-stock value zero.
No continuity of the derivatives is assumed. -/
def InJ (T : ℝ) (J : ValueFunction) : Prop :=
  (∀ x : ℕ, Differentiable ℝ (fun z : ℝ × ℝ => J z.1 z.2 x)) ∧
  (∀ p x, J T p x = 0) ∧ (∀ s p, J s p 0 = 0)

/-- The controls in `Πᴹ`, with the same fixed `B` and `theta` as the competitor. -/
def AdmissibleControl (lam theta B : ℝ) (f : ℝ → ℝ) (a : MarkovControl) : Prop :=
  ∀ y : State,
    negPart (a y).1 + lam * Fbar f y.1.2 * negPart (a y).2 ≤ theta ∧
    (y.1.2 = 0 → negPart (a y).1 = 0 ∧ negPart (a y).2 = 0) ∧
    |(a y).1| ≤ B ∧ |(a y).2| ≤ B

/-- The operator on pp. 1133–1134, zero outside `s < T`, `x > 0`. -/
def H (lam T : ℝ) (f : ℝ → ℝ) (J : ValueFunction) (a : MarkovControl)
    (y : State) : ℝ :=
  if y.1.1 < T ∧ 0 < y.2 then
    deriv (fun s => J s y.1.2 y.2) y.1.1 +
    deriv (fun p => J y.1.1 p y.2) y.1.2 * (a y).1 +
    (y.1.2 + J y.1.1 (y.1.2 + (a y).2) (y.2 - 1) - J y.1.1 y.1.2 y.2) *
      lam * Fbar f y.1.2
  else 0

/-- Equation (11), using `IsLUB` to express a genuine finite supremum. -/
def SolvesHJB (lam theta T B : ℝ) (f : ℝ → ℝ) (J : ValueFunction) : Prop :=
  InJ T J ∧ ∀ y : State,
    IsLUB {v : ℝ | ∃ a : MarkovControl, AdmissibleControl lam theta B f a ∧
      v = H lam T f J a y} 0

/-- A pointwise maximizing control; no uniqueness or continuity of the argmax set. -/
def MaximizingControl (lam theta T B : ℝ) (f : ℝ → ℝ)
    (J : ValueFunction) (a : MarkovControl) : Prop :=
  AdmissibleControl lam theta B f a ∧ ∀ y : State, H lam T f J a y = 0

end
end ChenFarias.SimplePolicy.Supplement


