-- Prove2me | Definitions.Def_CH_CardinalArithmetic
-- name    : CH_CardinalArithmetic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T22:24:04.96095+00:00
-- url     : https://prove2.me/theorems/054eaf8c-e6cd-4323-95b1-ef27b4543d73
-- title:
--   CH, GCH and Freiling's axiom in cardinal arithmetic
-- statement:
--   Statements about cardinals, formulated inside Lean's own set theory (Mathlib's `Cardinal`).
--
--   1. **Continuum hypothesis** (`CH`): there is no $S\subseteq\mathbb R$ with
--   $$\aleph_0<|S|<2^{\aleph_0}.$$
--   2. **Generalized continuum hypothesis** (`GCH`): for every infinite cardinal $\kappa$ there is no cardinal $\mu$ with $\kappa<\mu<2^\kappa$.
--   3. **Freiling's axiom of symmetry** (`FreilingAxiom`): for every function $f$ assigning to each real number $x$ a countable set $f(x)\subseteq\mathbb R$, there are reals $x,y$ with $x\notin f(y)$ and $y\notin f(x)$.
--
--   These are the hypotheses of the cardinal-arithmetic milestones of the mission.
--
--   **Formalization Note** `GCH` is universe-polymorphic: `GCH.{u}` quantifies over cardinals of universe `u`.
-- source:
--   Wikipedia, "Continuum hypothesis" (revision oldid=1376315189), https://en.wikipedia.org/w/index.php?title=Continuum_hypothesis&oldid=1376315189; 'Cardinality of infinite sets' (boxed statement 'Continuum Hypothesis — ∄S: ℵ₀ < |S| < 2^ℵ₀'), 'Generalized continuum hypothesis' (first paragraph), 'Arguments for and against' (Freiling's axiom of symmetry); Freiling, J. Symbolic Logic 51 (1986).

import Mathlib

/-!
# The continuum hypothesis inside Lean's cardinal arithmetic

`ContinuumHypothesis.CH` says that no set of real numbers has cardinality strictly between
`ℵ₀` and `2 ^ ℵ₀`; `ContinuumHypothesis.GCH` says that for no infinite cardinal `κ` is there a
cardinal strictly between `κ` and `2 ^ κ`; `ContinuumHypothesis.FreilingAxiom` is Freiling's
axiom of symmetry.
-/

namespace ContinuumHypothesis

open Cardinal

universe u

/-- The continuum hypothesis: there is no set `S ⊆ ℝ` with `ℵ₀ < |S| < 2 ^ ℵ₀`. -/
def CH : Prop := ∀ S : Set ℝ, ¬ (ℵ₀ < #S ∧ #S < 2 ^ ℵ₀)

/-- The generalized continuum hypothesis (for cardinals in universe `u`): for every infinite
cardinal `κ` there is no cardinal `μ` with `κ < μ < 2 ^ κ`. -/
def GCH : Prop := ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → ¬ ∃ μ : Cardinal.{u}, κ < μ ∧ μ < 2 ^ κ

/-- Freiling's axiom of symmetry: for every function `f` assigning to each real number a
countable set of real numbers, there are reals `x, y` with `x ∉ f y` and `y ∉ f x`. -/
def FreilingAxiom : Prop :=
  ∀ f : ℝ → Set ℝ, (∀ x, (f x).Countable) → ∃ x y : ℝ, x ∉ f y ∧ y ∉ f x

end ContinuumHypothesis


