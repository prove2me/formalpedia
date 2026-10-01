-- Prove2me | Definitions.Def_ChapterLinftyMaximalAbelian
-- name    : ChapterLinftyMaximalAbelian
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:02:05.531973+00:00
-- url     : https://prove2.me/theorems/6aa984bf-00d5-48f8-b58e-85512e6fa751
-- title:
--   Chapter LinftyMaximalAbelian
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLinftyMaximalAbelian.lean`): generated def bundle for ChapterLinftyMaximalAbelian. See BookProof/ChapterLinftyMaximalAbelian.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLinftyMaximalAbelian.lean

import Definitions.Def_ChapterLinftyMultiplication
import Mathlib


/-!
# `L∞(μ)` is *maximal* abelian on `L²(μ)` — the diffuse half of the classification

`ChapterLinftyMultiplication` builds the diffuse model of the abelian
classification: for essentially bounded `φ : α → ℂ` the multiplication operators
`multOp φ : L²(μ) →L[ℂ] L²(μ)` form a unital, abelian, star-closed and faithful
algebra.  `ChapterAbelianAtomicCondensation` proves the *atomic* condensation:
a purely atomic maximal abelian algebra **is** the diagonal algebra `ℓ∞`.

This module proves the matching statement for the diffuse model, which is the
structural fact the classification actually rests on:

  **the multiplication algebra is its own commutant.**

Concretely (`commutant_eq_multOp`), on a finite measure space every bounded
operator `T` on `L²(μ)` that commutes with *every* multiplication operator is
itself a multiplication operator `T = multOp ψ`, and its symbol is
`ψ = T(1)` with `‖ψ‖_∞ ≤ ‖T‖` (`symbol_ae_norm_le`,
`memLp_top_symbol`).  Hence the algebra is **maximal abelian**
(`multOp_algebra_maximal_abelian`): no bounded operator can be adjoined to it
without breaking commutativity.  Specialized to Lebesgue measure on `[0,1]`
(`unitInterval_multOp_maximal_abelian`) this is the diffuse companion of the
atomic condensation — the two ends of the classification list.

The proof is the classical one:

* `symbol T := T(1)` makes sense because `1 ∈ L²(μ)` for a finite measure;
* `symbol_mul` — commutation gives `T(φ) = φ · ψ` for every bounded `φ`;
* `symbol_ae_norm_le` — testing on the indicator of `{‖ψ‖ ≥ ‖T‖ + ε}` and
  comparing the two `L²` norms forces that set to be null, so `ψ ∈ L∞(μ)`;
* `commutant_eq_multOp` — `T` and `multOp ψ` are continuous and agree on the
  indicator functions, hence everywhere, by `Lp.induction`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

noncomputable section

open MeasureTheory ENNReal Complex

namespace BookProof.ChapterLinftyMaximalAbelian

open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- The constant function `1`, as an element of `L²(μ)` (available because `μ`
is finite).  It is the cyclic vector of the multiplication algebra. -/
def oneLp (μ : Measure α) [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  MemLp.toLp (fun _ : α => (1 : ℂ)) (memLp_const 1)



/-- The **symbol** of an operator: a strongly measurable representative of
`T(1)`.  For a `T` commuting with all multiplications this is the essentially
bounded function that `T` multiplies by. -/
def symbol (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : α → ℂ :=
  (Lp.aestronglyMeasurable (T (oneLp μ))).mk _





/-- An operator commuting with every multiplication operator. -/
def CommutesWithMultOps (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ (φ : α → ℂ) (hφ : MemLp φ ⊤ μ), T.comp (multOp φ hφ) = (multOp φ hφ).comp T















end BookProof.ChapterLinftyMaximalAbelian

end


