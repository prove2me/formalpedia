-- Prove2me | Definitions.Def_ChapterGaugeParametrization
-- name    : ChapterGaugeParametrization
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:58:04.984947+00:00
-- url     : https://prove2.me/theorems/deaa57ec-f81c-453c-8aa5-bd78f14f8e90
-- title:
--   Chapter GaugeParametrization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGaugeParametrization.lean`): generated def bundle for ChapterGaugeParametrization. See BookProof/ChapterGaugeParametrization.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeParametrization.lean

import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib


/-!
# Every parametrization carries a gauge symmetry

This module formalizes the opening argument of the section *"Gauge transformations,
constrained systems and conditioned probability"* of `book.tex` (lines 2240–2252):

> "This includes the case of parametrizations, since these are surjective but
> often there are two or more points in the space of parameters which correspond
> to the same point in the parametrized space […].  As a matter of principle, for
> all parametrizations we can define a gauge group transforming points in the
> parameter space without modifying the corresponding point in the parametrized
> space.  Thus all parametrizations are solutions to constraint equations
> requiring gauge invariance."

Given any parametrization `π : X → Y` of a space `Y` by a parameter space `X`, the
**gauge group of the parametrization** is the group `fiberGauge π` of the
permutations of the parameter space that do not move the parametrized point.

## Results

* `fiberGauge` — the gauge group of a parametrization, a subgroup of the
  permutations of the parameter space.
* `orbit_eq_fiber` — its orbits are *exactly* the fibers of `π`: two parameters
  describe the same point iff they are gauge equivalent.
* `isPhysicalObservable_iff_factors_through` — the gauge-invariant observables of
  this gauge group are exactly the functions of the parametrized point.  This is
  the book's "all parametrizations are solutions to constraint equations requiring
  gauge invariance".
* `fiberGauge_ne_bot_iff` — the gauge group is non-trivial precisely when the
  parametrization is redundant (two parameters for one point), and
  `fiberGauge_eq_bot_iff` is the injective case.
* `isCompleteGaugeFixing'_iff_injOn`,
  `isComprehensiveGaugeFixing_iff_surjOn` — a gauge fixing of this gauge symmetry
  is complete exactly when `π` is injective on it, and comprehensive exactly when
  it already meets every fiber, i.e. when `π` maps it onto the whole parametrized
  space.  A complete comprehensive gauge fixing is therefore the same thing as a
  set of parameters in bijection with the parametrized space.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ChapterGaugeParametrization

open BookProof.ChapterGaugeIncompleteFixing

variable {X Y : Type*}

/-- The **gauge group of a parametrization** `π : X → Y`: the permutations of the
parameter space `X` that leave the parametrized point `π x` unchanged. -/
def fiberGauge (π : X → Y) : Subgroup (Equiv.Perm X) where
  carrier := {σ | ∀ x, π (σ x) = π x}
  mul_mem' {a b} ha hb x := by
    simp only [Equiv.Perm.mul_apply]
    rw [ha (b x), hb x]
  one_mem' _ := rfl
  inv_mem' {a} ha x := by
    have h := ha (a⁻¹ x)
    simpa using h.symm



















end BookProof.ChapterGaugeParametrization


