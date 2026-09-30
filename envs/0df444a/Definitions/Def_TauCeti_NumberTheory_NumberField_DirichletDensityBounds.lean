-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_DirichletDensityBounds
-- name    : TauCeti_NumberTheory_NumberField_DirichletDensityBounds
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:49:53.182488+00:00
-- url     : https://prove2.me/theorems/c747947c-20a1-4617-9205-4365833315ca
-- title:
--   One-sided bounds for Dirichlet density
-- statement:
--   For a set $S$ of nonzero prime ideals, let $R_S(s)$ be its prime-zeta sum divided by the all-prime sum. A lower Dirichlet-density bound $\delta$ means that for every $\varepsilon>0$, eventually
--
--   $$
--   R_S(s)>\delta-\varepsilon\quad(s\to1^+).
--   $$
--
--   An upper bound reverses the inequality to $R_S(s)<\delta+\varepsilon$. These one-sided bounds can determine a density without assuming a limit in advance.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/DirichletDensityBounds.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/DirichletDensityBounds.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.NumberField.DirichletDensity

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# One-sided bounds for Dirichlet density

For a set `S` of nonzero prime ideals of a number field, Mathlib's
`NumberField.Set.HasDirichletDensity S δ` says that the ratio

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s`

tends to `δ` as `s` approaches `1` from the right.  Squeeze arguments often produce the two
sides of this limit separately.  This file records those one-sided conclusions as
`NumberField.Set.IsLowerDirichletDensityBound S δ` and
`NumberField.Set.IsUpperDirichletDensityBound S δ`.

The predicates use eventual epsilon inequalities, rather than assigning junk-valued lower and
upper densities.  They are monotone in the proposed bound, and a common lower and upper bound
forces a Dirichlet density.  A lower bound is always at most an upper bound; this
comparison also gives the natural interval restrictions on one-sided bounds.

## Main results

* `NumberField.Set.hasDirichletDensity_iff`: Mathlib's `HasDirichletDensity`, unfolded to the
  convergence of the defining ratio.
* `NumberField.Set.HasDirichletDensity.isLowerDirichletDensityBound` and
  `NumberField.Set.HasDirichletDensity.isUpperDirichletDensityBound`: a Dirichlet density is
  both a lower and an upper bound.
* `NumberField.Set.isLowerDirichletDensityBound_of_forall_lt` and
  `NumberField.Set.isUpperDirichletDensityBound_of_forall_gt`: a value is a lower (upper) bound as
  soon as every smaller (larger) value is.
* `NumberField.Set.IsLowerDirichletDensityBound.le_of_isUpperDirichletDensityBound`:
  every lower bound is at most every upper bound.
* `NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound`: matching one-sided bounds
  force a Dirichlet density.
* `NumberField.Set.hasDirichletDensity_iff_bounds`: the resulting characterization of
  Dirichlet density.

## References

* J.-P. Serre, *Corps locaux*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

open Filter IsDedekindDomain NumberField
open scoped Topology

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]



/-- A real number `δ` is a lower Dirichlet-density bound for `S` if, for every positive `ε`,
the ratio defining Dirichlet density is eventually strictly above `δ - ε` as `s → 1⁺`. -/
def IsLowerDirichletDensityBound
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
    δ - ε < S.primeIdealZetaSum s /
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s

/-- A real number `δ` is an upper Dirichlet-density bound for `S` if, for every positive `ε`,
the ratio defining Dirichlet density is eventually strictly below `δ + ε` as `s → 1⁺`. -/
def IsUpperDirichletDensityBound
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ s : ℝ in 𝓝[>] 1,
    S.primeIdealZetaSum s /
      NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s < δ + ε







-- The proof below follows `NumberField.Set.HasDirichletDensity.le_one` from
-- `Mathlib.NumberTheory.NumberField.DirichletDensity`.




























end NumberField.Set

end
end


