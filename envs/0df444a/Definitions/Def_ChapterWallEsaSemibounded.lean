-- Prove2me | Definitions.Def_ChapterWallEsaSemibounded
-- name    : ChapterWallEsaSemibounded
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T20:23:18.721339+00:00
-- url     : https://prove2.me/theorems/5616dfc0-c2a2-4885-8cce-d1528da5f7b2
-- title:
--   The quadratic form of `−d²/dx² + V` is bounded below when `V` is Contents
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.WallEsaSemibounded`, source chapter `BookProof/ChapterWallEsaSemibounded.lean`): The quadratic form of `−d²/dx² + V` is bounded below when `V` is Contents
--
--   `BookProof/ChapterWallEsaBddBelow.lean` proves that `−d²/dx² + V` is essentially self-adjoint on the compactly supported smooth core of `L²(ℝ)` for every smooth `V` bounded below. Its docstring promised, but did not supply, the packaging lemma that the shift-invert schemes need: the *quadratic form* of that operator is bounded below by the same constant. This module supplies it.
--
--   The content is the one-dimensional Green identity on the compactly supported smooth core,
--
--   `⟪(−d²/dx² + V) f, f⟫ = ∫ |f'|² + ∫ V |f|²`,
--
--   which is integration by parts once — carried out here with the compact-support integration-by-parts engine `BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport`. Both terms on the right are real, the first is `≥ 0`, and the second is `≥ -c ‖f‖²` when `V ≥ -c`.
--
--   * `SemiboundedBelowOn` — the quadratic form of an unbounded operator on a core is bounded below by `-c`. * `integral_conj_neg_deriv2_mul` — the Green identity `∫ conj(−f'') f = ∫ |f'|²` for a compactly supported `C²` function on the line. * `kinCcR_quadratic_form` / `opCc_quadratic_form` / `ccEquiv_norm_sq` — the three pieces of the pairing as ordinary integrals. * **`wallHamBddBelow_semibounded`** — the promised lemma: if `V ≥ -c` then the quadratic form of `wallHam V hV` is bounded below by `-c`. * `wallHam_nonneg_form` — the `c = 0` case: for `V ≥ 0` the form is non-negative.
--
--   The exponential wall `eˣ + e⁻ˣ` is handled in `BookProof/ChapterExpPotentialEsa.lean` (`expPotential_semibounded`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWallEsaSemibounded.lean

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterStrichartzWave


/-!
# The quadratic form of `−d²/dx² + V` is bounded below when `V` is

`BookProof/ChapterWallEsaBddBelow.lean` proves that `−d²/dx² + V` is essentially
self-adjoint on the compactly supported smooth core of `L²(ℝ)` for every smooth `V`
bounded below.  Its docstring promised, but did not supply, the packaging lemma that
the shift-invert schemes need: the *quadratic form* of that operator is bounded below
by the same constant.  This module supplies it.

The content is the one-dimensional Green identity on the compactly supported smooth
core,

  `⟪(−d²/dx² + V) f, f⟫ = ∫ |f'|² + ∫ V |f|²`,

which is integration by parts once — carried out here with the compact-support
integration-by-parts engine
`BookProof.SchrodingerCutoff.integral_deriv_eq_zero_of_hasCompactSupport`.  Both terms
on the right are real, the first is `≥ 0`, and the second is `≥ -c ‖f‖²` when `V ≥ -c`.

## Contents

* `SemiboundedBelowOn` — the quadratic form of an unbounded operator on a core is
  bounded below by `-c`.
* `integral_conj_neg_deriv2_mul` — the Green identity `∫ conj(−f'') f = ∫ |f'|²` for
  a compactly supported `C²` function on the line.
* `kinCcR_quadratic_form` / `opCc_quadratic_form` / `ccEquiv_norm_sq` — the three
  pieces of the pairing as ordinary integrals.
* **`wallHamBddBelow_semibounded`** — the promised lemma: if `V ≥ -c` then the
  quadratic form of `wallHam V hV` is bounded below by `-c`.
* `wallHam_nonneg_form` — the `c = 0` case: for `V ≥ 0` the form is non-negative.

The exponential wall `eˣ + e⁻ˣ` is handled in `BookProof/ChapterExpPotentialEsa.lean`
(`expPotential_semibounded`).
-/

namespace BookProof.WallEsaSemibounded

open MeasureTheory SchwartzMap
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The quadratic form of an unbounded operator `T`, defined on the core `D`, is
**bounded below by `-c`**: `Re ⟪T v, v⟫ ≥ -c ‖v‖²` for every `v` in the core. -/
def SemiboundedBelowOn (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) (c : ℝ) : Prop :=
  ∀ v : D, -c * ‖(v : F)‖ ^ 2 ≤ (inner ℂ (T v) (v : F) : ℂ).re

/-! ## The Green identity on the compactly supported smooth core -/



/-! ## The three pieces of the pairing -/









/-! ## The packaging lemma -/





end

end BookProof.WallEsaSemibounded


