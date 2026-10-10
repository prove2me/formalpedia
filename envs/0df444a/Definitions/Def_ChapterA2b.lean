-- Prove2me | Definitions.Def_ChapterA2b
-- name    : ChapterA2b
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-10T06:54:54.004211+00:00
-- url     : https://prove2.me/theorems/92f8f32e-f67c-4b04-af7b-dbb23035b197
-- title:
--   Chapter A2b
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA2b.lean`): generated def bundle for ChapterA2b. See BookProof/ChapterA2b.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA2b.lean

import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA2
import Mathlib


/-!
# Chapter A, §A.2 — the commutant classification, R-real case (work-package N2)

This file continues work-package **N2** of `FORMALIZATION_ROADMAP.md` (§A.2, the
commutant classification ℝ / ℂ / ℍ).  `ChapterA2.lean` established **Lemma 14**
(uniqueness of the antiisometry up to a unit phase).  Here we formalize the
**payoff for the R-real type — Prop 17** — together with the packaged form of
the underlying complex Schur statement.

The mathematics.  For a **complex Schur system** `(M, V)` the *full* commutant
(every continuous `ℂ`-linear operator commuting with `M`) is exactly the complex
scalars `ℂ · 1` — this is Schur's lemma for the representation, which the roadmap
flags as an `EXTERNAL` input for unitary representations; it is therefore taken
here as a **named hypothesis** `IsSchurFull`, never an `axiom`.

* `IsSchurFull` — the named Schur property: every commuting continuous
  `ℂ`-linear operator is a complex scalar `c • 1`.
* `commutant_eq_complex_scalars` — the packaged restatement: an operator lies in
  the commutant **iff** it is a complex scalar (Def 13, "the commutant is `ℂ`").

* `CommutesConj` — an operator commutes with an anti-unitary `θ` (equivalently,
  preserves the real form `V_θ = {x : θ x = x}`).
* **`Rreal_commutant_eq_real_scalars` (Prop 17).**  For a complex Schur system
  `(M, V)` with a C-conjugation `θ`, an operator commutes with `M` *and* with
  `θ` **iff** it is a **real** scalar `(r : ℂ) • 1`.  Via the complexification /
  real-form correspondence, operators commuting with `θ` are exactly the
  complexifications of the `ℝ`-linear operators on the real form `V_θ`, so this
  says the real commutant of an R-real Schur system is `ℝ` — the first entry of
  the ℝ / ℂ / ℍ trichotomy.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).

**Obstruction (recorded, N2 residue).**  The remaining two entries of the
trichotomy — Prop 18 (R-complex commutant `≅ ℂ`) and Prop 19 (R-pseudoreal
commutant `≅ ℍ`) — live on the *real* form and require sorting the `ℝ`-linear
commutant into its `ℂ`-linear (Schur `= ℂ`) and `ℂ`-antilinear (`= ℂ · θ`, by
Lemma 14) parts; the quaternion algebra `1, i, θ, iθ` then appears in the
C-pseudoreal case.  This needs the realification bookkeeping of `ChapterA1d.lean`
and is left for a later pass.
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## The full Schur property and the complex commutant -/

/-- **Def 13 (Schur, full form).**  `M` is *Schur* iff every continuous
`ℂ`-linear operator commuting with `M` is a complex scalar `c • 1`.  The roadmap
flags Schur's lemma for unitary representations as an `EXTERNAL` theorem (not in
Mathlib); it is used here only as a **named hypothesis**, never an `axiom`. -/
def IsSchurFull (M : System ℂ V) : Prop :=
  ∀ S : V →L[ℂ] V, M.Commutes S → ∃ c : ℂ, S = c • (1 : V →L[ℂ] V)

/-
**The commutant of a Schur system is `ℂ`.**  For a complex Schur system, an
operator lies in the commutant **iff** it is a complex scalar `c • 1`.  (The
backward direction holds for any system: scalars are central.)
-/


/-! ## Prop 17 — the R-real commutant is `ℝ` -/

/-- An operator `S` **commutes with the anti-unitary** `θ` iff `S (θ x) = θ (S x)`
for every `x`.  For a C-conjugation this is exactly the condition that `S`
preserves the real form `V_θ = {x : θ x = x}` (and hence descends to an
`ℝ`-linear operator on it). -/
def CommutesConj (θ : AntiUnitary V) (S : V →L[ℂ] V) : Prop :=
  ∀ x, S (θ x) = θ (S x)



/-
**Prop 17 (R-real commutant `≅ ℝ`).**  For a complex Schur system `(M, V)`
with a C-conjugation `θ`, an operator commutes with `M` **and** with `θ` iff it
is a **real** scalar `(r : ℂ) • 1`.

Via the real-form correspondence (operators commuting with `θ` are exactly the
complexifications of `ℝ`-linear operators on `V_θ = {x : θ x = x}`), this says
the real commutant of an R-real Schur system is `ℝ`.

*Proof.*  Forward: by `IsSchurFull` the operator is a complex scalar `c • 1`;
commuting with the conjugate-linear `θ` forces `c • θ x = conj c • θ x` for all
`x`, and as `θ` is surjective either `V` is trivial (so `S = 0 = 0 • 1`) or
`c = conj c` is real.  Backward: `real_scalar_commutesConj`, and scalars commute
with `M`.
-/


end BookProof.ChapterA


