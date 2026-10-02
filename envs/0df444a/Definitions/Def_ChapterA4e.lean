-- Prove2me | Definitions.Def_ChapterA4e
-- name    : ChapterA4e
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T14:02:14.720001+00:00
-- url     : https://prove2.me/theorems/b86530c9-383e-4a76-b27e-9dacf4707a6d
-- title:
--   Chapter A4e
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA4e.lean`): generated def bundle for ChapterA4e. See BookProof/ChapterA4e.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA4e.lean

import Definitions.Def_ChapterA5
import Mathlib


/-!
# Chapter A, §A.4 — Props 88 / Corollary 1: the CPT / "antiparticle" payoff

Source: `book.tex` §A.4 (line 5636), Props 87–88 and Corollary 1 — the *causality
⇒ antiparticles* / CPT statement.

The book's argument (roadmap §A.4, "Localization: Props 87–88, Corollary 1") is
that the `iγ⁰`-energy-sign projectors are **not conserved** by the imprimitivity
(momentum → position) structure: the spatial-gradient coefficients `γʲγ⁰`
(the operators appearing in the energy symbol `iH = ∂⃗·γ⃗γ⁰ + …` of §A.5) do
**not** commute with `iγ⁰`.  Concretely `iγ⁰` *anticommutes* with each `γʲγ⁰`
(this is one of the generalized Clifford relations already established in
`ChapterA5`), so the two energy-sign projectors are *swapped* by every spatial
operator.  Hence:

* a positive-energy subspace is mapped onto the negative-energy one — **Prop 88**
  ("a localizable rep containing a positive-energy subrep also contains the
  negative-energy one", i.e. *antiparticles are forced*), and
* the `iγ⁰`-sign projectors are **not conserved**, so a full-Poincaré-irreducible
  localizable rep cannot use them — the reduction underlying **Corollary 1** (the
  CPT / position-operator payoff).

This file formalizes that concrete algebraic core on the `4×4` Majorana Clifford
model of §A.3/§A.5.  The energy operator `iγ⁰` squares to `-1`, so its
eigenvalues are `±i` and the sign projectors `P± = ½(1 ∓ i·iγ⁰)` live over `ℂ`
(they are genuine complementary projectors).  Everything reduces to the integer
anticommutation `{iγ⁰, γʲγ⁰} = 0` (`ChapterA5.coeffBoostZ_mass1_anticomm`) and is
`sorry`-free / `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`),
with **no `EXTERNAL` hypothesis** (Wigner/Mackey enter only in the *exhaustiveness*
clauses of Props 87/88, which are the cited backbone, not this algebraic core).
-/

open Matrix

namespace BookProof.ChapterA4e

open BookProof.ChapterA3 BookProof.ChapterA5

/-! ## The energy operator and the spatial-gradient coefficients over `ℂ` -/

/-- The energy operator `iγ⁰` as a complex matrix (`= ChapterA3.mgamma 0`). -/
noncomputable def enSign : Matrix (Fin 4) (Fin 4) ℂ :=
  (Int.castRingHom ℂ).mapMatrix coeffMass1Z

/-- The spatial-gradient coefficient `γʲγ⁰` as a complex matrix
(`= ChapterA5.coeffBoostZ j` cast to `ℂ`). -/
noncomputable def spatialOp (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Int.castRingHom ℂ).mapMatrix (coeffBoostZ j)





/-! ## The energy-sign projectors `P± = ½(1 ∓ i·iγ⁰)` -/

/-- The positive-energy-sign projector `P₊ = ½(1 - i·iγ⁰)`. -/
noncomputable def projPos : Matrix (Fin 4) (Fin 4) ℂ :=
  (2 : ℂ)⁻¹ • (1 - Complex.I • enSign)

/-- The negative-energy-sign projector `P₋ = ½(1 + i·iγ⁰)`. -/
noncomputable def projNeg : Matrix (Fin 4) (Fin 4) ℂ :=
  (2 : ℂ)⁻¹ • (1 + Complex.I • enSign)

/-
`P₊ + P₋ = 1`: the two energy-sign projectors are complementary.
-/


/-
`P₊² = P₊`: the positive-sign projector is idempotent.
-/


/-
`P₋² = P₋`: the negative-sign projector is idempotent.
-/


/-
`P₊ P₋ = 0`: the two energy-sign projectors are orthogonal.
-/


/-! ## The payoff: the spatial operators swap the two energy-sign subspaces -/

/-
**Prop 88 core.**  Every spatial-gradient operator `γʲγ⁰` *intertwines* the
positive- and negative-energy-sign projectors: `P₊ (γʲγ⁰) = (γʲγ⁰) P₋`.  Thus
`γʲγ⁰` maps the negative-energy subspace onto the positive-energy one — a
positive-energy subrep forces the corresponding negative-energy one
("antiparticles").
-/


/-
Symmetrically, `P₋ (γʲγ⁰) = (γʲγ⁰) P₊`.
-/


/-
The commutator of the positive-sign projector with a spatial operator equals
`i·(γʲγ⁰)(iγ⁰) = i·iγʲ`, an explicit nonzero matrix — the projector is *moved*.
-/


/-
**Corollary 1 core: the energy-sign projectors are NOT conserved.**  There is
a spatial-gradient operator that does not commute with the positive-energy-sign
projector.  Hence a localizable representation that is irreducible under the full
Poincaré group cannot use the (non-conserved) `iγ⁰`-sign projectors — the
reduction underlying the CPT / position-operator payoff.
-/


end BookProof.ChapterA4e


