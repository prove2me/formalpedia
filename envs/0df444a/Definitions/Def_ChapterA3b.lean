-- Prove2me | Definitions.Def_ChapterA3b
-- name    : ChapterA3b
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:46:48.820986+00:00
-- url     : https://prove2.me/theorems/c3e85f2d-f758-4d85-b93b-a2f72f92f68b
-- title:
--   Chapter A3b
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3b.lean`): generated def bundle for ChapterA3b. See BookProof/ChapterA3b.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3b.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter A, §A.3 — charge conjugation (Lemma 40) and the real Pauli theorem (Prop 37)

This file continues the concrete `4×4` Majorana / gamma-matrix model of
`BookProof/ChapterA3.lean` (work-package **N4** of `FORMALIZATION_ROADMAP.md`,
book §A.3, line 5196), adding the two next deliverables of the queue:

* **Lemma 40 (charge conjugation `Θ`).**  In the Majorana basis, *entrywise
  complex conjugation* `Θ` on `ℂ⁴` is an anti-linear involution commuting with
  every Majorana matrix `iγ^μ` (this is the finite-dimensional instance of the
  C-conjugation of §A.0 Def 8).  Fully concrete — needs no external input,
  because the Majorana matrices are real (`ChapterA3.mgamma_map_conj`).

* **Prop 37 (real Pauli theorem).**  Two real Clifford sets `α^μ`, `β^μ`
  (`4×4` real matrices with `{α^μ,α^ν} = -2 η^{μν}`, same for `β`) are related
  by a **real** matrix `S` with `|det S| = 1`, `β^μ = S α^μ S⁻¹`, unique up to
  sign.  Proved from the **Pauli fundamental theorem** (Note 36, cited
  `Good1955Properties`), introduced as the EXTERNAL named hypothesis
  `PauliFundamental` — never an `axiom`, matching the design of §A.2/§A.3.

  *Proof.*  Complexify: by the fundamental theorem there is an invertible complex
  `T` with `β^μ = T α^μ T⁻¹`, unique up to a nonzero scalar.  Since `α, β` are
  real, entrywise conjugation `T̄` conjugates them the same way, so `T̄ = c·T`
  with `c ≠ 0`; conjugating again gives `c̄ c = 1`, i.e. `|c| = 1`.  Rescale
  `S := a·T` with `a = |det T|^{-1/4} · exp(i·arg c/2)`: then `S` is real
  (`S̄ = S`) and `|det S| = 1`.  Uniqueness up to sign follows from the
  same uniqueness clause applied to two real solutions.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); the sole external input is the named hypothesis
`PauliFundamental`.
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA3

/-! ## Lemma 40 — charge conjugation `Θ` (entrywise complex conjugation) -/

/-- **Charge conjugation** `Θ` on Majorana spinors `ℂ⁴`: entrywise complex
conjugation (Lemma 40; the finite-dimensional C-conjugation of §A.0 Def 8). -/
def chargeConj (v : Fin 4 → ℂ) : Fin 4 → ℂ := fun i => conj (v i)









/-! ## Prop 37 — the real Pauli theorem -/

/-- The Minkowski metric over `ℝ`. -/
def minkowskiR (μ ν : Fin 4) : ℝ := (minkowskiZ μ ν : ℝ)

/-- A **complex Clifford set**: four `4×4` complex matrices satisfying
`{A^μ, A^ν} = -2 η^{μν}`. -/
def IsCliffordC (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ μ ν, A μ * A ν + A ν * A μ = (-2 * minkowski μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℂ)

/-- A **real Clifford set**: four `4×4` real matrices satisfying
`{A^μ, A^ν} = -2 η^{μν}`. -/
def IsCliffordR (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ μ ν, A μ * A ν + A ν * A μ = (-2 * minkowskiR μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- Complexification of a real matrix (entrywise cast `ℝ → ℂ`). -/
def toC (M : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  M.map (Complex.ofReal)

/-- **Pauli fundamental theorem** (Note 36), taken as an EXTERNAL named
hypothesis (cite `Good1955Properties`; not re-proved).  Two complex Clifford
sets are conjugate by an invertible matrix, unique up to a nonzero scalar. -/
def PauliFundamental : Prop :=
  ∀ (A B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ), IsCliffordC A → IsCliffordC B →
    (∃ S : Matrix (Fin 4) (Fin 4) ℂ, IsUnit S.det ∧ ∀ μ, B μ = S * A μ * S⁻¹) ∧
    (∀ S T : Matrix (Fin 4) (Fin 4) ℂ, IsUnit S.det → IsUnit T.det →
      (∀ μ, B μ = S * A μ * S⁻¹) → (∀ μ, B μ = T * A μ * T⁻¹) →
      ∃ c : ℂ, c ≠ 0 ∧ T = c • S)

/-! ### Helper lemmas for the complexification bookkeeping -/

/-
The complexification of a real Clifford set is a complex Clifford set.
-/


/-
Complexification is a ring homomorphism on `4×4` matrices: it preserves
products.
-/


/-
Complexification preserves the identity.
-/


/-
The determinant of a complexified matrix is the cast of the determinant.
-/


/-
Entrywise conjugation fixes a complexified real matrix.
-/


/-
A complex matrix fixed by entrywise conjugation is the complexification of a
real matrix.
-/


/-
Complexification is injective.
-/


/-
Complexification commutes with the matrix inverse.
-/


/-
**Prop 37 (real Pauli theorem).**  Two real Clifford sets `α^μ`, `β^μ` are
related by a real matrix `S` with `|det S| = 1`, `β^μ = S α^μ S⁻¹`, unique up to
sign.
-/


/-! ## Prop 46 — the metric-preservation core (`Λ(S) ∈ O(1,3)`) -/

/-- The Minkowski metric as a `4×4` real matrix `η = diag(1,-1,-1,-1)`. -/
def minkowskiMat : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (fun μ ν => minkowskiR μ ν)

/-
**Prop 46 (metric preservation).**  If `S` is invertible and the real matrix
`Λ` describes the conjugation action of `S` on the Majorana basis,
`S⁻¹ (iγ^μ) S = Σ_ν Λ^μ_ν (iγ^ν)`, then `Λ` is a Lorentz transformation:
`Λ η Λᵀ = η`.  This is the computational heart of Prop 46 (that
`Λ : Pin(3,1) → O(1,3)`), following from the Clifford relation
`{iγ^μ, iγ^ν} = -2 η^{μν}`.
-/


end BookProof.ChapterA3


