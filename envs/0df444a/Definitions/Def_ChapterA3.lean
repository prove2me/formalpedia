-- Prove2me | Definitions.Def_ChapterA3
-- name    : ChapterA3
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T03:16:25.525877+00:00
-- url     : https://prove2.me/theorems/bea5de5e-420d-48d5-a3d1-708a6a9f6bb2
-- title:
--   Chapter A3
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3.lean`): generated def bundle for ChapterA3. See BookProof/ChapterA3.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3.lean

import Mathlib


/-!
# Chapter A, §A.3 — the concrete `4×4` Majorana / gamma-matrix model

This file builds the concrete Clifford-algebra model of Chapter A §A.3 of
`book.tex` (see `FORMALIZATION_ROADMAP.md`, work-package **N4**): the four
**Majorana matrices** `iγ^μ` (`μ = 0,1,2,3`) as explicit `4×4` complex matrices,
in the real Majorana basis printed at `book.tex` eq. `\label{basis}`, together
with the fifth matrix `iγ⁵`.

To keep the entrywise computations fast and robust, the matrices are defined over
`ℤ` (where the Clifford identities are closed by `decide`) and then cast into `ℂ`
through the ring homomorphism `Int.castRingHom ℂ`; every complex statement is
obtained from the corresponding integer statement by transport along that ring
homomorphism.  The self-contained "infrastructure" the roadmap asks for is:

* `mgamma_clifford` — the defining Clifford relation
  `(iγ^μ)(iγ^ν) + (iγ^ν)(iγ^μ) = -2 η^{μν}` with `η = diag(1,-1,-1,-1)`.
* `mgamma_map_conj` — the matrices are **real** (fixed by entrywise conjugation).
* `mgamma_unitary` — each `iγ^μ` is **unitary** (`(iγ^μ)ᴴ (iγ^μ) = 1`).
* `mgamma5_eq_prod` — `iγ⁵ = iγ⁰ iγ¹ iγ² iγ³`.
* `mgamma5_sq`, `mgamma5_anticomm` — `(iγ⁵)² = -1` and `iγ⁵` anticommutes with
  every `iγ^μ`.
* `dgamma`, `dgamma_clifford` — the Dirac matrices `γ^μ = -i(iγ^μ)` and their
  Clifford relation `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν}`.

Everything is `sorry`-free and `axiom`-free.  The Pauli fundamental theorem
(Note 36) and Weyl complete reducibility (Note 50), which the later §A.3 results
(Prop 37, Lemma 40, Prop 46, Lemma 52) build on, are `EXTERNAL` and are not
assumed here; only the concrete matrix model is established.
-/

open Matrix

namespace BookProof.ChapterA3

/-! ## Integer model -/

/-- The Minkowski metric `η^{μν} = diag(1, -1, -1, -1)`, over `ℤ`. -/
def minkowskiZ (μ ν : Fin 4) : ℤ := if μ = ν then (if μ = 0 then 1 else -1) else 0

/-- The four Majorana matrices `iγ^μ` over `ℤ`, in the explicit real Majorana
basis of `book.tex` eq. `\label{basis}`. -/
def mgammaZ : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => !![0,0,1,0; 0,0,0,1; -1,0,0,0; 0,-1,0,0]
  | 1 => !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1]
  | 2 => !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]
  | 3 => !![0,1,0,0; 1,0,0,0; 0,0,0,-1; 0,0,-1,0]

/-- The fifth Majorana matrix `iγ⁵` over `ℤ`. -/
def mgamma5Z : Matrix (Fin 4) (Fin 4) ℤ := !![0,-1,0,0; 1,0,0,0; 0,0,0,1; 0,0,-1,0]











/-! ## Complex model -/

/-- The Minkowski metric `η^{μν} = diag(1, -1, -1, -1)`. -/
def minkowski (μ ν : Fin 4) : ℂ := (minkowskiZ μ ν : ℂ)

/-- The four **Majorana matrices** `iγ^μ`, `μ = 0,1,2,3`, as `4×4` complex
matrices (the integer model cast into `ℂ`). -/
noncomputable def mgamma (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (Int.castRingHom ℂ).mapMatrix (mgammaZ μ)

/-- The fifth Majorana matrix `iγ⁵` as a complex matrix. -/
noncomputable def mgamma5 : Matrix (Fin 4) (Fin 4) ℂ :=
  (Int.castRingHom ℂ).mapMatrix mgamma5Z













/-- The **Dirac matrices** `γ^μ = -i (iγ^μ)` (Def 38). -/
noncomputable def dgamma (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-Complex.I) • mgamma μ



end BookProof.ChapterA3


