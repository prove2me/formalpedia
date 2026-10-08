-- Prove2me | Definitions.Def_ChapterPauliFundamental
-- name    : ChapterPauliFundamental
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:41:11.230231+00:00
-- url     : https://prove2.me/theorems/d9a6d301-7e49-4963-878c-d6aa898c329d
-- title:
--   Chapter PauliFundamental
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterPauliFundamental.lean`): generated def bundle for ChapterPauliFundamental. See BookProof/ChapterPauliFundamental.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterPauliFundamental.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterGammaCommutant
import Mathlib


/-!
# Note 36 — Pauli's fundamental theorem of the γ-matrices, proved

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §A.3, **Note 36**:

> Let `A^μ`, `B^μ` (`μ = 0,1,2,3`) be two sets of `4×4` complex matrices with
> `{A^μ, A^ν} = -2 η^{μν}`, `{B^μ, B^ν} = -2 η^{μν}`.  Then there is an invertible complex
> matrix `S` with `B^μ = S A^μ S⁻¹`, and `S` is unique up to a nonzero scalar.

`BookProof.ChapterA3b` carries this statement as the EXTERNAL named hypothesis
`PauliFundamental` (it is the only external input of §A.3, and the gap table of
`FORMALIZATION_ROADMAP.md` lists it as "not formalized"); Prop 37 (the real version) and
Lemma 40 are proved there *from* that hypothesis.  **This file proves the hypothesis**, so
`pauliFundamental` may be substituted wherever `PauliFundamental` was assumed.

## The proof

Everything is reduced to the *concrete* Majorana model `mgamma` of `BookProof.ChapterA3`.

* **The sixteen products.**  For `T : Finset (Fin 4)` let `gpF A T` be the product of the
  `A^μ`, `μ ∈ T`, in increasing order (`gp` over the list `sel T`).  The Clifford relations
  give the *shared* commutation rule `clifford_key`:
  `A^μ · gpF A T = sgnT μ T • gpF A (stepT μ T)`, where `stepT μ T = T Δ {μ}` and the sign
  `sgnT μ T = (-1)^#{ν ∈ T : ν < μ} · (μ ∈ T ? (A^μ)² : 1)` **depends only on `μ` and `T`** —
  the same function for every Clifford set, in particular for `mgamma`.
* **The intertwiner.**  `inter A F = ∑_T gpF A T · F · (G T)ᵀ`, with `G T = gpF mgamma T`
  (the concrete products are real orthogonal, so `(G T)ᵀ = (G T)⁻¹`).  The shared
  commutation rule plus the reindexing `T ↦ T Δ {μ}` (an involution of the index set) give
  `inter_intertwines`: `A^μ · inter A F = inter A F · mgamma μ`.
* **Nonvanishing.**  The concrete products are trace-orthogonal,
  `trace (G S · (G T)ᵀ) = 4 δ_{S,T}` (a finite integer computation), hence linearly
  independent, hence a basis of the `16`-dimensional matrix algebra.  If `inter A F = 0` for
  every `F`, taking `F` to be a matrix unit and pairing with `G U` forces every entry of
  every `gpF A T` to vanish — impossible, because `gpF A ∅ = 1`.
* **Invertibility.**  The kernel of a nonzero intertwiner is invariant under all `mgamma μ`,
  hence under all products `G T`, hence — as those span the whole matrix algebra — under
  every matrix; a nonzero vector in the kernel would therefore force the kernel to be
  everything, i.e. `S = 0`.  So `S` is injective and thus invertible.
* **Uniqueness** is `ChapterGammaCommutant.gamma_commutant_scalar` transported along `S`.

## Main results

* `exists_intertwiner` — every complex Clifford set is conjugate to the concrete Majorana
  set: `∃ S, IsUnit S.det ∧ ∀ μ, A μ = S * mgamma μ * S⁻¹`.
* `pauli_exists`, `pauli_unique` — the two halves of Note 36.
* **`pauliFundamental : PauliFundamental`** — the named hypothesis of `ChapterA3b`,
  discharged.
* `real_pauli'`, `chargeConj_unique'` — Prop 37 and the Lemma 40 uniqueness statement of
  `ChapterA3b`, now with no external input.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix Finset

namespace BookProof.ChapterPauliFundamental

open BookProof.ChapterA3 BookProof.ChapterGammaCommutant

/-- `4×4` complex matrices. -/
abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ

/-! ## The ordered products of a Clifford set -/

/-- The ordered product `A^{μ₁} ⋯ A^{μ_k}` along a list of indices. -/
noncomputable def gp (A : Fin 4 → M4) : List (Fin 4) → M4
  | [] => 1
  | μ :: t => A μ * gp A t



variable {A : Fin 4 → M4}







/-! ## The index bookkeeping (finite, decidable) -/

/-- The four indices in increasing order. -/
def idx : List (Fin 4) := [0, 1, 2, 3]

/-- The increasing list of the elements of `T`. -/
def sel (T : Finset (Fin 4)) : List (Fin 4) := idx.filter (fun x => x ∈ T)

/-- The elements of `T` below `μ`. -/
def lo (μ : Fin 4) (T : Finset (Fin 4)) : Finset (Fin 4) := T.filter (fun x => x < μ)

/-- The elements of `T` not below `μ`. -/
def hi (μ : Fin 4) (T : Finset (Fin 4)) : Finset (Fin 4) := T.filter (fun x => ¬ x < μ)

/-- The symmetric difference `T Δ {μ}`. -/
def stepT (μ : Fin 4) (T : Finset (Fin 4)) : Finset (Fin 4) :=
  if μ ∈ T then T.erase μ else insert μ T















theorem sel_empty : sel ∅ = [] := by decide

/-- The ordered product of the generators indexed by `T`. -/
noncomputable def gpF (A : Fin 4 → M4) (T : Finset (Fin 4)) : M4 := gp A (sel T)

@[simp] theorem gpF_empty (A : Fin 4 → M4) : gpF A ∅ = 1 := by
  rw [gpF, sel_empty]; rfl

/-- The sign produced when a generator is moved through an ordered product.  It depends only
on the index data, not on the Clifford set. -/
def sgnT (μ : Fin 4) (T : Finset (Fin 4)) : ℂ :=
  (-1) ^ ((lo μ T).card) * (if μ ∈ T then (if μ = 0 then (-1 : ℂ) else 1) else 1)



/-! ## The concrete products and their trace orthogonality -/

/-- The ordered products over `ℤ`, for the integer Majorana model. -/
def gpZ (A : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ) : List (Fin 4) → Matrix (Fin 4) (Fin 4) ℤ
  | [] => 1
  | μ :: t => A μ * gpZ A t

/-- The sixteen integer products of the Majorana matrices. -/
def GZ (T : Finset (Fin 4)) : Matrix (Fin 4) (Fin 4) ℤ := gpZ mgammaZ (sel T)





/-- The sixteen complex products of the Majorana matrices. -/
noncomputable def G (T : Finset (Fin 4)) : M4 := gpF mgamma T











/-! ## Linear independence and spanning of the sixteen products -/





/-! ## The intertwiner -/

/-- Pauli's averaged intertwiner `∑_T (A-product) · F · (γ-product)⁻¹`. -/
noncomputable def inter (A : Fin 4 → M4) (F : M4) : M4 :=
  ∑ T : Finset (Fin 4), gpF A T * F * (G T)ᵀ





/-! ## The intertwiner is not always zero -/



/-! ## Invertibility of a nonzero intertwiner -/






/-! ## Pauli's fundamental theorem -/











end BookProof.ChapterPauliFundamental


