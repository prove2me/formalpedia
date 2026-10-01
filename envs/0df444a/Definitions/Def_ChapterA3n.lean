-- Prove2me | Definitions.Def_ChapterA3n
-- name    : ChapterA3n
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:27:10.180986+00:00
-- url     : https://prove2.me/theorems/8c7a2eff-9f40-4e77-a93a-937bb5e3681b
-- title:
--   Chapter A3n
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3n.lean`): generated def bundle for ChapterA3n. See BookProof/ChapterA3n.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3n.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Mathlib


/-!
# Chapter A, §A.3 — Note 51 / Lemma 52: the arbitrary `N`-fold symmetric power

Source: `book.tex` §A.3, Notes 50–51 and Lemma 52 (line ~5560).

`ChapterA3l` (two-fold, `S₂`) and `ChapterA3m` (three-fold, `S₃`) built the
braiding / symmetrizer structure at the first two symmetric tensor powers.  This
file takes the **general step**: for *arbitrary* `N` it formalizes the `N`-fold
tensor product `V^{⊗N}` and the action of the full symmetric group `S_N` by
braidings, culminating in the Lemma-52 payoff that the total symmetrizer
`projSym = (1/N!)·Σ_{σ∈S_N} ρ(σ)` is a genuine projector onto a **full-Lorentz**
subrepresentation (the symmetric power `V^{⊙N}`, carrier of the top irrep
`V⁺_{N/2}`).

## The model

Rather than iterated (left-associated) Kronecker products, we use the clean
`N`-fold tensor model: the carrier is `Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ`,
indexed by *tuples* `a : Fin N → Fin 4`.  A family of single-slot operators
`M : Fin N → Matrix (Fin 4) (Fin 4) ℂ` acts as the tensor operator

  `tensorPow M := a b ↦ ∏ i, (M i) (a i) (b i)`  (the `N`-fold `⊗ᵢ Mᵢ`),

which is *multiplicative* (`tensorPow M * tensorPow M' = tensorPow (M·M')`,
`tensorPow_mul`) and unital (`tensorPow_one`) because a sum over tuples of a
product factorises (`Finset.prod_univ_sum`).  A permutation `σ : S_N` acts by the
slot-braiding permutation matrix

  `permMat σ := a b ↦ [b = a ∘ σ]`,

a homomorphism `permMat σ * permMat τ = permMat (σ·τ)` (`permMat_mul`,
`permMat_one`).  The two interact by the **braiding relation**

  `permMat σ * tensorPow M = tensorPow (M ∘ σ⁻¹) * permMat σ`  (`permMat_braiding`).

## The Lemma-52 payoff

* The **diagonal** `Spin⁺` generator `diagGen A := Σᵢ (1⊗…⊗A⊗…⊗1)` and the
  **uniform** parity operator `uniform A := A⊗…⊗A` each commute with every
  `permMat σ` (`permMat_diagGen_comm`, `permMat_uniform_comm`) — the totally
  symmetric diagonal action is invariant under any permutation of the `N` slots.
* Hence the total symmetrizer `projSym N := (N!)⁻¹ • Σ_{σ} permMat σ` is a genuine
  **projector** (`projSym_idem`, encoding `(Σ_σ σ)² = N!·Σ_σ σ`) that commutes
  with `diagGen A` and `uniform A` (`projSym_diagGen_comm`, `projSym_uniform_comm`).
* Specialising `A` to the §A.3 data gives the headline statement: the symmetric
  power is a full-Lorentz subrepresentation, invariant under the diagonal `Spin⁺`
  generators `γ^μγ^ν` (`projSym_spinGenDiag_comm`) **and** under diagonal parity
  `γ⁰⊗…⊗γ⁰` (`projSym_parityDiag_comm`).

Everything is `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`), with **no `EXTERNAL` hypothesis** (Note 50 / Weyl complete
reducibility remains the cited backbone).  This generalises the concrete `N = 2`
(`ChapterA3l`) and `N = 3` (`ChapterA3m`) constructions to all `N`.
-/

open Matrix
open scoped BigOperators

namespace BookProof.ChapterA3n

open BookProof.ChapterA3 BookProof.ChapterA3j

/-- The index type of the `N`-fold tensor product: tuples `Fin N → Fin 4`. -/
abbrev Idx (N : ℕ) := Fin N → Fin 4

/-- The `4^N`-dimensional carrier space `V^{⊗N}` of `N` Dirac spinors, modeled as
matrices indexed by tuples `Fin N → Fin 4`. -/
abbrev MN (N : ℕ) := Matrix (Idx N) (Idx N) ℂ

/-- The `N`-fold tensor operator `⊗ᵢ Mᵢ` built from a family of single-slot
operators `M : Fin N → Matrix (Fin 4) (Fin 4) ℂ`:
`(tensorPow M) a b = ∏ i, (M i) (a i) (b i)`. -/
noncomputable def tensorPow {N : ℕ} (M : Fin N → Matrix (Fin 4) (Fin 4) ℂ) : MN N :=
  Matrix.of fun a b => ∏ i, M i (a i) (b i)

/-- The slot-braiding permutation matrix of `σ : S_N`, acting on `V^{⊗N}` by
permuting the tensor factors: `(permMat σ) a b = [b = a ∘ σ]`. -/
noncomputable def permMat {N : ℕ} (σ : Equiv.Perm (Fin N)) : MN N :=
  Matrix.of fun a b => if b = a ∘ σ then (1 : ℂ) else 0

/-- The **diagonal** `Spin⁺` generator built from a single-slot operator `A`:
`diagGen A = Σᵢ (1 ⊗ … ⊗ A ⊗ … ⊗ 1)` with `A` in slot `i`. -/
noncomputable def diagGen {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : MN N :=
  ∑ i : Fin N, tensorPow (fun j => if j = i then A else 1)

/-- The **uniform** (diagonal-parity type) operator `A ⊗ … ⊗ A`. -/
noncomputable def uniform {N : ℕ} (A : Matrix (Fin 4) (Fin 4) ℂ) : MN N :=
  tensorPow (fun _ => A)

/-- The total symmetrizer `projSym N = (N!)⁻¹ • Σ_{σ∈S_N} permMat σ` onto the
symmetric power `V^{⊙N}`. -/
noncomputable def projSym (N : ℕ) : MN N :=
  (Nat.factorial N : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), permMat σ

/-! ## Multiplicativity of the tensor operator -/

/-
The tensor operator is multiplicative: `(⊗ᵢ Mᵢ)(⊗ᵢ M'ᵢ) = ⊗ᵢ (Mᵢ M'ᵢ)`.
This is the factorisation of a sum over tuples of a product of factors.
-/


/-
The tensor operator of the all-identity family is the identity.
-/


/-! ## The permutation representation -/

/-
`permMat` is a homomorphism from `S_N`: `permMat σ * permMat τ = permMat (σ*τ)`.
-/


/-
`permMat` sends the identity permutation to the identity matrix.
-/


/-! ## The braiding relation -/

/-
**Braiding relation**: conjugating the tensor operator by a permutation
matrix permutes the single-slot operators,
`permMat σ * tensorPow M = tensorPow (fun j => M (σ⁻¹ j)) * permMat σ`.
-/


/-! ## Each permutation commutes with the diagonal action -/

/-
Every braiding commutes with the uniform (diagonal-parity) operator, since
permuting identical factors leaves the tensor unchanged.
-/


/-
Every braiding commutes with the diagonal `Spin⁺` generator, since permuting
the slots merely reindexes the sum `Σᵢ (1⊗…⊗A⊗…⊗1)`.
-/


/-! ## The total symmetrizer -/

/-
The core group identity `(Σ_{σ∈S_N} σ)² = N!·(Σ_{σ∈S_N} σ)`: multiplying the
group sum by itself and reindexing gives `|S_N| = N!` copies of the group sum.
-/


/-
`projSym N` is idempotent — a genuine projector onto the symmetric power.
-/


/-
The symmetrizer commutes with the uniform (diagonal-parity) operator.
-/


/-
The symmetrizer commutes with the diagonal `Spin⁺` generator.
-/


/-! ## Lemma 52 payoff — the symmetric power is a full-Lorentz subrepresentation -/





end BookProof.ChapterA3n


