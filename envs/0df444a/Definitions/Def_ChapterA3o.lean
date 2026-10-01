-- Prove2me | Definitions.Def_ChapterA3o
-- name    : ChapterA3o
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:25:51.358668+00:00
-- url     : https://prove2.me/theorems/9f0496bf-4bc3-4fca-abb5-1fe1d5f058fc
-- title:
--   Chapter A3o
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3o.lean`): generated def bundle for ChapterA3o. See BookProof/ChapterA3o.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3o.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3n
import Mathlib


/-!
# Chapter A, §A.3 — Note 51 / Lemma 52: the arbitrary `N`-fold *antisymmetric* power

Source: `book.tex` §A.3, Notes 50–51 and Lemma 52 (line ~5560), together with
Def 57 (`Pinor₀` = the **antisymmetric** pair of Majorana spinors).

`ChapterA3n` built, for arbitrary `N`, the totally *symmetric* power `V^{⊙N}`
via the symmetrizer `projSym N = (N!)⁻¹·Σ_{σ∈S_N} ρ(σ)`.  This file is the exact
dual construction: the totally *antisymmetric* power (the `N`-fold exterior power
`Λ^N V`), whose base case `N = 2` is the antisymmetric pair `Pinor₀` of Def 57.

It reuses the tensor model of `ChapterA3n` verbatim — the carrier
`MN N = Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ`, the tensor operator
`tensorPow`, the permutation representation `permMat`, the diagonal `Spin⁺`
generator `diagGen`, and the uniform parity operator `uniform` — and only changes
the group average from the trivial character to the **sign** character `sgn : S_N → {±1}`.

## The construction

The total **antisymmetrizer**

  `projAnti N := (N!)⁻¹ • Σ_{σ∈S_N} sgn(σ)·permMat σ`

is a genuine projector (`projAnti_idem`) onto the exterior power `Λ^N V`.  Its
idempotency is the *signed* group identity

  `(Σ_σ sgn(σ)·ρ(σ))² = N!·Σ_σ sgn(σ)·ρ(σ)`  (`sum_signed_permMat_sq`),

which holds because `sgn` is a homomorphism valued in `{±1}` (so
`sgn(σ)·sgn(σ⁻¹ρ) = sgn(ρ)` after the reindexing `ρ = στ`).

## The Lemma-52 payoff (antisymmetric case)

Because *every* braiding `permMat σ` already commutes with the diagonal `Spin⁺`
generator `diagGen A` and the uniform parity operator `uniform A`
(`ChapterA3n.permMat_diagGen_comm`, `ChapterA3n.permMat_uniform_comm`), so does
any linear combination of them — in particular the signed average `projAnti N`
(`projAnti_diagGen_comm`, `projAnti_uniform_comm`).  Specialising to the §A.3
data gives the headline statement exactly as in the symmetric case: the
antisymmetric power is a **full-Lorentz** subrepresentation, invariant under the
diagonal `Spin⁺` generators `γ^μγ^ν` (`projAnti_spinGenDiag_comm`) **and** under
diagonal parity `γ⁰⊗…⊗γ⁰` (`projAnti_parityDiag_comm`).

Everything is `sorry`-free / `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`), with **no `EXTERNAL` hypothesis** (Note 50 / Weyl complete
reducibility remains the cited backbone).  Together with `ChapterA3n` this
completes the pair of totally (anti)symmetric tensor-power constructions of
Notes 50–51 / Def 57.
-/

open Matrix
open scoped BigOperators

namespace BookProof.ChapterA3o

open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3n

/-- The sign of a permutation as a complex scalar `±1`. -/
noncomputable def signC {N : ℕ} (σ : Equiv.Perm (Fin N)) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ)

/-- The total **antisymmetrizer** `projAnti N = (N!)⁻¹ • Σ_{σ∈S_N} sgn(σ)·permMat σ`
onto the exterior power `Λ^N V`. -/
noncomputable def projAnti (N : ℕ) : MN N :=
  (Nat.factorial N : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), signC σ • permMat σ

/-! ## The signed group identity -/

/-
The signed core group identity `(Σ_{σ∈S_N} sgn(σ)·ρ(σ))² = N!·Σ_{σ} sgn(σ)·ρ(σ)`.
Multiplying the signed group sum by itself and reindexing `ρ = στ` gives `|S_N| = N!`
copies of the signed group sum, using that `sgn` is a `{±1}`-valued homomorphism.
-/




/-! ## The Lemma-52 payoff — the antisymmetric power is a full-Lorentz subrepresentation -/









end BookProof.ChapterA3o


