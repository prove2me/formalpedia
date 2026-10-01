-- Prove2me | Definitions.Def_ChapterA3c
-- name    : ChapterA3c
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:24:08.610604+00:00
-- url     : https://prove2.me/theorems/83c965b3-8dac-4b4c-b7a7-d1195ff0a30a
-- title:
--   Chapter A3c
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3c.lean`): generated def bundle for ChapterA3c. See BookProof/ChapterA3c.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3c.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
import Mathlib


/-!
# Chapter A, §A.3 — the group homomorphism `Λ : Pin(3,1) → O(1,3)` (Prop 46, group form)

This file completes work-package **N4**'s **Prop 46** of `FORMALIZATION_ROADMAP.md`
(book §A.3, line 5196): the *group-theoretic wrapper* of the metric-preservation
core `lorentz_of_conj` proved in `BookProof/ChapterA3b.lean`.

Working entirely over `ℝ` (the Majorana matrices `iγ^μ` have integer, hence real,
entries — `mgammaR`), we build:

* `LorentzO` — the Lorentz group `O(1,3) = {Λ | Λ η Λᵀ = η}`.
* `HasLambda S Λ` — the predicate that the real matrix `Λ` describes the
  conjugation action of `S` on the Majorana basis:
  `S⁻¹ (iγ^μ) S = Σ_ν Λ^μ_ν (iγ^ν)`.
* `IsPin S` — membership in `Pin(3,1)`: `|det S| = 1` and the conjugation action
  lands in `Maj = span_ℝ{iγ^μ}` (i.e. some `Λ` exists).
* `LambdaOf S` — the (well-defined, by linear independence `mgammaR_indep`)
  Lorentz matrix `Λ(S)`.

and prove the three headline properties of Prop 46:

* **Lands in `O(1,3)`** (`lambda_mem_lorentz`) — directly from `lorentz_of_conj`.
* **Homomorphism** (`lambdaOf_mul`) — `Λ(S₁ S₂) = Λ(S₁) Λ(S₂)`.
* **2-to-1 surjective** (`lambda_surjective`, `lambda_two_to_one`) — via the real
  Pauli theorem `real_pauli`; the fibre of `Λ` over any `λ ∈ O(1,3)` is exactly
  `{±S}`.

The only external input is the named hypothesis `PauliFundamental` (Note 36),
inherited from `ChapterA3b.real_pauli`; there is no `axiom`.
-/

open Matrix
open scoped ComplexConjugate

namespace BookProof.ChapterA3

/-! ## The real Majorana matrices -/

/-- The four Majorana matrices `iγ^μ` as **real** `4×4` matrices (integer model
cast into `ℝ`). -/
noncomputable def mgammaR (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (mgammaZ μ)

/-
The complexification of the real Majorana matrix is the complex one.
-/


/-
The real Majorana matrices form a real Clifford set.
-/


/-
**Linear independence of the Majorana basis.**  The four matrices `iγ^μ` are
`ℝ`-linearly independent, so a Lorentz matrix `Λ` describing the conjugation
action is unique.
-/


/-! ## The Lorentz group and the map `Λ` -/

/-- The Lorentz group `O(1,3) = {Λ ∈ Matrix (Fin 4) (Fin 4) ℝ | Λ η Λᵀ = η}`. -/
def LorentzO : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {Λ | Λ * minkowskiMat * Λᵀ = minkowskiMat}

/-- `HasLambda S Λ`: the real matrix `Λ` describes the conjugation action of `S`
on the Majorana basis, `S⁻¹ (iγ^μ) S = Σ_ν Λ^μ_ν (iγ^ν)`. -/
def HasLambda (S Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ μ, S⁻¹ * mgammaR μ * S = ∑ ν, Λ μ ν • mgammaR ν

/-- Membership in `Pin(3,1)`: `S` is invertible with `|det S| = 1` and its
conjugation action on the Majorana basis lands in `Maj = span_ℝ{iγ^μ}`. -/
def IsPin (S : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  IsUnit S.det ∧ |S.det| = 1 ∧ ∃ Λ, HasLambda S Λ

open Classical in
/-- The Lorentz matrix `Λ(S)` associated to `S` (junk `0` when `S ∉ Pin(3,1)`). -/
noncomputable def LambdaOf (S : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  if h : ∃ Λ, HasLambda S Λ then h.choose else 0



/-
**Uniqueness of `Λ`** (from linear independence of the Majorana basis).
-/


/-! ## Prop 46(a) — `Λ(S)` lands in `O(1,3)` -/

/-
**Real form of `lorentz_of_conj`.**  If `S` is invertible and `HasLambda S Λ`,
then `Λ ∈ O(1,3)`.
-/




/-! ## Prop 46(b) — `Λ` is a homomorphism -/

/-
`HasLambda` composes: if `S₁, S₂` are invertible with `HasLambda S₁ Λ₁` and
`HasLambda S₂ Λ₂`, then `HasLambda (S₁ S₂) (Λ₁ Λ₂)`.
-/


/-
`Pin(3,1)` is closed under multiplication.
-/




/-! ## Prop 46(c) — `Λ` is 2-to-1 surjective -/

/-
The Majorana-basis combination `β^μ = Σ_ν Λ^μ_ν (iγ^ν)` of a Lorentz matrix
`Λ` is again a real Clifford set.
-/


/-
`-S` is again in `Pin(3,1)` with the same Lorentz image.
-/






/-
**Prop 46 (surjectivity).** Every `Λ ∈ O(1,3)` is `Λ(S)` for some
`S ∈ Pin(3,1)`.  (Uses the real Pauli theorem, hence the named hypothesis
`PauliFundamental`.)
-/


/-
**Prop 46 (2-to-1).** Two Pin elements with the same Lorentz image differ by a
sign: the fibre of `Λ` over any `λ ∈ O(1,3)` is exactly `{±S}`.
-/


end BookProof.ChapterA3


