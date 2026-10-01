-- Prove2me | Definitions.Def_ChapterA3d
-- name    : ChapterA3d
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:23:03.91182+00:00
-- url     : https://prove2.me/theorems/72aa3606-0787-41d6-acac-ccae718d4790
-- title:
--   Chapter A3d
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA3d.lean`): generated def bundle for ChapterA3d. See BookProof/ChapterA3d.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA3d.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3c
import Mathlib


/-!
# Chapter A, §A.3 — the discrete Pin subgroup `Ω` (Definition 49)

This file continues work-package **N4** of `FORMALIZATION_ROADMAP.md`
(book §A.3, line 5476), formalizing **Definition 49**: the *discrete Pin
subgroup*

`Ω := {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵} ⊆ Pin(3,1)`,

which is the **double cover of the discrete Lorentz subgroup**
`Δ := {1, η, -η, -1} ⊆ O(1,3)`.

Everything is stated over `ℝ` on the concrete `4×4` Majorana matrix model of
`ChapterA3.lean` / `ChapterA3c.lean`, and is fully self-contained: no external
hypothesis (no Pauli/Weyl input) is needed, since `Ω` is a finite explicit set
and each membership/`Λ`-value is a concrete matrix computation.

Deliverables:
* `OmegaPin`, `LorentzDelta` — the finite sets `Ω`, `Δ`.
* `omega_subset_pin` — every element of `Ω` is in `Pin(3,1)`.
* `lambda_omega_mem_delta` — `Λ(ω) ∈ Δ` for every `ω ∈ Ω` (the 2-to-1 cover
  `Ω → Δ`), with the explicit values `Λ(±iγ⁰) = η`, `Λ(±γ⁰γ⁵) = -η`,
  `Λ(±iγ⁵) = -1`, `Λ(±1) = 1`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open Matrix

namespace BookProof.ChapterA3

/-! ## The integer generators of `Ω` -/

/-- `iγ⁰` as an integer matrix (a generator of `Ω`). -/
def omegaA0Z : Matrix (Fin 4) (Fin 4) ℤ := mgammaZ 0

/-- `iγ⁵` as an integer matrix (a generator of `Ω`). -/
def omegaA5Z : Matrix (Fin 4) (Fin 4) ℤ := mgamma5Z

/-- `γ⁰γ⁵ = -(iγ⁰)(iγ⁵)` as an integer matrix (a generator of `Ω`). -/
def omegaG05Z : Matrix (Fin 4) (Fin 4) ℤ := -(mgammaZ 0 * mgamma5Z)

/-- The integer Minkowski metric as a matrix `η = diag(1,-1,-1,-1)`. -/
def minkowskiMatZ : Matrix (Fin 4) (Fin 4) ℤ := Matrix.of minkowskiZ



/-! ## The real generators of `Ω` -/

/-- `iγ⁰` as a real matrix. -/
noncomputable def omegaA0 : Matrix (Fin 4) (Fin 4) ℝ := mgammaR 0

/-- `iγ⁵` as a real matrix. -/
noncomputable def omegaA5 : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix omegaA5Z

/-- `γ⁰γ⁵` as a real matrix. -/
noncomputable def omegaG05 : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix omegaG05Z

/-- The **discrete Lorentz subgroup** `Δ = {1, η, -η, -1}`. -/
def LorentzDelta : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {1, minkowskiMat, -minkowskiMat, -1}

/-- The **discrete Pin subgroup** `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}`. -/
def OmegaPin : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {1, -1, omegaA0, -omegaA0, omegaG05, -omegaG05, omegaA5, -omegaA5}

/-! ## Generic helpers -/









/-! ## The generator `iγ⁰` -/









/-! ## The generator `iγ⁵` -/









/-! ## The generator `γ⁰γ⁵` -/









/-! ## The identity generators `±1` -/







/-! ## `Ω` covers `Δ` two-to-one -/







end BookProof.ChapterA3


