-- Prove2me | Definitions.Def_ChapterA5
-- name    : ChapterA5
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T11:26:15.039469+00:00
-- url     : https://prove2.me/theorems/e81cad5f-f214-49bb-aef9-f91c698d0b15
-- title:
--   Chapter A5
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterA5.lean`): generated def bundle for ChapterA5. See BookProof/ChapterA5.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterA5.lean

import Definitions.Def_ChapterA3c
import Mathlib


/-!
# Chapter A §A.5 — Spinor frame and the CPT / energy operator (work-package N4)

Source: `book.tex` line 6453 (*"Spinor frame and CPT theorem"*).

The book's §A.5 closing statement is that, in space coordinates, **the most
general mass term in the Hamiltonian `iH` that is covariant under the connected
component of the Lorentz group** is

`iH = ∂⃗·γ⃗γ⁰ + iγ⁰ m₁ + γ⁰γ⁵ m₂`,

and, being real in the Majorana basis, it is automatically invariant under a
parity–time-reversal transformation (PT) — *this is essentially the CPT theorem*.

This file formalizes the concrete, self-contained mathematical core of that
statement on the `4×4` Majorana Clifford model of §A.3 (`ChapterA3`): the five
coefficient matrices of `iH`,

* `coeffBoostZ j := γʲγ⁰ = -(iγʲ)(iγ⁰)` for `j = 1,2,3` (the spatial-gradient
  coefficients `∂ⱼ ↦ γʲγ⁰`),
* `coeffMass1Z := iγ⁰` (the parity-even mass `m₁`),
* `coeffMass2Z := γ⁰γ⁵ = -(iγ⁰)(iγ⁵)` (the parity-odd / chiral mass `m₂`),

form a **generalized anticommuting (Clifford) system**: the five matrices
mutually anticommute, with `(γʲγ⁰)² = 1` and `(iγ⁰)² = (γ⁰γ⁵)² = -1`.  All five
are **real integer matrices** — the Majorana (reality) property that underlies
CPT invariance.

Consequently the momentum-space symbol
`D(p⃗, m₁, m₂) := p₁ γ¹γ⁰ + p₂ γ²γ⁰ + p₃ γ³γ⁰ + m₁ iγ⁰ + m₂ γ⁰γ⁵`
satisfies the **mass-shell identity**
`D² = (p₁² + p₂² + p₃² - m₁² - m₂²) · 1`
(equivalently `H² = |p⃗|² + m₁² + m₂²`, the Klein–Gordon relation with the two
independent masses combining as `m² = m₁² + m₂²`).

Everything is proved on the integer model (`decide`) and transported to the real
and complex Majorana matrices via `(Int.castRingHom _).mapMatrix`, so it is
`sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`),
with **no `EXTERNAL` hypothesis** (the covariance statements that motivate the
form of `iH` are the §A.3 results `spinBoost_hasAdLambda` / `spinRot_hasAdLambda`;
the PT/CPT physics discussion is captured in these docstrings, not as theorems).
-/

open Matrix

namespace BookProof.ChapterA5

open BookProof.ChapterA3

/-- The spatial index `j ↦ j+1 : Fin 4` (so `j = 0,1,2 ↦ 1,2,3`). -/
def spatialIdx (j : Fin 3) : Fin 4 := ⟨j.val + 1, by omega⟩

/-! ## Integer model of the coefficient matrices of `iH` -/

/-- The spatial-gradient coefficient `γʲγ⁰ = -(iγʲ)(iγ⁰)` (`j = 1,2,3`), over `ℤ`. -/
def coeffBoostZ (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℤ :=
  -(mgammaZ (spatialIdx j) * mgammaZ 0)

/-- The parity-even mass coefficient `iγ⁰`, over `ℤ`. -/
def coeffMass1Z : Matrix (Fin 4) (Fin 4) ℤ := mgammaZ 0

/-- The parity-odd (chiral) mass coefficient `γ⁰γ⁵ = -(iγ⁰)(iγ⁵)`, over `ℤ`. -/
def coeffMass2Z : Matrix (Fin 4) (Fin 4) ℤ := -(mgammaZ 0 * mgamma5Z)

/-! ### Squares -/







/-! ### Anticommutation (the generalized Clifford relations) -/









/-! ## The energy-operator symbol and the mass-shell identity -/

/-- The momentum-space symbol of `iH` at 3-momentum `p⃗` and masses `m₁, m₂`
(integer model): `D = p₁ γ¹γ⁰ + p₂ γ²γ⁰ + p₃ γ³γ⁰ + m₁ iγ⁰ + m₂ γ⁰γ⁵`. -/
def energySymbolZ (p : Fin 3 → ℤ) (m₁ m₂ : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  p 0 • coeffBoostZ 0 + p 1 • coeffBoostZ 1 + p 2 • coeffBoostZ 2
    + m₁ • coeffMass1Z + m₂ • coeffMass2Z

/-
**Mass-shell identity (integer model).**  The energy-operator symbol squares
to the scalar `|p⃗|² - m₁² - m₂²`; equivalently `H² = |p⃗|² + m₁² + m₂²`, the
Klein–Gordon relation with the two masses combining as `m² = m₁² + m₂²`.
-/


/-! ## Real Majorana model (the physical, reality/CPT form) -/

/-- The spatial-gradient coefficient `γʲγ⁰` as a **real** matrix. -/
noncomputable def coeffBoostR (j : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix (coeffBoostZ j)

/-- The mass coefficient `iγ⁰` as a **real** matrix. -/
noncomputable def coeffMass1R : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix coeffMass1Z

/-- The chiral mass coefficient `γ⁰γ⁵` as a **real** matrix. -/
noncomputable def coeffMass2R : Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix coeffMass2Z

/-- The real energy-operator symbol. -/
noncomputable def energySymbolR (p : Fin 3 → ℝ) (m₁ m₂ : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  p 0 • coeffBoostR 0 + p 1 • coeffBoostR 1 + p 2 • coeffBoostR 2
    + m₁ • coeffMass1R + m₂ • coeffMass2R



end BookProof.ChapterA5


