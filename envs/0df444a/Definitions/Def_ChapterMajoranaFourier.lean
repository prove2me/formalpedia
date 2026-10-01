-- Prove2me | Definitions.Def_ChapterMajoranaFourier
-- name    : ChapterMajoranaFourier
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:12:32.338031+00:00
-- url     : https://prove2.me/theorems/a67745ee-283c-4a4c-98a8-214967ced436
-- title:
--   Chapter MajoranaFourier
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMajoranaFourier.lean`): generated def bundle for ChapterMajoranaFourier. See BookProof/ChapterMajoranaFourier.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaFourier.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter A, §A.5 — the algebraic core of the Majorana–Fourier boost (Prop 73)

`book.tex` (§A.5, "Application to the momentum of Majorana spinor fields",
Proposition 73) proves that the **Majorana–Fourier transform**
`𝓕_M = S ∘ 𝓕_P^Θ` is unitary by reducing to the statement that the explicit
`2×2` block "boost mixing" matrix

```
S = [ c      -s·A ]
    [ s·A     c   ]
```

is **orthogonal / unitary**, where

* `c = √((E+m)/(2E))`, `s = √((E-m)/(2E))` are the boost half-angle coefficients
  (`E = √(q²+m²)` the relativistic energy, `q = |p⃗|` the momentum modulus,
  `m ≥ 0` the mass), and
* `A = (n̂·γ⃗) γ⁰` is built from the Dirac spatial slash of the unit momentum
  direction `n̂` (`Σ nᵢ² = 1`).

This file formalizes exactly that algebraic core, reusing the concrete `4×4`
Dirac model `BookProof.ChapterA3.dgamma`:

* the real half-angle identities `c² + s² = 1`, `c² − s² = m/E`, `2cs = q/E`;
* `A` is a **Hermitian involution** (`Aᴴ = A`, `A² = 1`), hence unitary;
* the abstract block lemma: for any Hermitian involution `A` and reals `c,s`
  with `c² + s² = 1`, the block matrix `S` is unitary (`Sᴴ S = 1`);
* the headline `majoranaFourier_boostBlock_unitary`: the concrete boost mixing
  matrix of Proposition 73 is unitary.

The surrounding analytic content (the integral operators `𝓕_P`, `𝓕_M` and their
unitarity as operators on `L²`) is left as prose; here we discharge the finite
linear-algebra identity on which the book's proof rests.

Everything is `sorry`-free and `axiom`-free.
-/

open Matrix

namespace BookProof.ChapterMajoranaFourier

open BookProof.ChapterA3

/-! ## The boost half-angle coefficients -/

/-- Relativistic energy `E = √(q² + m²)`. -/
noncomputable def Ep (m q : ℝ) : ℝ := Real.sqrt (q ^ 2 + m ^ 2)

/-- Boost half-angle cosine-type coefficient `c = √((E+m)/(2E))`. -/
noncomputable def boostC (m q : ℝ) : ℝ := Real.sqrt ((Ep m q + m) / (2 * Ep m q))

/-- Boost half-angle sine-type coefficient `s = √((E−m)/(2E))`. -/
noncomputable def boostS (m q : ℝ) : ℝ := Real.sqrt ((Ep m q - m) / (2 * Ep m q))









/-
`c² + s² = 1`: the boost mixing coefficients lie on the unit circle.
-/


/-
`c² − s² = m/E`.
-/


/-
`2cs = q/E`.
-/


/-! ## Hermiticity of the Dirac matrices in the Majorana model -/





 

/-
`(γ⁰)² = 1`.
-/


/-
`γ⁰` anticommutes with each spatial `γⁱ` (`i = 0,1,2 ↦ γ^{i+1}`).
-/


/-! ## The direction slash `A = (n̂·γ⃗) γ⁰` -/

/-- Spatial Dirac slash of a real 3-vector `n`, `n̸ = Σ nᵢ γ^{i+1}`. -/
noncomputable def nslash (n : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ i : Fin 3, (n i : ℂ) • dgamma i.succ

/-- The Prop-73 direction matrix `A = n̸ · γ⁰`. -/
noncomputable def Aop (n : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  nslash n * dgamma 0

/-
The spatial slash is anti-Hermitian: `n̸ᴴ = −n̸`.
-/


/-
`γ⁰` anticommutes with the whole spatial slash: `γ⁰ n̸ = −n̸ γ⁰`.
-/


/-
Each spatial `γⁱ` squares to `−1`.
-/


/-
Distinct spatial `γⁱ`, `γʲ` anticommute.
-/


/-
For a **unit** direction, the slash squares to `−1`: `n̸² = −1`.
-/


/-
`A = n̸ γ⁰` is Hermitian.
-/


/-
For a unit direction, `A = n̸ γ⁰` is an involution: `A² = 1`.
-/


/-! ## The abstract boost block and its unitarity -/

/-- The `2×2` block boost mixing matrix `S = [[c, −s·A],[s·A, c]]`. -/
noncomputable def boostBlock (c s : ℝ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ :=
  Matrix.fromBlocks ((c : ℂ) • 1) ((-(s : ℂ)) • A) ((s : ℂ) • A) ((c : ℂ) • 1)

/-
**Abstract boost-block unitarity.** For any Hermitian involution `A`
(`Aᴴ = A`, `A² = 1`) and reals `c, s` with `c² + s² = 1`, the block matrix
`S = [[c, −s·A],[s·A, c]]` satisfies `Sᴴ S = 1`.
-/




end BookProof.ChapterMajoranaFourier


