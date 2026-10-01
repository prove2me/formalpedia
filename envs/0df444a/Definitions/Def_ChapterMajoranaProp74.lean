-- Prove2me | Definitions.Def_ChapterMajoranaProp74
-- name    : ChapterMajoranaProp74
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T08:50:24.407633+00:00
-- url     : https://prove2.me/theorems/396403b9-1bb8-4a43-a345-fd0da337100d
-- title:
--   Chapter MajoranaProp74
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMajoranaProp74.lean`): generated def bundle for ChapterMajoranaProp74. See BookProof/ChapterMajoranaProp74.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp74.lean

import Definitions.Def_ChapterMajoranaFourier
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"Fourier-Majorana Transform", **Proposition 74** — the inverse Majorana–Fourier
intertwining identities

`book.tex` **Proposition 74** (line ~6003) states that the inverse Majorana–Fourier
transform `𝓕_M⁻¹ = (𝓕_P^Θ)⁻¹ ∘ S⁻¹` intertwines the Dirac operator with a momentum
multiplier:

  `(γ⁰ γ⃗·∂⃗ + i γ⁰ m) 𝓕_M⁻¹{Ψ} = (𝓕_M⁻¹ ∘ R){Ψ}`,   `R{Ψ}(p⃗) = i γ⁰ E_p Ψ(p⃗)`,
  `∂ⱼ 𝓕_M⁻¹{Ψ} = (𝓕_M⁻¹ ∘ Rⱼ){Ψ}`,                     `Rⱼ{Ψ}(p⃗) = i γ⁰ pⱼ Ψ(p⃗)`.

Writing `𝓕_M⁻¹ = (𝓕_P^Θ)⁻¹ ∘ S⁻¹`, the book reduces both statements to purely
algebraic `2×2`-block identities over the Dirac matrices, on the two-component
`(+p⃗, −p⃗)` momentum splitting:

* `Q ∘ S⁻¹ = S⁻¹ ∘ R`, where
  `Q = [[i γ⁰ m, i p⃗·γ⃗], [−i p⃗·γ⃗, i γ⁰ m]]`,
  `S⁻¹ = [[c, s A], [−s A, c]]`,
  `R = diag(i γ⁰ E, i γ⁰ E)`,
  with `A = (n̂·γ⃗) γ⁰`, `c = √((E+m)/(2E))`, `s = √((E−m)/(2E))`, `p⃗ = |p⃗| n̂`;
* `Rⱼ ∘ S⁻¹ = S⁻¹ ∘ Rⱼ`, i.e. the diagonal block `Dⱼ = diag(i γ⁰ pⱼ, −i γ⁰ pⱼ)`
  commutes with `S⁻¹`.

This file formalizes exactly those two block identities, reusing the concrete `4×4`
Dirac model and the boost coefficients from `BookProof.ChapterMajoranaFourier`
(`dgamma`, `nslash`, `Aop`, `boostC`, `boostS`, `Ep` and the Clifford relations
`gamma0_sq`, `nslash_sq`, `gamma0_nslash_anticomm`).  Both identities are proved
first as **abstract** statements for any pair `g, ns` of `4×4` complex matrices
satisfying the Majorana relations `g² = 1`, `ns² = −1`, `g·ns = −ns·g`, and then
instantiated on the concrete Dirac model.

The surrounding analytic content (the integral transforms `𝓕_P`, `𝓕_M` and their
inverses) is left as prose; here we discharge the finite linear-algebra core on
which the book's proof rests.  This stays **off the gravity line** and **off the
Hankel-transform line**.

Everything is `sorry`-free and `axiom`-free.
-/

open Matrix

namespace BookProof.ChapterMajoranaProp74

open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

/-! ## The block operators of Proposition 74 -/

/-- The Dirac-operator momentum block `Q = [[i γ⁰ m, i p⃗·γ⃗], [−i p⃗·γ⃗, i γ⁰ m]]`,
with `g = γ⁰` and `ns = p⃗·γ⃗ / |p⃗|` scaled by the modulus `q = |p⃗|`. -/
noncomputable def Qmat (g ns : Matrix (Fin 4) (Fin 4) ℂ) (m q : ℝ) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ :=
  Matrix.fromBlocks (((m : ℂ) * Complex.I) • g) (((q : ℂ) * Complex.I) • ns)
    ((-((q : ℂ) * Complex.I)) • ns) (((m : ℂ) * Complex.I) • g)

/-- The inverse boost-mixing block `S⁻¹ = [[c, s A], [−s A, c]]`. -/
noncomputable def Sinv (A : Matrix (Fin 4) (Fin 4) ℂ) (c s : ℝ) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ :=
  Matrix.fromBlocks ((c : ℂ) • 1) ((s : ℂ) • A) ((-(s : ℂ)) • A) ((c : ℂ) • 1)

/-- The energy multiplier block `R = diag(i γ⁰ E, i γ⁰ E)`. -/
noncomputable def Rmat (g : Matrix (Fin 4) (Fin 4) ℂ) (E : ℝ) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ :=
  Matrix.fromBlocks (((E : ℂ) * Complex.I) • g) 0 0 (((E : ℂ) * Complex.I) • g)

/-- The momentum-component multiplier block `Dⱼ = diag(i γ⁰ pⱼ, −i γ⁰ pⱼ)`. -/
noncomputable def Dmat (g : Matrix (Fin 4) (Fin 4) ℂ) (pj : ℝ) :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℂ :=
  Matrix.fromBlocks (((pj : ℂ) * Complex.I) • g) 0 0 ((-((pj : ℂ) * Complex.I)) • g)

/-! ## Clifford consequences for `A = ns · g` -/

/-
`ns · A = −g` when `A = ns·g` and `ns² = −1`.
-/


/-
`g · A = −ns` when `A = ns·g`, `g·ns = −ns·g` and `g² = 1`.
-/


/-
`A · g = ns` when `A = ns·g` and `g² = 1`.
-/


/-! ## The abstract intertwining identities -/

/-
**Proposition 74, first identity (abstract).** For any `4×4` matrices `g, ns`
with `g² = 1`, `ns² = −1`, `g·ns = −ns·g`, and reals `c, s, m, q, E` with
`c² + s² = 1`, `m = (c²−s²)E`, `q = 2csE`, the Dirac-operator block `Q`
intertwines with the boost mixing `S⁻¹` and the energy multiplier `R`:
`Q · S⁻¹ = S⁻¹ · R`.
-/


/-
**Proposition 74, second identity (abstract).** For any `4×4` matrices `g, ns`
with `g² = 1` and `g·ns = −ns·g`, the diagonal momentum-component block `Dⱼ`
commutes with the boost mixing `S⁻¹`: `Dⱼ · S⁻¹ = S⁻¹ · Dⱼ`.
-/


/-! ## The concrete Dirac-model instantiations -/

/-
**Proposition 74, first identity (concrete Dirac model).** With `g = γ⁰`,
`ns = p⃗·γ⃗/|p⃗|`, `A = (n̂·γ⃗) γ⁰`, boost coefficients `c, s` for mass `m ≥ 0` and
momentum modulus `q > 0`, and energy `E = √(q²+m²)`, the Dirac-operator block `Q`
intertwines with `S⁻¹` and the energy multiplier `R`.
-/


/-
**Proposition 74, second identity (concrete Dirac model).** With `g = γ⁰` and
`A = (n̂·γ⃗) γ⁰`, the diagonal momentum-component block `Dⱼ` commutes with `S⁻¹`.
-/


end BookProof.ChapterMajoranaProp74


