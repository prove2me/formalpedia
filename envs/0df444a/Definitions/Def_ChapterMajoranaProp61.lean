-- Prove2me | Definitions.Def_ChapterMajoranaProp61
-- name    : ChapterMajoranaProp61
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-08T01:39:49.922711+00:00
-- url     : https://prove2.me/theorems/91980f94-72ab-4414-81ae-d05abad2b77a
-- title:
--   Majorana properties 61
-- statement:
--   Formal definitions for the Majorana properties 61 of the timepiece Lean 4 formalization (module `BookProof.MajoranaProp61`, source chapter `BookProof/ChapterMajoranaProp61.lean`).
--
--   `book.tex` **Proposition 61** (line ~5712) states: given a unitary operator `U : Pinorⱼ(ℝ³) → Pinorⱼ(𝕏)` with `U ∘ H² = E² ∘ U`, where `iH = γ⁰ (∂⃗·γ⃗) + iγ⁰ m` is the Majorana/Dirac Hamiltonian (`H` self-adjoint) and `E(X) ≥ m ≥ 0`, the operator
--
--   `U' ≡ (E + U H γ⁰ U†) / (√(E+m) √(2E))`
--
--   is unitary.
--
--   The book's proof is the algebraic identity `(U')† U' = 1` (and `U' (U')† = 1`), which rests on three facts coming from the Majorana setup:
--
--   * the Clifford **anticommutation** `H γ⁰ + γ⁰ H = 2m` (from `iH = γ⁰(∂⃗·γ⃗) + iγ⁰ m` and `(γ⁰)² = 1`, `{γʲ, γ⁰} = 0`), * the intertwining relation, i.e. `E² = U H² U†`, * `E = √(E²)` (hence also the normaliser `√(2E(E+m))`) **commutes** with `A := U H γ⁰ U†`.
--
--   We formalize exactly this algebraic core in a general `ℝ`-star-algebra `𝒜` (playing the role of the bounded operators on the pinor space): `U` unitary, `g = γ⁰` a self-adjoint involution, `H` self-adjoint with the anticommutator `H*g + g*H = (2m)•1`, `E` self-adjoint with `E*E = U*H²*U†`, `A := U*H*g*U†` commuting with `E`, and a self-adjoint invertible normaliser `N` (`= √(2E(E+m))`) with `N*N = 2•E² + (2m)•E` commuting with `E` and `A`.
--
--   We prove:
--
--   * `gsq_Hsq_comm` — `g*(H*H) = (H*H)*g` follows *purely* from the anticommutator * `prop61_star_mul_self` — `(U')† U' = 1` * `prop61_mul_star_self` — `U' (U')† = 1` * `prop61_isUnit` — `U'` is a unit (two-sided inverse `(U')†`), the algebraic form of "`U'` is unitary".
--
--   As requested this stays **off the gravity line** and **off the Hankel-transform line** (the surrounding integral operators `𝓕_M` and the Hankel-Majorana material of Definitions 65–66 are not touched); only the Majorana/Dirac algebra is used.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaProp61.lean

import Mathlib

/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"Fourier-Majorana Transform", **Proposition 61** — the boost intertwiner `U'` is unitary

`book.tex` **Proposition 61** (line ~5712) states: given a unitary operator
`U : Pinorⱼ(ℝ³) → Pinorⱼ(𝕏)` with `U ∘ H² = E² ∘ U`, where `iH = γ⁰ (∂⃗·γ⃗) + iγ⁰ m`
is the Majorana/Dirac Hamiltonian (`H` self-adjoint) and `E(X) ≥ m ≥ 0`, the operator

  `U' ≡ (E + U H γ⁰ U†) / (√(E+m) √(2E))`

is unitary.

The book's proof is the algebraic identity `(U')† U' = 1` (and `U' (U')† = 1`), which
rests on three facts coming from the Majorana setup:

* the Clifford **anticommutation** `H γ⁰ + γ⁰ H = 2m` (from `iH = γ⁰(∂⃗·γ⃗) + iγ⁰ m`
  and `(γ⁰)² = 1`, `{γʲ, γ⁰} = 0`),
* the intertwining relation, i.e. `E² = U H² U†`,
* `E = √(E²)` (hence also the normaliser `√(2E(E+m))`) **commutes** with
  `A := U H γ⁰ U†`.

We formalize exactly this algebraic core in a general `ℝ`-star-algebra `𝒜`
(playing the role of the bounded operators on the pinor space): `U` unitary, `g = γ⁰`
a self-adjoint involution, `H` self-adjoint with the anticommutator
`H*g + g*H = (2m)•1`, `E` self-adjoint with `E*E = U*H²*U†`, `A := U*H*g*U†` commuting
with `E`, and a self-adjoint invertible normaliser `N` (`= √(2E(E+m))`) with
`N*N = 2•E² + (2m)•E` commuting with `E` and `A`.

We prove:

* `gsq_Hsq_comm` — `g*(H*H) = (H*H)*g` follows *purely* from the anticommutator
* `prop61_star_mul_self` — `(U')† U' = 1`
* `prop61_mul_star_self` — `U' (U')† = 1`
* `prop61_isUnit` — `U'` is a unit (two-sided inverse `(U')†`), the algebraic form of
  "`U'` is unitary".

As requested this stays **off the gravity line** and **off the Hankel-transform line**
(the surrounding integral operators `𝓕_M` and the Hankel-Majorana material of
Definitions 65–66 are not touched); only the Majorana/Dirac algebra is used.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ChapterMajoranaProp61

variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℝ 𝒜] [StarModule ℝ 𝒜]



/-- The `γ⁰`-dressed conjugated operator `A = U H γ⁰ U†` of Proposition 61. -/
def Aop (U H g : 𝒜) : 𝒜 := U * H * g * star U

/-- The boost intertwiner `U' = N⁻¹ (E + A)` of Proposition 61, with `N⁻¹`
represented by a given two-sided inverse `Ni` of the normaliser `N = √(2E(E+m))`. -/
def Uprime (U H g E Ni : 𝒜) : 𝒜 := Ni * (E + Aop U H g)

section
variable (U H g E N Ni : 𝒜) (m : ℝ)
  (hU₁ : star U * U = 1) (hU₂ : U * star U = 1)
  (hg_sa : star g = g) (hg2 : g * g = 1)
  (hH_sa : star H = H)
  (hanti : H * g + g * H = (2 * m) • (1 : 𝒜))
  (hE_sa : star E = E)
  (hE2 : E * E = U * (H * H) * star U)
  (hEA : E * Aop U H g = Aop U H g * E)
  (hN_sa : star N = N)
  (hN2 : N * N = (2 : ℝ) • (E * E) + (2 * m) • E)
  (hNi₁ : N * Ni = 1) (hNi₂ : Ni * N = 1)
  (hNE : N * E = E * N)
  (hNA : N * Aop U H g = Aop U H g * N)

include hU₁ hU₂ hg_sa hg2 hH_sa hanti hE_sa hE2 hEA hN_sa hN2 hNi₁ hNi₂ hNE hNA







end

end BookProof.ChapterMajoranaProp61


