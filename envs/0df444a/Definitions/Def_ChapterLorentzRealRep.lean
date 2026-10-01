-- Prove2me | Definitions.Def_ChapterLorentzRealRep
-- name    : ChapterLorentzRealRep
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T08:46:16.643149+00:00
-- url     : https://prove2.me/theorems/89765f07-2721-478d-bf65-05537f0dfcc7
-- title:
--   Chapter LorentzRealRep
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLorentzRealRep.lean`): generated def bundle for ChapterLorentzRealRep. See BookProof/ChapterLorentzRealRep.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLorentzRealRep.lean

import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"On the Lorentz, SL(2,C) and Pin(3,1) groups", **Lemma 52** — concrete real
irreducible representations of `SL(2,C)`

`book.tex` (Lemma 52, line ~5560) classifies the finite-dimensional real
irreducible representations of `SL(2,C)` and gives three explicit examples in the
`4×4` Majorana matrix model, on which the spin group acts by conjugation
`M(S)(A) = S A S†`:

* the **`(1/2,1/2)` vector representation** — the real span of
  `{1, γ⁰γ¹, γ⁰γ², γ⁰γ³}` (a `1 + 3` vector, dimension `4`);
* the **`(1,0)` representation** — the real span of
  `{iγ¹, iγ², iγ³, γ¹γ⁵, γ²γ⁵, γ³γ⁵}` (dimension `6`);
* the **pseudo-`(1/2,1/2)` representation** — the real span of
  `{iγ⁵, iγ⁵γ¹γ⁰, iγ⁵γ²γ⁰, iγ⁵γ³γ⁰}` (dimension `4`).

Here we discharge the concrete, self-contained core over the discrete `Pin(3,1)`
subgroup `Ω = {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}` (the quaternion group `Q₈` of
`BookProof.ChapterPinOmega`, whose image under the covering map `Λ` is the
Klein-four discrete Lorentz group `Δ`).  For each of the three example spaces we
prove:

* **conjugation invariance** — conjugation by every `S ∈ Ω` maps each basis matrix
  to `±` a basis matrix (a *signed permutation* of the basis), decidably over `ℤ`;
* **dimension** — the basis matrices are linearly independent over `ℝ` (their
  Frobenius Gram matrix is `4·I`), so the representation spaces have dimensions
  `4`, `6`, `4`;
* **`Submodule` invariance** — the real span is carried into itself by the
  conjugation map `A ↦ S A S⁻¹`, for every `S ∈ Ω`.

All the finite/entrywise facts are closed over `ℤ` by `decide` and transported to
`ℝ` through `Int.castRingHom ℝ`.  As requested this stays **off the gravity line**
and **off the Hankel-transform line** (only the concrete Majorana matrices of
`ChapterA3` and the discrete group `Ω` of `ChapterPinOmega` are used).

Everything is `sorry`-free and `axiom`-free.
-/

open Matrix

namespace BookProof.ChapterLorentzRealRep

open BookProof.ChapterA3 BookProof.ChapterPinOmega

/-! ## The inverse inside `Ω` (integer model)

For `S ∈ Ω` one has `S² = ±1`, so the two-sided inverse is `S` itself when
`S² = 1` and `-S` otherwise; either way it stays inside `Ω`. -/

/-- Inverse of an element of `Ω` inside the integer matrix ring. -/
def cinv (S : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  if S * S = 1 then S else -S





/-! ## The three example bases (integer model) -/

/-- Basis of the `(1/2,1/2)` vector representation: `1, γ⁰γ¹, γ⁰γ², γ⁰γ³`.
(Recall `γ^μ = -i(iγ^μ)`, so `γ⁰γ^k = -(iγ⁰)(iγ^k)` is integral.) -/
def bHalf : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => 1
  | ⟨k + 1, h⟩ => -(mgammaZ 0 * mgammaZ ⟨k + 1, h⟩)

/-- Basis of the `(1,0)` representation: `iγ¹, iγ², iγ³, γ¹γ⁵, γ²γ⁵, γ³γ⁵`. -/
def b10 : Fin 6 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => mgammaZ 1
  | 1 => mgammaZ 2
  | 2 => mgammaZ 3
  | 3 => -(mgammaZ 1 * mgamma5Z)
  | 4 => -(mgammaZ 2 * mgamma5Z)
  | 5 => -(mgammaZ 3 * mgamma5Z)

/-- Basis of the pseudo-`(1/2,1/2)` representation: `iγ⁵, iγ⁵γ¹γ⁰, iγ⁵γ²γ⁰, iγ⁵γ³γ⁰`. -/
def bPs : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ
  | 0 => mgamma5Z
  | ⟨k + 1, h⟩ => mgamma5Z * (-(mgammaZ ⟨k + 1, h⟩ * mgammaZ 0))

/-- Signed basis (`{±bᵢ}`) of the `(1/2,1/2)` representation. -/
def SBHalf : Finset (Matrix (Fin 4) (Fin 4) ℤ) :=
  (Finset.univ.image bHalf) ∪ (Finset.univ.image fun i => -bHalf i)

/-- Signed basis of the `(1,0)` representation. -/
def SB10 : Finset (Matrix (Fin 4) (Fin 4) ℤ) :=
  (Finset.univ.image b10) ∪ (Finset.univ.image fun i => -b10 i)

/-- Signed basis of the pseudo-`(1/2,1/2)` representation. -/
def SBPs : Finset (Matrix (Fin 4) (Fin 4) ℤ) :=
  (Finset.univ.image bPs) ∪ (Finset.univ.image fun i => -bPs i)

/-! ## Conjugation invariance (signed-permutation form), over `ℤ`

For every `S ∈ Ω` and every basis matrix `A`, the conjugate `S A S⁻¹` is again
`±` a basis matrix.  This is the representation-theoretic heart of Lemma 52 for
the discrete group `Ω`. -/







/-! ## Cardinalities (the number of basis matrices) -/





/-! ## Frobenius Gram matrices, over `ℤ` (all equal to `4·I`) -/







/-! ## Real model: cast the bases into `ℝ` -/

/-- Cast an integer matrix to a real matrix. -/
noncomputable def castR : Matrix (Fin 4) (Fin 4) ℤ → Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix

/-- `(1/2,1/2)` basis over `ℝ`. -/
noncomputable def bHalfR (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := castR (bHalf i)

/-- `(1,0)` basis over `ℝ`. -/
noncomputable def b10R (i : Fin 6) : Matrix (Fin 4) (Fin 4) ℝ := castR (b10 i)

/-- pseudo-`(1/2,1/2)` basis over `ℝ`. -/
noncomputable def bPsR (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := castR (bPs i)







/-! ## Real Frobenius Gram matrices (cast of the integer ones) -/







/-! ## Linear independence from Frobenius orthogonality -/

/-
**Orthogonality ⇒ linear independence.**  A finite family of real `4×4`
matrices whose Frobenius Gram matrix is `4·I` (in particular, an orthogonal
family of nonzero matrices) is linearly independent.
-/








/-! ## The three representation spaces (`ℝ`-submodules) -/

/-- The `(1/2,1/2)` vector representation space. -/
noncomputable def WHalf : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  Submodule.span ℝ (Set.range bHalfR)

/-- The `(1,0)` representation space. -/
noncomputable def W10 : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) := Submodule.span ℝ (Set.range b10R)

/-- The pseudo-`(1/2,1/2)` representation space. -/
noncomputable def WPs : Submodule ℝ (Matrix (Fin 4) (Fin 4) ℝ) := Submodule.span ℝ (Set.range bPsR)

/-- The conjugation linear map `A ↦ S A T` on real matrices. -/
noncomputable def conjL (S T : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  (LinearMap.mulLeft ℝ S).comp (LinearMap.mulRight ℝ T)



/-! ### Every element of the signed bases casts into the corresponding span -/







/-! ### `Submodule` invariance under conjugation by `Ω` -/

/-
**`(1/2,1/2)` `Submodule` invariance.**  For `S ∈ Ω`, conjugation by `S`
maps the vector representation space into itself.
-/


/-
**`(1,0)` `Submodule` invariance.**
-/


/-
**pseudo-`(1/2,1/2)` `Submodule` invariance.**
-/




end BookProof.ChapterLorentzRealRep


