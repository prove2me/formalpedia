-- Prove2me | Definitions.Def_ChapterSE2
-- name    : ChapterSE2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:59:06.324987+00:00
-- url     : https://prove2.me/theorems/ef98e2da-d4de-492d-be8a-cce30850b394
-- title:
--   Chapter SE2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSE2.lean`): generated def bundle for ChapterSE2. See BookProof/ChapterSE2.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSE2.lean

import Definitions.Def_ChapterA3
import Mathlib


/-!
# Chapter "Real representations, CPT theorem and the relativistic position operator",
§"Real unitary representations of the Poincaré group", **Proposition 79** — the `SE(2)`
translation subgroup of the null little group

`book.tex` (§"Real unitary representations of the Poincaré group", Proposition 79,
massless case `i\cancel l = i(γ⁰+γ³)`) exhibits the little group `G_l = SE(2)` with the
explicit parametrization

  `SE(2) = { (1 + iγ⁵(γ¹a + γ²b)(γ⁰+γ³)) · e^{iγ⁰γ³γ⁵θ} : a,b,θ ∈ ℝ }`.

The **rotation** factor `e^{iγ⁰γ³γ⁵θ}` requires the matrix exponential and is left as
prose.  We formalize the **translation** factor, i.e. the abelian normal subgroup of
`SE(2)`:

  `N(a,b) ≡ 1 + iγ⁵(γ¹a + γ²b)(γ⁰+γ³)`.

Writing everything in terms of the concrete real Majorana matrices `M_μ = iγ^μ` of
`BookProof.ChapterA3` (so `γ^μ = -i M_μ`, `iγ⁵ = M₅`), the translation matrix is the
real `4×4` matrix

  `X(a,b) = -(M₅ (a M₁ + b M₂) (M₀+M₃))`,  `N(a,b) = 1 + X(a,b)`.

The headline `Nmat_mul` shows `N` is a **group homomorphism from `(ℝ², +)`**:
`N(a,b) · N(c,d) = N(a+c, b+d)`, hence the translations form an abelian group `≅ ℝ²`
(with unit `N(0,0) = 1` and inverse `N(-a,-b)`).  The whole computation reduces to the
nilpotency facts
`(γ⁰+γ³)² = 0` and `X(a,b) · X(c,d) = 0`, which in turn come from the four decidable
identities `se2_coef_*` over the integer Majorana model.

This stays off the gravity line and off the Hankel-transform line, per the roadmap.
Everything is `sorry`-free and `axiom`-free.
-/

open Matrix

namespace BookProof.ChapterSE2

open BookProof.ChapterA3

/-! ### Integer nilpotency identities (decidable) -/











/-! ### Real Majorana model -/

/-- Cast integer matrices to real ones. -/
noncomputable def castR : Matrix (Fin 4) (Fin 4) ℤ →+* Matrix (Fin 4) (Fin 4) ℝ :=
  (Int.castRingHom ℝ).mapMatrix

/-- The real Majorana matrix `M_μ = iγ^μ`. -/
noncomputable def M (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := castR (mgammaZ μ)

/-- The real fifth Majorana matrix `M₅ = iγ⁵`. -/
noncomputable def M5 : Matrix (Fin 4) (Fin 4) ℝ := castR mgamma5Z

/-- The light-cone projector direction `P = iγ⁰ + iγ³` (real). -/
noncomputable def Pr : Matrix (Fin 4) (Fin 4) ℝ := M 0 + M 3

/-- The `SE(2)` translation matrix `X(a,b) = iγ⁵(γ¹a + γ²b)(γ⁰+γ³)` (real). -/
noncomputable def Xmat (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  -(M5 * (a • M 1 + b • M 2) * Pr)

/-- The `SE(2)` translation group element `N(a,b) = 1 + X(a,b)`. -/
noncomputable def Nmat (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := 1 + Xmat a b

/-- `X` is additive in `(a,b)`: `X(a,b) + X(c,d) = X(a+c, b+d)`. -/
theorem Xmat_add (a b c d : ℝ) : Xmat a b + Xmat c d = Xmat (a + c) (b + d) := by
  unfold Xmat; ring;
  simp only [mul_add, mul_smul_comm, Pr, add_mul, add_smul] ; abel_nf;

/-- The translations are **nilpotent**: `X(a,b) · X(c,d) = 0`. -/
theorem Xmat_mul_Xmat (a b c d : ℝ) : Xmat a b * Xmat c d = 0 := by
  -- By expanding the product using the definitions of `Xmat`, `M`, `M5`, and `Pr`, we can apply the
  -- nilpotency conditions.
  have h_expand : (M5 * (a • M 1 + b • M 2) * Pr) * (M5 * (c • M 1 + d • M 2) * Pr) = 0 := by
    simp only [M5, M, Fin.isValue, mul_add, Algebra.mul_smul_comm, Pr, add_mul,
        Algebra.smul_mul_assoc, mul_assoc, smul_add, smul_smul];
    simp only [Fin.isValue, ← map_mul, ← mul_assoc];
    unfold castR; norm_num [ mgamma5Z, mgammaZ ] ;
    ext i j ;      fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, Fin.sum_univ_succ ]
        <;> ring!;
  unfold Xmat; aesop;

/-- `N(0,0) = 1`. -/
theorem Nmat_zero : Nmat 0 0 = 1 := by
  unfold Nmat Xmat; aesop;

/-- **Proposition 79 (`SE(2)` translations).** `N` is a homomorphism from `(ℝ², +)`:
`N(a,b) · N(c,d) = N(a+c, b+d)`. -/
theorem Nmat_mul (a b c d : ℝ) : Nmat a b * Nmat c d = Nmat (a + c) (b + d) := by
  convert congr_arg ( fun x : Matrix ( Fin 4 ) ( Fin 4 ) ℝ => 1 + x ) ( Xmat_add a b c d ) using 1
  · unfold Nmat; simp only [mul_add, mul_one, add_mul, one_mul, Xmat_mul_Xmat, add_zero] ;
    rw [ add_assoc ]
  · rfl



/-- **Capstone.** `N` assembles into a monoid homomorphism from `(ℝ², +)` (as
`Multiplicative (ℝ × ℝ)`) into the matrix monoid: this is the abelian translation
subgroup of `SE(2)`, isomorphic to `ℝ²`. -/
noncomputable def NmatHom : Multiplicative (ℝ × ℝ) →* Matrix (Fin 4) (Fin 4) ℝ where
  toFun p := Nmat (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2
  map_one' := Nmat_zero
  map_mul' x y := (Nmat_mul (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
    (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2).symm

end BookProof.ChapterSE2


