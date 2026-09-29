-- Prove2me | Definitions.Def_ChapterSqSumFarisLavine
-- name    : ChapterSqSumFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-12T08:23:21.154895+00:00
-- url     : https://prove2.me/theorems/926c55ec-8481-415a-aea8-ccd6b1b977aa
-- title:
--   This module proves, on the Gauss–polynomial core of `L²(ℝᴰ)`, the two inequalities that Theorem 1 of Faris–Lavine asks o ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.SqSumFarisLavine`, source chapter `BookProof/ChapterSqSumFarisLavine.lean`).
--
--   This module proves, on the Gauss–polynomial core of `L²(ℝᴰ)`, the two inequalities that Theorem 1 of Faris–Lavine asks of a Hamiltonian and its comparison operator, for the **kinetic-plus-squares Hamiltonian**
--
--   `H = ½ Σ_j κ_j π_j² + ½ Σ_r L_r²`, `L_r = Σ_i v_{ri} x_i`,
--
--   of `BookProof.QgOuterFock.sqSumOp`, against the harmonic comparison operator `N = −Δ + ‖x‖²/4` (`harmCore`). The signature `κ` is an arbitrary *real* vector — no sign, no ellipticity — and the family of linear forms `L_r` is arbitrary and finite.
--
--   What matters for the Fock lift is the *shape of the constants*: both are expressed through
--
--   * `km`, a bound on `|κ_j|`, and * Schur-type `ℓ¹` bounds on the coefficient matrix `v` of the linear forms
--
--   and **not** through the dimension `D`. This is exactly what makes the same two constants serve every particle-number sector of the outer Fock space simultaneously, which is the hypothesis the `ℓ²`-direct-sum Faris–Lavine theorem of `BookProof.ChapterQgOuterFockFarisLavine` needs.
--
--   * `schur_bound` — the Schur test for a real matrix with bounded row and column `ℓ¹` norms; * `linFun`, `potFun`, `potPoly`, `gradPoly`, `gradFun`, `kinPart` — the data of the Hamiltonian, and `sqSumPoly_apply`, its splitting into kinetic and potential parts; * `potFun_le_of_schur`, `sum_gradFun_sq_le_of_schur` — the pointwise bounds `V(x) ≤ (ab/2)‖x‖²` and `Σ_k (∂_k V)(x)² ≤ (ab)²‖x‖²` from the Schur data of `v`; * `commPoly`, `commPoly_eq` — the commutator `[H, N]` computed in polynomial coordinates: it is again first order, with the gradient of the potential as its coefficient; * `commForm_eq_im`, `abs_im_gaussInt_le` — the commutator form as a Gaussian integral; * **`commForm_sqSumOp_le`** — the Faris–Lavine commutator bound `|⟪u, i[H,N]u⟫| ≤ (km/2 + 2M)·⟪u, Nu⟫`, with `M` a bound on the gradient of the potential; * **`norm_sqSumOp_le`** — the relative bound `‖Hu‖ ≤ (3km/2 + 8B)·‖(N+1)u‖`, with `B` a bound on the potential.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSqSumFarisLavine.lean

import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Mathlib
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterGaussCoreQuadBounds
open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteCore
open BookProof.QgHermiteFriedrichs
open BookProof.YangMillsHermite
open BookProof.GaussCoreQuadBounds


/-!
# The two Faris–Lavine inequalities for `½ Σ_j κ_j π_j² + ½ Σ_r L_r²`

This module proves, on the Gauss–polynomial core of `L²(ℝᴰ)`, the two inequalities that
Theorem 1 of Faris–Lavine asks of a Hamiltonian and its comparison operator, for the
**kinetic-plus-squares Hamiltonian**

`H = ½ Σ_j κ_j π_j² + ½ Σ_r L_r²`,  `L_r = Σ_i v_{ri} x_i`,

of `BookProof.QgOuterFock.sqSumOp`, against the harmonic comparison operator
`N = −Δ + ‖x‖²/4` (`harmCore`).  The signature `κ` is an arbitrary *real* vector — no sign,
no ellipticity — and the family of linear forms `L_r` is arbitrary and finite.

What matters for the Fock lift is the *shape of the constants*: both are expressed through

* `km`, a bound on `|κ_j|`, and
* Schur-type `ℓ¹` bounds on the coefficient matrix `v` of the linear forms

and **not** through the dimension `D`.  This is exactly what makes the same two constants
serve every particle-number sector of the outer Fock space simultaneously, which is the
hypothesis the `ℓ²`-direct-sum Faris–Lavine theorem of
`BookProof.ChapterQgOuterFockFarisLavine` needs.

## What is proved

* `schur_bound` — the Schur test for a real matrix with bounded row and column `ℓ¹` norms;
* `linFun`, `potFun`, `potPoly`, `gradPoly`, `gradFun`, `kinPart` — the data of the
  Hamiltonian, and `sqSumPoly_apply`, its splitting into kinetic and potential parts;
* `potFun_le_of_schur`, `sum_gradFun_sq_le_of_schur` — the pointwise bounds
  `V(x) ≤ (ab/2)‖x‖²` and `Σ_k (∂_k V)(x)² ≤ (ab)²‖x‖²` from the Schur data of `v`;
* `commPoly`, `commPoly_eq` — the commutator `[H, N]` computed in polynomial coordinates:
  it is again first order, with the gradient of the potential as its coefficient;
* `commForm_eq_im`, `abs_im_gaussInt_le` — the commutator form as a Gaussian integral;
* **`commForm_sqSumOp_le`** — the Faris–Lavine commutator bound
  `|⟪u, i[H,N]u⟫| ≤ (km/2 + 2M)·⟪u, Nu⟫`, with `M` a bound on the gradient of the
  potential;
* **`norm_sqSumOp_le`** — the relative bound `‖Hu‖ ≤ (3km/2 + 8B)·‖(N+1)u‖`, with `B` a
  bound on the potential.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SqSumFarisLavine


noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

/-! ## 1. The Schur test -/



/-! ## 2. The data of a kinetic-plus-squares Hamiltonian -/

/-- The value of the linear form `L_v` at a point. -/
def linFun (v : Fin D → ℝ) (x : Vd D) : ℝ := ∑ i : Fin D, v i * x i

/-- The potential `V = ½ Σ_r L_r²`, as a real function. -/
def potFun (v : R → Fin D → ℝ) (x : Vd D) : ℝ := (1 / 2) * ∑ r : R, (linFun (v r) x) ^ 2


def linForm (v : Fin D → ℝ) : MvPolynomial (Fin D) ℂ :=
  ∑ i : Fin D, ((v i : ℝ) : ℂ) • X i

def sqSumPoly {R : Type*} [Fintype R] (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    MvPolynomial (Fin D) ℂ →ₗ[ℂ] MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    ((∑ j : Fin D, ((kappa j : ℝ) : ℂ) •
        (YangMillsHermite.momOp j).comp (YangMillsHermite.momOp j))
      + ∑ r : R, (YangMillsHermite.mulOp (linForm (v r))).comp
          (YangMillsHermite.mulOp (linForm (v r))))

/-- The potential `V = ½ Σ_r L_r²`, as a polynomial. -/
def potPoly (v : R → Fin D → ℝ) : MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ r : R, linForm (v r) * linForm (v r)

/-- The gradient `∂_k V = Σ_r v_{rk} L_r`, as a polynomial. -/
def gradPoly (v : R → Fin D → ℝ) (k : Fin D) : MvPolynomial (Fin D) ℂ :=
  ∑ r : R, ((v r k : ℝ) : ℂ) • linForm (v r)

/-- The gradient `∂_k V`, as a real function. -/
def gradFun (v : R → Fin D → ℝ) (k : Fin D) (x : Vd D) : ℝ :=
  ∑ r : R, v r k * linFun (v r) x

/-- The kinetic part `−½ Σ_j κ_j ∂_j²`, on polynomial coordinates. -/
def kinPart (kappa : Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) : MvPolynomial (Fin D) ℂ :=
  ∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ) • coreD j (coreD j p)



/-! ### Evaluations -/











/-! ## 3. The Schur bounds on the potential data -/





/-! ## 4. The first Faris–Lavine inequality: the relative bound -/







/-! ## 5. The second Faris–Lavine inequality: the commutator form -/

/-- The formal commutator `[H, N]`, on polynomial coordinates. -/
def commPoly (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    MvPolynomial (Fin D) ℂ :=
  sqSumPoly kappa v (harmP p) - harmP (sqSumPoly kappa v p)

/-- The commutator constant of the identity below. -/
def commConst (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) : ℝ :=
  -(1 / 4) * ∑ j : Fin D, kappa j + ∑ r : R, ∑ k : Fin D, (v r k) ^ 2

/-! ### Derivatives of the potentials -/

















/-! ### The two commutators -/







/-! ### The commutator form on the core -/

















end

end BookProof.SqSumFarisLavine


