-- Prove2me | Definitions.Def_TensorIso233_BQP_Tensor
-- name    : TensorIso233_BQP_Tensor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:38.8477+00:00
-- url     : https://prove2.me/theorems/61597d61-6ab3-46c2-be5b-0b1f04d19c97
-- title:
--   Integral $2\times3\times3$ tensors, the action (2.1), isomorphism, strict equivalence and the determinant form
-- statement:
--   An integral $2\times3\times3$ tensor $T\in\mathbb Z^2\otimes\mathbb Z^3\otimes\mathbb Z^3$ is recorded by its two slices $T=(A,B)$, a pair of $3\times3$ integer matrices. For $h=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}\in GL_2(\mathbb Z)$ and $P,Q\in GL_3(\mathbb Z)$ the action (2.1) is
--
--   $$
--   (h,P,Q)\cdot(A,B)=\bigl(P(\alpha A-\beta B)Q^{-1},\;P(-\gamma A+\delta B)Q^{-1}\bigr).
--   $$
--
--   Two tensors are **isomorphic**, $T\cong T'$, when $T'=(h,P,Q)\cdot T$ for some $(h,P,Q)$. They are **strictly equivalent**, $T\sim_{\mathrm{str}}T'$, when $T'=(I_2,P,Q)\cdot T$ with $\det P=\det Q$.
--
--   The pencil is $M_T(x,y)=xA-yB$ and the **determinant form** is the integral binary cubic $f_T(x,y)=\det(xA-yB)$; $T$ is regular when $f_T\neq0$. The slices are **dependent** when $aA+bB=0$ for some rational $(a,b)\neq(0,0)$; the zero tensor has dependent slices.
--
--   A binary cubic $f=f_0x^3+f_1x^2y+f_2xy^2+f_3y^3$ is recorded by $(f_0,f_1,f_2,f_3)$. For $h$ as above, (2.2) sets $f^h(x,y)=f(\alpha x+\gamma y,\beta x+\delta y)$. A **pure cube** is $C\ell^3$ with $C\in\mathbb Z\setminus\{0\}$ and $\ell=ux+vy$, $\gcd(u,v)=1$. The matrix $h_{t,\delta}=\begin{pmatrix}1&-t\\0&\delta\end{pmatrix}$ is (5.1). Over $\mathbb Q$, $D=A^{-1}B$ and $E=BA^{-1}$ are the operators (4.4).
--
--   These are the basic objects of every statement in the mission.
--
--   **Formalization Note** $Q^{-1}$ is the inverse in the group $GL_3(\mathbb Z)$, an integer matrix. Polynomials are `MvPolynomial (Fin 2) ℤ` with $x$ = `X 0`, $y$ = `X 1`. $D$ and $E$ use the Mathlib inverse, which is meaningful exactly when $\det A\neq0$; every statement that uses them assumes this.
-- source:
--   Thomas Huffstutler, Integral 2 × 3 × 3 Tensor Isomorphism is in BQP, STOC 2027 submission #319 (October 2026), §2.1, pp. 12–13, (2.1)–(2.2); §4.1, p. 15, (4.4); §5.1, p. 18, pure cubes and (5.1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/319.pdf

import Mathlib

/-!
# Integral 2 × 3 × 3 tensors, the action (2.1), isomorphism and the determinant form

Thomas Huffstutler, *Integral 2 × 3 × 3 Tensor Isomorphism is in BQP*, STOC 2027 submission #319
(October 2026), §2.1 (pp. 12–13), §4.1 (p. 14), §5 (pp. 18–19).

A tensor `T ∈ ℤ² ⊗ ℤ³ ⊗ ℤ³` is recorded by its two slices `T = (A, B)`, two `3 × 3` integer
matrices. All statements of the mission are about these objects.
-/

namespace TensorIso233.BQP

open MvPolynomial

/-- A `3 × 3` integer matrix. -/
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℤ

/-- §2.1, p. 12: an integral `2 × 3 × 3` tensor `T = (A, B)`, given by its two slices. -/
abbrev Tensor := Mat3 × Mat3

/-- `GL₂(ℤ)`, the integer `2 × 2` matrices with integer inverse. -/
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) ℤ

/-- `GL₃(ℤ)`, the integer `3 × 3` matrices with integer inverse. -/
abbrev GL3 := Matrix.GeneralLinearGroup (Fin 3) ℤ

/-- Equation (2.1), p. 12: for `h = (α β; γ δ) ∈ GL₂(ℤ)` and `P, Q ∈ GL₃(ℤ)`,
`(h, P, Q) · (A, B) = (P(αA − βB)Q⁻¹, P(−γA + δB)Q⁻¹)`. Here `Q⁻¹` is the group inverse in
`GL₃(ℤ)`, which is an integer matrix. -/
def act (h : GL2) (P Q : GL3) (T : Tensor) : Tensor :=
  ((P : Mat3) * (((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0) • T.1 - ((h : Matrix (Fin 2) (Fin 2) ℤ) 0 1) • T.2)
      * ((Q⁻¹ : GL3) : Mat3),
   (P : Mat3) * ((-(h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) • T.1 + ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1) • T.2)
      * ((Q⁻¹ : GL3) : Mat3))

/-- §1.1 and §2.1: `T ≅ T'`, i.e. `T'` lies in the `GL₂(ℤ) × GL₃(ℤ) × GL₃(ℤ)`-orbit of `T` under
the action (2.1). -/
def Iso (T T' : Tensor) : Prop :=
  ∃ (h : GL2) (P Q : GL3), act h P Q T = T'

/-- §2.1, p. 13: strict equivalence `T ∼str T'`: `T' = (I₂, P, Q) · T` for some `(P, Q) ∈ G₃`,
i.e. `P, Q ∈ GL₃(ℤ)` with `det P = det Q`. -/
def StrictEquiv (T T' : Tensor) : Prop :=
  ∃ P Q : GL3, (P : Mat3).det = (Q : Mat3).det ∧ act 1 P Q T = T'

/-- §2.1, p. 12: the pencil `M_T(x, y) = xA − yB` as a `3 × 3` matrix of integer polynomials in
the two variables `x = X 0`, `y = X 1`. -/
noncomputable def pencilPoly (T : Tensor) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 2) ℤ) :=
  Matrix.of fun i j => X 0 * C (T.1 i j) - X 1 * C (T.2 i j)

/-- §2.1, p. 12: the determinant form `f_T(x, y) = det(xA − yB)`, an integral binary cubic
(as a polynomial in `x = X 0`, `y = X 1`). `T` is *regular* when `f_T ≠ 0`. -/
noncomputable def detForm (T : Tensor) : MvPolynomial (Fin 2) ℤ :=
  (pencilPoly T).det

/-- The slices of `T` are linearly dependent over `ℚ`: `aA + bB = 0` for some rational
`(a, b) ≠ (0, 0)`. The zero tensor has dependent slices. -/
def SlicesDependent (T : Tensor) : Prop :=
  ∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
    a • T.1.map (Int.cast : ℤ → ℚ) + b • T.2.map (Int.cast : ℤ → ℚ) = 0

/-! ### Binary cubics and the first-factor action (2.2) -/

/-- An integral binary cubic `f = f₀x³ + f₁x²y + f₂xy² + f₃y³`, recorded by its coefficient
vector `(f₀, f₁, f₂, f₃)`. -/
abbrev BinCubic := Fin 4 → ℤ

/-- The polynomial `f₀x³ + f₁x²y + f₂xy² + f₃y³` of a coefficient vector. -/
noncomputable def cubicPoly (f : BinCubic) : MvPolynomial (Fin 2) ℤ :=
  ∑ i : Fin 4, C (f i) * X 0 ^ (3 - (i : ℕ)) * X 1 ^ (i : ℕ)

/-- Equation (2.2), p. 12: for `h = (α β; γ δ)`, the substitution
`p^h(x, y) = p(αx + γy, βx + δy)` of an integer polynomial in two variables. -/
noncomputable def polySubst (h : GL2) (p : MvPolynomial (Fin 2) ℤ) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.aeval
    (![C ((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0) * X 0 + C ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) * X 1,
       C ((h : Matrix (Fin 2) (Fin 2) ℤ) 0 1) * X 0 + C ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1) * X 1])
    p

/-- p. 18: a pure cube is a form `Cℓ³` with `C ∈ ℤ`, `C ≠ 0`, and `ℓ = ux + vy` a primitive
integral linear form (`gcd(u, v) = 1`). -/
def IsPureCube (p : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∃ c u v : ℤ, c ≠ 0 ∧ Int.gcd u v = 1 ∧ p = C c * (C u * X 0 + C v * X 1) ^ 3

/-- The pure cube `Cx³`. -/
noncomputable def cubeX (c : ℤ) : MvPolynomial (Fin 2) ℤ := C c * X 0 ^ 3

/-- (5.1), p. 18: the matrix `h_{t,δ} = (1 −t; 0 δ)`. -/
def shearMat (t δ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, -t; 0, δ]

/-! ### Rational slices and the operators (4.4) -/

/-- A slice as a rational matrix. -/
def toQ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℚ :=
  M.map (Int.cast : ℤ → ℚ)

/-- (4.4), p. 15: `D = A⁻¹B` over `ℚ` (meaningful when `det A ≠ 0`). -/
noncomputable def opD (T : Tensor) : Matrix (Fin 3) (Fin 3) ℚ := (toQ T.1)⁻¹ * toQ T.2

/-- (4.4), p. 15: `E = BA⁻¹` over `ℚ` (meaningful when `det A ≠ 0`). -/
noncomputable def opE (T : Tensor) : Matrix (Fin 3) (Fin 3) ℚ := toQ T.2 * (toQ T.1)⁻¹

end TensorIso233.BQP


