-- Prove2me | Definitions.Def_BirkhoffGlobalSection_TangentialHessian
-- name    : BirkhoffGlobalSection_TangentialHessian
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-09-26T17:39:26.796637+00:00
-- url     : https://prove2.me/theorems/04839b5b-f27a-4eee-9a0a-eee28612bcbd
-- title:
--   Explicit gradient, Hessian and tangential Hessian of the Levi-Civita Hamiltonian
-- statement:
--   Throughout, $\mathrm{Phase}=\mathbb R^4$ with coordinates $s=(z_1,z_2,w_1,w_2)$ of the Levi-Civita regularization $q+\mu=2z^2$, $p=w/\bar z$ of the planar circular restricted three-body problem at the primary of mass $1-\mu$ located at $(-\mu,0)$. The regularized Hamiltonian at the Jacobi level $H=-c$ is $K_{\mu,c}=P-\mu Z/r$, where $Z=z_1^2+z_2^2$, $r=\lvert 2z^2-1\rvert=\sqrt{D}$ with $D=(2(z_1^2-z_2^2)-1)^2+(4z_1z_2)^2$, and $P$ is the polynomial part of eq. (2.2). The set $U=\{D>0\}$ excludes the (unregularized) second collision.
--
--   This module defines the explicit objects needed to state and check the tangential-Hessian condition of Proposition 4.4.
--
--   1. The polynomial pieces: $P$ (`pP`), its gradient and Hessian (`dP`, `hP`), and those of $Z$ and $D$ (`dZ`, `hZ`, `dD`, `hD`).
--   2. The explicit gradient and Hessian of $K_{\mu,c}$, with $r$ as a free argument:
--   $$
--   \nabla K_i=\partial_iP-\mu\Big(\frac{\partial_iZ}{r}-\frac{Z\,\partial_iD}{2r^3}\Big),\qquad
--   \nabla^2K_{ij}=\partial_{ij}P-\mu\Big(\frac{\partial_{ij}Z}{r}-\frac{\partial_iZ\,\partial_jD+\partial_jZ\,\partial_iD}{2r^3}-\frac{Z\,\partial_{ij}D}{2r^3}+\frac{3Z\,\partial_iD\,\partial_jD}{4r^5}\Big),
--   $$
--   as `kGradR`/`kHessR`. The versions `kGrad`/`kHess` substitute $r=\sqrt D$.
--   3. The quaternionic matrices $I,J,K$ of Section 2.3 (`qI`, `qJ`, `qK`) and the frame $(I\nabla K,J\nabla K,K\nabla K)$ (`frame`).
--   4. The $3\times3$ tangential Hessian $\mathrm{THess}_{ij}=v_i^{\mathsf T}\nabla^2K\,v_j$ in that frame, symmetrized (`tHessR`, `tHess`), and positive definiteness of a $3\times3$ quadratic form (`QuadPos`).
--   5. The reduced quantities of the radial-derivative estimate: $u=z_1^2-z_2^2$ (`uCoord`) and the denominator-free polynomials $E\,r^3$, $R^2 r$, $F\,r^6$ (`radEr3`, `radrR2`, `radFr6`).
--
--   These definitions allow the positive-tangential-Hessian clause of Proposition 4.4 to be reduced to explicit inequalities between polynomials and powers of $r$.
--
--   **Formalization Note.** All objects are total functions on $\mathbb R^4$. Division by $r=0$ follows Lean's convention $x/0=0$, and every statement about derivatives is restricted to $U$.
-- source:
--   Joung–van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159v3, Section 2.3 (frame I∇K, J∇K, K∇K and THess), eq. (2.2), eq. (4.1), Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Explicit derivatives and the tangential Hessian of the Levi-Civita Hamiltonian

Definitions for the tangential-Hessian condition of Joung--van Koert, Proposition 4.4
(arXiv:2407.19159v3): on `U = {0 < secondCollisionDistanceSq}` with `r = √(secondCollisionDistanceSq s)`,
`K = P - μ Z / r`; explicit gradient `kGrad` and Hessian `kHess` (built from the polynomial gradients/Hessians
`dP, hP, dZ, hZ, dD, hD` of `P`, `Z = zNormSq` and `D = secondCollisionDistanceSq`); the quaternionic frame
`I∇K, J∇K, K∇K` of Section 2.3; the `3 × 3` tangential Hessian `tHess` in that frame; positive definiteness
of a quadratic form (`QuadPos`); and the reduced quantities of the radial-derivative estimate.
-/

namespace BirkhoffGlobalSection.TangentialHessian

open BirkhoffGlobalSection

noncomputable section

/-- `I` from Joung--van Koert, Section 2.3, in the order `(z₁,z₂,w₁,w₂)`. -/
def qI : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

/-- `J` from Joung--van Koert, Section 2.3. -/
def qJ : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- `K` from Joung--van Koert, Section 2.3. -/
def qK : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, -1; 0, 0, 1, 0; 0, -1, 0, 0; 1, 0, 0, 0]

/-- The gradient of `F` at `s` in the coordinates `(z₁,z₂,w₁,w₂)`. -/
def grad (F : Phase → ℝ) (s : Phase) : Phase :=
  fun i => partialDerivative F s i

/-- The paper's frame `v₁ = I∇K`, `v₂ = J∇K`, `v₃ = K∇K`. -/
def frame (g : Phase) : Fin 3 → Phase :=
  ![qI.mulVec g, qJ.mulVec g, qK.mulVec g]

/-- Away from the (unregularized) second collision. -/
def U : Set Phase := {s | 0 < secondCollisionDistanceSq s}

/-- `r = |2z² - 1|`. -/
def rD (s : Phase) : ℝ := Real.sqrt (secondCollisionDistanceSq s)

/-- The polynomial part `P` of `K = P - μ Z / r`. -/
def pP (μ c : ℝ) (s : Phase) : ℝ :=
  wNormSq s / 2 + c * zNormSq s - (1 - μ) / 2
    + 2 * zNormSq s * (s 0 * s 3 - s 1 * s 2) - μ * (s 0 * s 3 + s 1 * s 2)

/-- Gradient of `P`. -/
def dP (μ c : ℝ) (s : Phase) : Fin 4 → ℝ :=
  ![2 * c * s 0 - μ * s 3 - 4 * s 2 * s 0 * s 1 + 6 * s 3 * s 0 ^ 2 + 2 * s 3 * s 1 ^ 2,
    2 * c * s 1 - μ * s 2 - 2 * s 2 * s 0 ^ 2 - 6 * s 2 * s 1 ^ 2 + 4 * s 3 * s 0 * s 1,
    -μ * s 1 + s 2 - 2 * s 0 ^ 2 * s 1 - 2 * s 1 ^ 3,
    -μ * s 0 + s 3 + 2 * s 0 ^ 3 + 2 * s 0 * s 1 ^ 2]

/-- Hessian of `P`. -/
def hP (μ c : ℝ) (s : Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 * c - 4 * s 2 * s 1 + 12 * s 3 * s 0, -4 * s 2 * s 0 + 4 * s 3 * s 1,
      -4 * s 0 * s 1, -μ + 6 * s 0 ^ 2 + 2 * s 1 ^ 2;
    -4 * s 2 * s 0 + 4 * s 3 * s 1, 2 * c - 12 * s 2 * s 1 + 4 * s 3 * s 0,
      -μ - 2 * s 0 ^ 2 - 6 * s 1 ^ 2, 4 * s 0 * s 1;
    -4 * s 0 * s 1, -μ - 2 * s 0 ^ 2 - 6 * s 1 ^ 2, 1, 0;
    -μ + 6 * s 0 ^ 2 + 2 * s 1 ^ 2, 4 * s 0 * s 1, 0, 1]

/-- Gradient of `Z = zNormSq`. -/
def dZ (s : Phase) : Fin 4 → ℝ := ![2 * s 0, 2 * s 1, 0, 0]

/-- Hessian of `Z`. -/
def hZ : Matrix (Fin 4) (Fin 4) ℝ := !![2, 0, 0, 0; 0, 2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- Gradient of `D = secondCollisionDistanceSq`. -/
def dD (s : Phase) : Fin 4 → ℝ :=
  ![16 * s 0 ^ 3 + 16 * s 0 * s 1 ^ 2 - 8 * s 0,
    16 * s 0 ^ 2 * s 1 + 16 * s 1 ^ 3 + 8 * s 1, 0, 0]

/-- Hessian of `D`. -/
def hD (s : Phase) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![48 * s 0 ^ 2 + 16 * s 1 ^ 2 - 8, 32 * s 0 * s 1, 0, 0;
    32 * s 0 * s 1, 16 * s 0 ^ 2 + 48 * s 1 ^ 2 + 8, 0, 0;
    0, 0, 0, 0;
    0, 0, 0, 0]

/-- The gradient of `K`, with `r` a free variable (`r = rD s` on `U`). -/
def kGradR (μ c r : ℝ) (s : Phase) : Fin 4 → ℝ := fun i =>
  dP μ c s i - μ * (dZ s i / r - zNormSq s * dD s i / (2 * r ^ 3))

/-- The Hessian of `K`, with `r` a free variable (`r = rD s` on `U`). -/
def kHessR (μ c r : ℝ) (s : Phase) : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  hP μ c s i j - μ * (hZ i j / r - (dZ s i * dD s j + dZ s j * dD s i) / (2 * r ^ 3)
    - zNormSq s * hD s i j / (2 * r ^ 3) + 3 * zNormSq s * dD s i * dD s j / (4 * r ^ 5))

/-- The gradient of the Levi-Civita Hamiltonian on `U` (explicit form). -/
def kGrad (μ c : ℝ) (s : Phase) : Fin 4 → ℝ := kGradR μ c (rD s) s

/-- The Hessian of the Levi-Civita Hamiltonian on `U` (explicit form). -/
def kHess (μ c : ℝ) (s : Phase) : Matrix (Fin 4) (Fin 4) ℝ := kHessR μ c (rD s) s

/-- Positive definiteness of the quadratic form of a `3 × 3` matrix. -/
def QuadPos (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ a : Fin 3 → ℝ, a ≠ 0 → 0 < ∑ i, ∑ j, a i * a j * A i j

/-- The unsymmetrized tangential Hessian `vᵢᵀ H vⱼ` for gradient `g` and Hessian `H`. -/
def frameHess (g : Phase) (H : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ k, ∑ l, frame g i k * frame g j l * H k l

/-- The symmetrized tangential Hessian, with `r` a free variable. -/
def tHessR (μ c r : ℝ) (s : Phase) : Matrix (Fin 3) (Fin 3) ℝ :=
  let M := frameHess (kGradR μ c r s) (kHessR μ c r s)
  fun i j => (M i j + M j i) / 2

/-- The `3 × 3` tangential Hessian in the frame `I∇K, J∇K, K∇K` (symmetrized). -/
def tHess (μ c : ℝ) (s : Phase) : Matrix (Fin 3) (Fin 3) ℝ := tHessR μ c (rD s) s

/-- `u = z₁² - z₂²`. -/
def uCoord (s : Phase) : ℝ := s 0 ^ 2 - s 1 ^ 2

/-- `E · r³` (denominator-free). -/
def radEr3 (μ Z u r : ℝ) : ℝ :=
  r ^ 3 * ((1 - μ) - 8 * Z ^ 3 + 4 * μ * Z * u) + 4 * μ * Z * (2 * Z ^ 2 - u)

/-- `R² · r` (denominator-free). -/
def radrR2 (μ c Z u r : ℝ) : ℝ :=
  r * ((1 - μ) - 2 * c * Z + (4 * Z ^ 2 + μ ^ 2) * Z - 4 * μ * Z * u) + 2 * μ * Z

/-- `F · r⁶ = (E r³)² - 16 Z³ r⁵ (R² r)` with `F = E² - 16 Z³ R²` (denominator-free). -/
def radFr6 (μ c Z u r : ℝ) : ℝ :=
  radEr3 μ Z u r ^ 2 - 16 * Z ^ 3 * r ^ 5 * radrR2 μ c Z u r

end

end BirkhoffGlobalSection.TangentialHessian


