-- Prove2me | Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane
-- name    : ConjGrad_ErrorDecrease_Supplement_cdPlane
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:52:02.013807+00:00
-- url     : https://prove2.me/theorems/331fe4e4-367e-483a-b2d0-e814a9a3fcc6
-- title:
--   The plane $P_i$ (4:10) and the conjugate plane $\pi_i$ of Theorem 4:6
-- statement:
--   Let $p_0,p_1,\dots$ be direction vectors in $\mathbb R^n$ and $x_0\in\mathbb R^n$. The **plane** $P_i$ of (4:10) is the set of points
--
--   $$x=x_0+\alpha_0p_0+\cdots+\alpha_{i-1}p_{i-1},\qquad \alpha_0,\dots,\alpha_{i-1}\in\mathbb R .$$
--
--   For a matrix $A$, the **conjugate direction space** $W_i$ is the set of vectors $v$ with $(Ap_j,v)=0$ for $j=0,\dots,i-1$, and the **plane $\pi_i$ through a point $y$ conjugate to $p_0,\dots,p_{i-1}$** is $\pi_i=y+W_i$, the set of points $x$ with
--
--   $$(Ap_j,x-y)=0\qquad(j=0,1,\dots,i-1).$$
--
--   In the paper $y=x_i$. $P_i$ is the plane on which the cd- and cg-methods minimize the error function (Theorems 4:3, 6:1, 7:2); $\pi_i$ is the plane of Theorems 4:6 and 6:7.
--
--   **Formalization Note** Directions form a 0-based sequence `p : ℕ → (Fin n → ℝ)`; $P_i$ is `cdPlane x₀ p i`, $W_i$ is `conjDir A p i`, the kernel of the linear map $v\mapsto((Ap_j,v))_{j<i}$, and $\pi_i$ is `conjPlane A p y i`.
--
--   `levelSection A h y p i` is the level section $\{z\in\pi_i:f(z)=f(y)\}$, with $\pi_i$ through $y$ and $f(z)=(h-z,A(h-z))$.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 413, eq. (4:10); p. 414, Theorem 4:6; p. 417, equation of the plane $\pi_i$ (PDF p. 5)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- The plane `Pᵢ` of (4:10) (Hestenes–Stiefel 1952, p. 413): the points
`x = x₀ + α₀p₀ + ⋯ + αᵢ₋₁pᵢ₋₁` with real parameters `α₀, …, αᵢ₋₁`. The directions are a
0-based sequence `p : ℕ → ℝⁿ`; only `p 0, …, p (i - 1)` enter. -/
def cdPlane {n : ℕ} (x₀ : Fin n → ℝ) (p : ℕ → Fin n → ℝ) (i : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ α : ℕ → ℝ, x = x₀ + ∑ j ∈ Finset.range i, α j • p j}

/-- The direction space of the plane `πᵢ` of Theorem 4:6 (p. 414; equation on p. 417): the
vectors `v` with `(Apⱼ, v) = 0` for `j = 0, …, i − 1`, i.e. the vectors conjugate to
`p₀, …, pᵢ₋₁`. -/
def conjDir {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ → Fin n → ℝ) (i : ℕ) :
    Submodule ℝ (Fin n → ℝ) :=
  LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (j : Fin i) (l : Fin n) => (A *ᵥ p j) l))

/-- The plane `πᵢ` through the point `y` (in the paper `y = xᵢ`) conjugate to
`p₀, …, pᵢ₋₁`: the points `x` with `(Apⱼ, x − y) = 0` for `j = 0, …, i − 1`. -/
def conjPlane {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p : ℕ → Fin n → ℝ) (y : Fin n → ℝ)
    (i : ℕ) : Set (Fin n → ℝ) :=
  {x | x - y ∈ conjDir A p i}

/-- The level section Eᵢ′ in Theorem 4:6. At level zero this is the singleton solution. -/
def levelSection {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h y : Fin n → ℝ)
    (p : ℕ → Fin n → ℝ) (i : ℕ) : Set (Fin n → ℝ) :=
  {z | z ∈ conjPlane A p y i ∧ errorFun A h z = errorFun A h y}

end ConjGrad.ErrorDecrease.Supplement


