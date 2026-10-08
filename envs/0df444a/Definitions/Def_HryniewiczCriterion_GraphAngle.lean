-- Prove2me | Definitions.Def_HryniewiczCriterion_GraphAngle
-- name    : HryniewiczCriterion_GraphAngle
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-06T15:16:44.063521+00:00
-- url     : https://prove2.me/theorems/aa060ff9-627a-4186-a484-b43599d350ea
-- title:
--   Graph angles of symplectic matrices and the homogeneous convex model
-- statement:
--   Auxiliary objects for the finite-dimensional form of the Hofer–Wysocki–Zehnder index estimate for strictly convex energy surfaces in $\mathbb{R}^4$.
--
--   * **Homogeneous convex model.** $K:\mathbb{R}^4\to\mathbb{R}$ is smooth on $\mathbb{R}^4\setminus\{0\}$, satisfies $K(rx)=r^2K(x)$ for $r>0$, is positive away from $0$, and has Hessian positive definite on all vectors at every point of $K^{-1}(1)$ (HWZ (3.32)).
--   * **Frame.** `homogFrame K x` is the matrix with columns $x$, $X_K(x)/\omega_0(x,X_K(x))$, $Z_1(x)$, $Z_2(x)$, where $Z_1,Z_2$ is the global frame of $\xi$. `frameFlowMatrix` is $F^{-1}Z(t)F$ with $F$ the frame at $x(0)$. `symplJ4` is the matrix $J$ with $X_H=J\nabla H$, and `blockOne g` $=\operatorname{diag}(I_2,g)$.
--   * **Graph unitary.** For a real $2n\times2n$ matrix $M$ (here $n=1,2$) the graph $\Gamma_M=\{(z,Mz)\}$ is encoded as a complex matrix $A$ whose columns are positions plus $i$ times momenta, with momenta of the first factor negated (form $-\omega_0\oplus\omega_0$). `lagUnitary A` $=A(A^{*}A)^{-1}A^{\mathsf T}$ is the Souriau image $W(L)=UU^{\mathsf T}$ of the Lagrangian, and `graphUnitary` is $W(\Gamma_M)W(\Delta)^{-1}$ with $\Delta=\Gamma_I$. Its eigenvalue $1$ has multiplicity $\dim\ker(M-I)$ when $M$ is symplectic.
--   * **Angles.** `angPos z` is $\arg z$ normalized to $(0,2\pi]$ (so `angPos 1` $=2\pi$). `eigenAngleSum V` sums `angPos` over the eigenvalues of $V$ with algebraic multiplicity. `IsDetAngleLift V T θ`: $\theta$ is continuous on $[0,T]$, $\theta(0)=0$ and $\det V(t)=e^{i\theta(t)}$. `IsPolarAngleLift φ α`: $\alpha$ is continuous on $[0,1]$, $\alpha(0)=0$ and $\varphi(t)=R(\alpha(t))P(t)$ with $P(t)$ symmetric positive definite.
-- source:
--   Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Section 3, pp. 219–222, (3.32)–(3.46); Souriau map of the Lagrangian Grassmannian as in Robbin–Salamon, The Maslov index for paths, Topology 32 (1993) 827–844; contact frame of Hryniewicz, https://arxiv.org/html/1105.2077v5, Section 2.1.1, equations (4)–(5).

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Graph angles of symplectic matrices and the homogeneous convex model

Auxiliary objects for the Hofer–Wysocki–Zehnder index estimate (Ann. of Math. 148 (1998),
Theorem 3.4, pp. 219–222), in a finite-dimensional form.

* `IsHomogeneousConvexModel K`: `K` is positively homogeneous of degree two, smooth away from
  the origin and positive there, with Hessian positive definite on every vector at the points
  of its unit level. HWZ (3.32) take `K` to be the square of the Minkowski functional.
* `homogFrame K x`: the symplectic frame `x, X_K(x)/ω₀(x, X_K(x)), Z₁(x), Z₂(x)` of `ℝ⁴`
  (HWZ (3.35)–(3.36): the splitting `ℝ⁴ = span{x, X_K(x)} ⊕ ξ_x`).
* `graphUnitary4 g`, `graphUnitary2 g`: for a real matrix `g`, the unitary `W(Γ_g) W(Δ)⁻¹`,
  where `Γ_g = {(z, g z)}` lies in `(ℝ²ⁿ ⊕ ℝ²ⁿ, -ω₀ ⊕ ω₀)`, `Δ = Γ_1`, and `W(L) = U Uᵀ` for a
  unitary basis `U` of a Lagrangian `L` (Souriau map). Its eigenvalue `1` occurs exactly on
  `ker (g - 1)`.
* `angPos`, `eigenAngleSum`: the argument normalized to `(0, 2π]` and its sum over the
  eigenvalues of a complex matrix, with multiplicity.
* `IsDetAngleLift`, `IsPolarAngleLift`: continuous lifts of the determinant angle of a unitary
  path and of the rotation angle in the polar decomposition of a path in `SL(2, ℝ)`.
-/

namespace HryniewiczCriterion

noncomputable section

open scoped ContDiff

/-- HWZ (3.32): `K` is smooth on `ℝ⁴ \ {0}`, positively homogeneous of degree two and positive
away from the origin, and its Hessian is positive definite on all vectors at every point of
`K⁻¹(1)`. -/
def IsHomogeneousConvexModel (K : R4 → ℝ) : Prop :=
  ContDiffOn ℝ ∞ K {x | x ≠ 0} ∧
  (∀ r : ℝ, 0 < r → ∀ x : R4, K (r • x) = r ^ 2 * K x) ∧
  (∀ x : R4, x ≠ 0 → 0 < K x) ∧
  (∀ x : R4, K x = 1 → ∀ v : R4, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ K) x v v)

/-- The matrix with columns `x`, `X_K(x) / ω₀(x, X_K(x))`, `Z₁(x)`, `Z₂(x)`. On the unit level
of a homogeneous convex model it is symplectic for `ω₀`, and its column pairs `(0, 1)` and
`(2, 3)` span `span{x, X_K(x)}` and `ξ_x`. -/
def homogFrame (K : R4 → ℝ) (x : R4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    (![x, (omega0 x (hamiltonianVectorField K x))⁻¹ • hamiltonianVectorField K x,
      xiFrame1 K x, xiFrame2 K x] j) i

/-- The linearized flow `Y(t)` written in the frame at the initial point:
`F(x(0))⁻¹ Y(t) F(x(0))`. -/
def frameFlowMatrix (K : R4 → ℝ) (Q : PeriodicOrbit K) (Z : ℝ → (R4 →L[ℝ] R4)) (t : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  (homogFrame K (Q.x 0))⁻¹ * LinearMap.toMatrix' (Z t : R4 →ₗ[ℝ] R4) * homogFrame K (Q.x 0)

/-- The matrix `J` with `X_H = J ∇H` in the coordinates `(q₁, p₁, q₂, p₂)`. -/
def symplJ4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

/-- The block matrix `diag(1₂, g)` on `ℝ⁴ = ℝ² ⊕ ℝ²` (coordinate pairs `(0, 1)` and `(2, 3)`). -/
def blockOne (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, g 0 0, g 0 1; 0, 0, g 1 0, g 1 1]

/-- `W(L) = A (Aᴴ A)⁻¹ Aᵀ` for a complex matrix `A` whose columns `aₖ = uₖ + i vₖ` encode a real
basis of a Lagrangian `L` (positions `uₖ`, momenta `vₖ`). It equals `U Uᵀ` for any unitary
basis `U` of `L`. -/
def lagUnitary {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A * (A.conjTranspose * A)⁻¹ * A.transpose

/-- The graph `Γ_g ⊂ ℝ⁴ ⊕ ℝ⁴` of `g` in complex coordinates. Column `k` is `(eₖ, g eₖ)`;
row `0`, `1` are the positions `q₁, q₂` of the first factor (momenta with reversed sign, for
`-ω₀`), rows `2`, `3` those of the second factor. -/
def graphBasis4 (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun r k =>
    ![((1 : Matrix (Fin 4) (Fin 4) ℝ) 0 k : ℂ) - Complex.I * ((1 : Matrix (Fin 4) (Fin 4) ℝ) 1 k : ℂ),
      ((1 : Matrix (Fin 4) (Fin 4) ℝ) 2 k : ℂ) - Complex.I * ((1 : Matrix (Fin 4) (Fin 4) ℝ) 3 k : ℂ),
      (g 0 k : ℂ) + Complex.I * (g 1 k : ℂ),
      (g 2 k : ℂ) + Complex.I * (g 3 k : ℂ)] r

/-- The graph `Γ_g ⊂ ℝ² ⊕ ℝ²` of a `2 × 2` matrix in complex coordinates. -/
def graphBasis2 (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r k =>
    ![((1 : Matrix (Fin 2) (Fin 2) ℝ) 0 k : ℂ) - Complex.I * ((1 : Matrix (Fin 2) (Fin 2) ℝ) 1 k : ℂ),
      (g 0 k : ℂ) + Complex.I * (g 1 k : ℂ)] r

/-- The unitary `W(Γ_g) W(Δ)⁻¹` for `g ∈ Sp(4)`. -/
def graphUnitary4 (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  lagUnitary (graphBasis4 g) * (lagUnitary (graphBasis4 1))⁻¹

/-- The unitary `W(Γ_g) W(Δ)⁻¹` for `g ∈ Sp(1)`. -/
def graphUnitary2 (g : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  lagUnitary (graphBasis2 g) * (lagUnitary (graphBasis2 1))⁻¹

/-- The argument of `z` normalized to `(0, 2π]`; in particular `angPos 1 = 2π`. -/
def angPos (z : ℂ) : ℝ := if 0 < Complex.arg z then Complex.arg z else Complex.arg z + 2 * Real.pi

/-- The sum of `angPos` over the eigenvalues of `V`, counted with algebraic multiplicity. -/
def eigenAngleSum {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ) : ℝ :=
  ((V.charpoly.roots).map angPos).sum

/-- `θ` is a continuous determinant angle of the unitary path `V` on `[0, T]` with `θ(0) = 0`:
`det V(t) = e^{iθ(t)}`. -/
def IsDetAngleLift {n : Type} [Fintype n] [DecidableEq n] (V : ℝ → Matrix n n ℂ) (T : ℝ)
    (θ : ℝ → ℝ) : Prop :=
  ContinuousOn θ (Set.Icc 0 T) ∧ θ 0 = 0 ∧
    ∀ t ∈ Set.Icc 0 T, (V t).det = Complex.exp ((θ t : ℂ) * Complex.I)

/-- The rotation by the angle `a`. -/
def rotationMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos a, -Real.sin a; Real.sin a, Real.cos a]

/-- `α` is a continuous polar angle of `φ` on `[0, 1]` with `α(0) = 0`:
`φ(t) = R(α(t)) P(t)` with `P(t)` symmetric positive definite. -/
def IsPolarAngleLift (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (α : ℝ → ℝ) : Prop :=
  ContinuousOn α (Set.Icc 0 1) ∧ α 0 = 0 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.PosDef ∧
      φ t = rotationMatrix (α t) * P

end

end HryniewiczCriterion


