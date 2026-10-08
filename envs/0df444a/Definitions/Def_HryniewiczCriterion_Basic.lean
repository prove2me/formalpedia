-- Prove2me | Definitions.Def_HryniewiczCriterion_Basic
-- name    : HryniewiczCriterion_Basic
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-05T17:32:23.370741+00:00
-- url     : https://prove2.me/theorems/6147e70c-6bbc-4656-ac26-c4757acebdf8
-- title:
--   Star-shaped energy surfaces in $\mathbb{R}^4$, Hamiltonian flows, periodic orbits
-- statement:
--   Basic objects on $\mathbb{R}^4$ with coordinates $x=(q_1,p_1,q_2,p_2)$.
--
--   1. The **Liouville form** $\lambda_0=\tfrac12\sum_j(q_j\,dp_j-p_j\,dq_j)$ and the symplectic form $\omega_0=d\lambda_0=\sum_j dq_j\wedge dp_j$.
--   2. For a smooth $H:\mathbb{R}^4\to\mathbb{R}$, the **energy surface** $S=H^{-1}(1)$. It is **strictly star-shaped** if $H$ is smooth, every ray $\{ru: r>0\}$, $u\neq 0$, meets $S$ exactly once, and $dH(x)\,x>0$ on $S$. It is **strictly convex** if the Hessian of $H$ is positive definite on every tangent space $T_xS=\ker dH(x)$, $x\in S$.
--   3. The **Hamiltonian vector field** $X_H$ is defined by $\omega_0(X_H,\cdot)=-dH$, that is
--   $$X_H=\Big(-\frac{\partial H}{\partial p_1},\ \frac{\partial H}{\partial q_1},\ -\frac{\partial H}{\partial p_2},\ \frac{\partial H}{\partial q_2}\Big).$$
--   With this sign $\lambda_0(X_H)=\tfrac12\,dH(x)\,x>0$ on a star-shaped $S$, so $X_H$ is a positive multiple of the Reeb vector field of $\lambda_0|_S$.
--   4. A **trajectory** is a solution $y:\mathbb{R}\to S$ of $\dot y=X_H(y)$. A **periodic orbit** $P=(x,T)$ is a trajectory with $x(t+T)=x(t)$ for all $t$ and $T>0$. It is **prime** if $T$ is its least positive period; multiple covers are periodic orbits too. Its image is $x(\mathbb{R})$.
--   5. The **global frame of the contact structure** $\xi=\ker\lambda_0\cap TS$. Let $Q_1x=(-q_2,p_2,q_1,-p_1)$ and $Q_2x=(p_2,q_2,-p_1,-q_1)$. Put
--   $$Z_1(x)=\frac{1}{|x|}\Big(Q_2x-\frac{dH(x)(Q_2x)}{dH(x)\,x}\,x\Big),\qquad Z_2(x)=\frac{1}{|x|}\Big(Q_1x-\frac{dH(x)(Q_1x)}{dH(x)\,x}\,x\Big).$$
--   On $S$ these span $\xi_x$ and satisfy $\omega_0(Z_1,Z_2)=1$. They are the images of the standard quaternionic frame of $\ker\lambda_0|_{S^3}$ under the radial diffeomorphism $S^3\to S$.
--
--   These are the objects of Hryniewicz's Section 3, where the contact form is written as $f\lambda_0|_{S^3}$, equivalently $\lambda_0|_S$ on a star-shaped $S$.
--
--   **Formalization Note** $\mathbb{R}^4$ is `Fin 4 → ℝ`. Its default norm is the sup norm, so the Euclidean inner product and norm are defined separately (`dot4`, `euclidNorm`). Smoothness means `ContDiff ℝ ∞`.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, p. 2 (Liouville form, star-shaped domains) and Section 3, p. 12 (reduction to $f\lambda_0|_{S^3}$)

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Star-shaped energy surfaces in `ℝ⁴` and their Hamiltonian flows

Basic objects for Hryniewicz, *Systems of global surfaces of section for dynamically
convex Reeb flows on the 3-sphere*, J. Symplectic Geom. 12 (2014), arXiv:1105.2077,
§1 (p. 2) and §3 (p. 12): the Liouville form `λ₀ = ½ Σ (q dp - p dq)`, the
symplectic form `ω₀ = dλ₀`, strictly star-shaped levels `S = H⁻¹(1)`, the Hamiltonian
vector field (a positive multiple of the Reeb field of `λ₀|S`), periodic orbits, and
the global symplectic frame of the contact structure `ξ = ker λ₀|S`.
-/

namespace HryniewiczCriterion

noncomputable section

open scoped ContDiff

/-- `ℝ⁴` with coordinates ordered `(q₁, p₁, q₂, p₂)`. -/
abbrev R4 := Fin 4 → ℝ

/-- The Liouville form `λ₀ = ½ (q₁ dp₁ - p₁ dq₁ + q₂ dp₂ - p₂ dq₂)` at `x`,
applied to `v`. -/
def liouvilleForm (x v : R4) : ℝ :=
  (x 0 * v 1 - x 1 * v 0 + x 2 * v 3 - x 3 * v 2) / 2

/-- The symplectic form `ω₀ = dλ₀ = dq₁ ∧ dp₁ + dq₂ ∧ dp₂`. -/
def omega0 (u v : R4) : ℝ :=
  u 0 * v 1 - u 1 * v 0 + u 2 * v 3 - u 3 * v 2

/-- The Euclidean inner product on `ℝ⁴`. -/
def dot4 (x y : R4) : ℝ := ∑ i, x i * y i

/-- The Euclidean norm on `ℝ⁴` (the default norm on `Fin 4 → ℝ` is the sup norm). -/
def euclidNorm (x : R4) : ℝ := Real.sqrt (dot4 x x)

/-- The partial derivative `∂H/∂xᵢ` at `x`. -/
def partialDeriv (H : R4 → ℝ) (x : R4) (i : Fin 4) : ℝ :=
  fderiv ℝ H x (Pi.single i 1)

/-- The Hamiltonian vector field `X_H`, defined by `ω₀(X_H, ·) = -dH`:
`X_H = (-∂H/∂p₁, ∂H/∂q₁, -∂H/∂p₂, ∂H/∂q₂)`. With this sign
`λ₀(X_H) = ½ dH(x) x`, so on a strictly star-shaped level `X_H` is a positive
multiple of the Reeb vector field of `λ₀|S`. -/
def hamiltonianVectorField (H : R4 → ℝ) (x : R4) : R4 :=
  ![-partialDeriv H x 1, partialDeriv H x 0, -partialDeriv H x 3, partialDeriv H x 2]

/-- The energy surface `S = H⁻¹(1)`. -/
def energySurface (H : R4 → ℝ) : Set R4 := {x | H x = 1}

/-- `S = H⁻¹(1)` is a strictly star-shaped hypersurface: `H` is smooth, every ray from
the origin meets `S` exactly once, and it crosses `S` transversally, `dH(x) x > 0`. -/
def IsStrictlyStarShapedLevel (H : R4 → ℝ) : Prop :=
  ContDiff ℝ ∞ H ∧
  (∀ u : R4, u ≠ 0 → ∃! r : ℝ, 0 < r ∧ H (r • u) = 1) ∧
  (∀ x : R4, H x = 1 → 0 < fderiv ℝ H x x)

/-- `S = H⁻¹(1)` bounds a strictly convex domain: the Hessian of `H` is positive
definite on every tangent space `T_x S = ker dH(x)`. -/
def IsStrictlyConvexLevel (H : R4 → ℝ) : Prop :=
  ∀ x : R4, H x = 1 → ∀ v : R4, v ≠ 0 → fderiv ℝ H x v = 0 →
    0 < fderiv ℝ (fderiv ℝ H) x v v

/-- `y` is a trajectory of `X_H` on `S`, defined for all times. -/
def IsTrajectory (H : R4 → ℝ) (y : ℝ → R4) : Prop :=
  (∀ t : ℝ, HasDerivAt y (hamiltonianVectorField H (y t)) t) ∧ ∀ t : ℝ, H (y t) = 1

/-- A periodic orbit `P = (x, T)` of `X_H` on `S`: a trajectory with period `T > 0`.
`T` need not be the least period, so multiple covers are included. -/
structure PeriodicOrbit (H : R4 → ℝ) where
  x : ℝ → R4
  T : ℝ
  T_pos : 0 < T
  trajectory : IsTrajectory H x
  periodic : ∀ t : ℝ, x (t + T) = x t

/-- `P` is prime (simply covered): `T` is the least positive period. -/
def PeriodicOrbit.IsPrime {H : R4 → ℝ} (P : PeriodicOrbit H) : Prop :=
  ∀ t : ℝ, 0 < t → t < P.T → P.x t ≠ P.x 0

/-- The geometric image `x(ℝ)` of a periodic orbit. -/
def PeriodicOrbit.image {H : R4 → ℝ} (P : PeriodicOrbit H) : Set R4 :=
  Set.range P.x

/-- The quaternionic matrix `Q₁ x = (-q₂, p₂, q₁, -p₁)`. -/
def quatQ1 (x : R4) : R4 := ![-x 2, x 3, x 0, -x 1]

/-- The quaternionic matrix `Q₂ x = (p₂, q₂, -p₁, -q₁)`; `Q₂ = J₀ Q₁` where
`ω₀(u, v) = ⟨u, J₀ v⟩`. Both `Q₁ x` and `Q₂ x` lie in `ker λ₀(x)`, and
`ω₀(Q₂ x, Q₁ x) = |x|²`. -/
def quatQ2 (x : R4) : R4 := ![x 3, x 2, -x 1, -x 0]

/-- Radial projection of `Q x` to `T_x S`: `Q x - (dH(x)(Q x) / dH(x) x) x`. This is
the push-forward of the round-sphere vector `Q u` under `u ↦ ρ(u) u`, `x = ρ(u) u`. -/
def xiFrameRaw (H : R4 → ℝ) (Q : R4 → R4) (x : R4) : R4 :=
  Q x - (fderiv ℝ H x (Q x) / fderiv ℝ H x x) • x

/-- First vector `Z₁ = |x|⁻¹ (Q₂ x - (dH(Q₂x)/dH(x)x) x)` of the global symplectic frame
of `ξ = ker λ₀ ∩ TS`. -/
def xiFrame1 (H : R4 → ℝ) (x : R4) : R4 := (euclidNorm x)⁻¹ • xiFrameRaw H quatQ2 x

/-- Second vector `Z₂ = |x|⁻¹ (Q₁ x - (dH(Q₁x)/dH(x)x) x)`; `ω₀(Z₁, Z₂) = 1`. -/
def xiFrame2 (H : R4 → ℝ) (x : R4) : R4 := (euclidNorm x)⁻¹ • xiFrameRaw H quatQ1 x

end

end HryniewiczCriterion


