-- Prove2me | Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
-- name    : AutomorphicForm_GL2RealOrbitalTransforms
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/4c80b67a-9d69-50b0-ac3d-aae1cf818943
-- title:
--   Split and elliptic orbital transforms on GL₂(ℝ)
-- statement:
--   Four explicit group elements are introduced in $\mathrm{GL}_2(\mathbb{R})$, each produced from a $2\times 2$ real matrix together with a proof that its determinant is non-zero: `rotation` $\theta$ with rows $(\cos\theta,\sin\theta)$ and $(-\sin\theta,\cos\theta)$; `upperTriangular` $a_1,a_2,u$ with rows $(a_1,u)$ and $(0,a_2)$, under the hypothesis $a_1a_2\neq 0$; `upperHalfPlaneElt` $x,y$ with rows $(y,x)$ and $(0,1)$, under $0<y$; and `ellipticElt` $r,\theta$ with rows $(r\cos\theta,r\sin\theta)$ and $(-r\sin\theta,r\cos\theta)$, under $0<r$. Two transforms of a function $f:\mathrm{GL}_2(\mathbb{R})\to\mathbb{C}$ are then defined by case distinction on the parameters. `splitTransform` $f\,a_1\,a_2$ is, when $a_1a_2\neq 0$, the quantity $\frac{1}{2\pi}\int_0^{2\pi}\!\int_{\mathbb{R}} f\bigl(k_\theta\, n(a_1,u,a_2)\,k_\theta^{-1}\bigr)\,du\,d\theta$ with $k_\theta$ the rotation and $n$ the upper-triangular element, and is $0$ when $a_1a_2=0$. `ellipticTransform` $f\,r\,\theta$ is, when $r>0$, the quantity $4\sin^2\theta\int_{y>0}\int_{x\in\mathbb{R}} \bigl(f(g\,r k_\theta\,g^{-1})+f(g\,r k_{-\theta}\,g^{-1})\bigr)y^{-2}\,dx\,dy$ with $g=g(x,y)$ the upper half-plane element, the two terms corresponding to the representatives $rk_{\theta}$ and $rk_{-\theta}$; it is $0$ when $r\le 0$ (and the inner integrand is set to $0$ off $y>0$). `discreteSeriesPairing` $k\,H\,E\,r$, for $k:\mathbb{N}$ and $H,E:\mathbb{R}\to\mathbb{R}\to\mathbb{C}$, is
--   $$\int_0^{\pi} E(r,\theta)\,U_{k-2}(\cos\theta)\,d\theta-\frac{2\pi}{r}\int_{\mathbb{R}} e^{-(k-1)|t|}\Bigl(H(re^{t},re^{-t})+(-1)^kH(-re^{t},-re^{-t})\Bigr)dt,$$
--   where $U_{k-2}$ is the Chebyshev polynomial of the second kind of integer index $(k:\mathbb{Z})-2$. Finally `entrySlice` turns a complex function $\Phi$ of a pair (a real $2\times 2$ entry array, a parameter $p$ in a type $P$) into the function on $\mathrm{GL}_2(\mathbb{R})$ sending $g$ to $\Phi$ evaluated at the entries of $g$ and at $p$.
--
--   **Relation to Mathlib.** The matrix elements are built with Mathlib's `Matrix.GeneralLinearGroup.mkOfDetNeZero` and the pairing uses Mathlib's `Chebyshev.U`; the split and elliptic transforms and the discrete-series pairing are the project's own notions, Mathlib having no orbital integrals for $\mathrm{GL}_2(\mathbb{R})$.
--
--   **Where it is used.** These are the archimedean charts and integral transforms in which the split and elliptic orbital data of a function on $\mathrm{GL}_2(\mathbb{R})$, and the weight-$k$ discrete-series pairing between them, are formulated; they feed the archimedean side of the adelic description of automorphic forms on $\mathrm{GL}_2$ used in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GL2RealOrbitalTransforms.lean

import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Polynomial

noncomputable section

namespace AutomorphicForm.GL2Real

def rotation (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
    (by rw [Matrix.det_fin_two_of]; nlinarith [Real.cos_sq_add_sin_sq θ])

def upperTriangular (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a₁, u; 0, a₂]
    (by rw [Matrix.det_fin_two_of]; simpa using h)

def upperHalfPlaneElt (x y : ℝ) (hy : 0 < y) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![y, x; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [hy.ne'])

def ellipticElt (r θ : ℝ) (hr : 0 < r) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ]
    (by
      rw [Matrix.det_fin_two_of]
      have h1 : 0 < r ^ 2 := by positivity
      nlinarith [Real.cos_sq_add_sin_sq θ])

def splitTransform (f : GL (Fin 2) ℝ → ℂ) (a₁ a₂ : ℝ) : ℂ :=
  if h : a₁ * a₂ ≠ 0 then
    (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ u : ℝ,
        f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹)
  else 0

def ellipticTransform (f : GL (Fin 2) ℝ → ℂ) (r θ : ℝ) : ℂ :=
  if hr : 0 < r then
    (4 * Real.sin θ ^ 2 : ℂ) *
      ∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        if hy : 0 < y then
          (f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
              f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹)) /
            ((y : ℂ) ^ 2)
        else 0
  else 0

def discreteSeriesPairing (k : ℕ) (H : ℝ → ℝ → ℂ) (E : ℝ → ℝ → ℂ) (r : ℝ) : ℂ :=
  (∫ θ in (0 : ℝ)..Real.pi, E r θ * (((Chebyshev.U ℝ ((k : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) -
    (2 * Real.pi / r : ℂ) *
      ∫ t : ℝ, (Real.exp (-(((k : ℝ) - 1) * |t|)) : ℂ) *
        (H (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ k * H (-(r * Real.exp t)) (-(r * Real.exp (-t))))

def entrySlice {P : Type*} (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (p : P) : GL (Fin 2) ℝ → ℂ :=
  fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)

end AutomorphicForm.GL2Real

end


