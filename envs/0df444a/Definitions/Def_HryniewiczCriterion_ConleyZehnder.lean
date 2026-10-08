-- Prove2me | Definitions.Def_HryniewiczCriterion_ConleyZehnder
-- name    : HryniewiczCriterion_ConleyZehnder
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-05T17:53:49.118121+00:00
-- url     : https://prove2.me/theorems/04e97a5c-3b89-44de-908a-4c22f0b4adc2
-- title:
--   Conley–Zehnder index via winding intervals; dynamical convexity
-- statement:
--   **Winding interval.** Let $\varphi:[0,1]\to Sp(1)$ be a path with $\varphi(0)=I$. For $s\in[0,2\pi]$ let $\theta(\cdot,s)$ be the continuous argument of $t\mapsto\varphi(t)e^{is}$ with $\theta(0,s)=s$, so that $\varphi(t)e^{is}=r\,e^{i\theta(t,s)}$ with $r>0$. Put $\Delta(s)=(\theta(1,s)-s)/2\pi$. The winding interval is
--   $$I(\varphi)=\{\Delta(s): s\in[0,2\pi]\}.$$
--
--   **Conley–Zehnder index.** With $I(\varphi)=[a,b]$, Hryniewicz sets $\hat\mu(J)=2k$ if $k\in J\cap\mathbb{Z}$ and $\hat\mu(J)=2k+1$ if $J\subset(k,k+1)$. Degenerate paths use the lower semicontinuous extension $\hat\mu(J)=\lim_{\epsilon\to0^+}\hat\mu(J-\epsilon)$. In closed form,
--   $$\mu(\varphi)=\begin{cases}2(\lceil b\rceil-1) & \text{if } a\le\lceil b\rceil-1,\\ 2\lceil b\rceil-1 & \text{otherwise.}\end{cases}$$
--
--   **Index of a periodic orbit.** Let $P=(x,T)$ be a periodic orbit of $X_H$ on $S=H^{-1}(1)$ and let $Y(t)$ be the linearized flow, $Y(0)=\mathrm{id}$, $\dot Y=DX_H(x(t))\,Y$. Project $T_xS$ onto $\xi_x=\ker\lambda_0$ along $X_H$; this turns the linearized Hamiltonian flow into the linearized Reeb flow on $\xi$. The path $\varphi(\tau)$, $\tau\in[0,1]$, is the matrix of $v\mapsto\pi_{x(T\tau)}Y(T\tau)v$, $\xi_{x(0)}\to\xi_{x(T\tau)}$, in the global symplectic frame $Z_1,Z_2$. Then $\mu_{CZ}(P)=\mu(\varphi)$.
--
--   **Dynamical convexity** (Definition 1.1, after Hofer–Wysocki–Zehnder): $\mu_{CZ}(P)\ge3$ for every periodic orbit $P$ on $S$, prime or multiply covered.
--
--   On the round sphere every Hopf fibre has $\mu_{CZ}=3$. On an ellipsoid with radii $r_1<r_2$ the short axis has index $3$ and the long axis index $2\lfloor r_2^2/r_1^2\rfloor+1$.
--
--   **Formalization Note** Paths are maps `ℝ → Matrix (Fin 2) (Fin 2) ℝ` used on $[0,1]$. Dynamical convexity quantifies over every solution `Y` of the variational equation; for smooth $H$ that solution exists and is unique.
-- source:
--   Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014) 791-862, https://arxiv.org/abs/1105.2077, Section 2.1.1, pp. 5-6 (winding interval, eqs. (4)-(5)) and Definition 1.1, p. 1

import Definitions.Def_HryniewiczCriterion_Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The Conley–Zehnder index and dynamical convexity

Hryniewicz, arXiv:1105.2077, §2.1.1 (pp. 5–6): the winding interval `I(φ)` of a path
`φ : [0, 1] → Sp(1)` with `φ(0) = I`, the index `μ̂(I(φ))` of (4), its lower
semicontinuous extension (5) to degenerate paths, and Definition 1.1 (dynamical
convexity). The path attached to a periodic orbit is the linearized flow on `ξ`
written in the global frame `Z₁, Z₂` of `Definitions.Def_HryniewiczCriterion_Basic`.
-/

namespace HryniewiczCriterion

noncomputable section

/-- The unit vector `e^{is} = (cos s, sin s)` of `ℝ²`. -/
def rotationVector (s : ℝ) : Fin 2 → ℝ := ![Real.cos s, Real.sin s]

/-- `θ` is a continuous argument of `t ↦ φ(t) e^{is}` on `[0, 1]` with `θ(0) = s`:
`φ(t) e^{is} = r e^{iθ(t)}` with `r > 0`. -/
def IsAngleLift (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContinuousOn θ (Set.Icc 0 1) ∧ θ 0 = s ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (φ t).mulVec (rotationVector s) = r • rotationVector (θ t)

/-- The winding interval `I(φ) = {Δ(s) : s ∈ [0, 2π]}`, `Δ(s) = (θ(1, s) - s) / 2π`
(total rotation of `e^{is}` under `φ`, in turns). -/
def windingInterval (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Set ℝ :=
  {d | ∃ s ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ∃ θ : ℝ → ℝ,
    IsAngleLift φ s θ ∧ d = (θ 1 - s) / (2 * Real.pi)}

/-- The Conley–Zehnder index `μ(φ) = μ̂(I(φ))` of (4)–(5): with `I(φ) = [a, b]`,
`μ̂(J) = lim_{ε → 0⁺} μ̂(J - ε)`, where `μ̂(J) = 2k` if `k ∈ J` and `2k + 1` if
`J ⊂ (k, k + 1)`. In closed form: `2(⌈b⌉ - 1)` if `a ≤ ⌈b⌉ - 1`, else `2⌈b⌉ - 1`. -/
def czIndexOfPath (φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : ℤ :=
  let a := sInf (windingInterval φ)
  let b := sSup (windingInterval φ)
  if a ≤ ((⌈b⌉ - 1 : ℤ) : ℝ) then 2 * (⌈b⌉ - 1) else 2 * ⌈b⌉ - 1

/-- `Y` is the linearized flow of `X_H` along `x`: `Y(0) = id` and
`Y'(t) = DX_H(x(t)) ∘ Y(t)`. -/
def IsLinearizedFlow (H : R4 → ℝ) (x : ℝ → R4) (Y : ℝ → (R4 →L[ℝ] R4)) : Prop :=
  Y 0 = ContinuousLinearMap.id ℝ R4 ∧
    ∀ t : ℝ, HasDerivAt Y ((fderiv ℝ (hamiltonianVectorField H) (x t)).comp (Y t)) t

/-- Projection onto `ker λ₀(x)` along `X_H(x)`. On `T_x S` it turns the linearized
Hamiltonian flow into the linearized Reeb flow on `ξ`. -/
def reebProjection (H : R4 → ℝ) (x v : R4) : R4 :=
  v - (liouvilleForm x v / liouvilleForm x (hamiltonianVectorField H x)) •
    hamiltonianVectorField H x

/-- Coordinates of `v ∈ ξ_x` in the frame `Z₁, Z₂`: `v = a Z₁ + b Z₂` with
`a = ω₀(v, Z₂)`, `b = ω₀(Z₁, v)`. -/
def xiCoords (H : R4 → ℝ) (x v : R4) : Fin 2 → ℝ :=
  ![omega0 v (xiFrame2 H x), omega0 (xiFrame1 H x) v]

/-- The path `φ : [0, 1] → Sp(1)` of a periodic orbit `P = (x, T)`: the linearized
Reeb flow on `ξ` from `x(0)` to `x(Tτ)`, in the frame `Z₁, Z₂`. Column `j` is the
image of `Zⱼ(x(0))`. -/
def linearizedXiPath (H : R4 → ℝ) (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)) :
    ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun τ => Matrix.of fun i j =>
    xiCoords H (P.x (P.T * τ))
      (reebProjection H (P.x (P.T * τ))
        (Y (P.T * τ) (![xiFrame1 H (P.x 0), xiFrame2 H (P.x 0)] j))) i

/-- Hryniewicz Definition 1.1 (after HWZ): every periodic orbit on `S`, prime or
multiply covered, has Conley–Zehnder index at least `3`. (On `S ≅ S³` every orbit
is contractible and `c₁(ξ) = 0`.) -/
def IsDynamicallyConvex (H : R4 → ℝ) : Prop :=
  ∀ (P : PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)),
    IsLinearizedFlow H P.x Y → 3 ≤ czIndexOfPath (linearizedXiPath H P Y)

end

end HryniewiczCriterion


