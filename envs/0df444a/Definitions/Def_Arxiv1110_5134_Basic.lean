-- Prove2me | Definitions.Def_Arxiv1110_5134_Basic
-- name    : Arxiv1110_5134_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T08:57:59.579257+00:00
-- url     : https://prove2.me/theorems/fa02e9a6-b66b-4025-8788-ee62b3eb9b60
-- title:
--   Stokes vectors, rotation matrices, transport and streaming operators for graded index media
-- statement:
--   Objects of Zhao, Tan and Liu (2011), arXiv:1110.5134.
--
--   1. **Stokes vector (Eq. 1).** A beam of intensity $I$ whose polarization ellipse has ellipticity angle $\chi$ and orientation angle $\psi$, measured in a right-hand frame, has Stokes vector $\mathbf I=(I,Q,U,V)=(I,\ I\cos2\chi\cos2\psi,\ I\cos2\chi\sin2\psi,\ I\sin2\chi)$.
--   2. **Torsion matrix (Eq. 14).** $\mathbf R(\kappa)$ is the $4\times4$ matrix with $R_{23}=2\kappa$, $R_{32}=-2\kappa$ and all other entries $0$, where $\kappa$ is the torsion of the ray.
--   3. **Rotation matrices (Eqs. 23, 31).** $\Re(\phi)$ has rows $(1,0,0,0)$, $(0,\cos2\phi,\sin2\phi,0)$, $(0,-\sin2\phi,\cos2\phi,0)$, $(0,0,0,1)$. The same matrix written through $c=\cos\phi$ for $\phi\in[0,\pi]$ has $\cos2\phi=2c^2-1$ and $\sin2\phi=2c\sqrt{1-c^2}$. With $\sigma=(\boldsymbol\Omega\times\boldsymbol\nu)\cdot\mathbf e_z$, the modified rotation matrix is $\tilde\Re(\phi_G)=\tfrac12(1+\operatorname{sgn}\sigma)\Re(\phi_G)+\tfrac12(1-\operatorname{sgn}\sigma)\Re(-\phi_G)$.
--   4. **Left-hand frame (Eq. 64).** $T=\operatorname{diag}(1,1,-1,1)$.
--   5. **Transport operator and source (Eq. 20).** Along a ray with arc length $s$ and refractive index $n(s)$, the transport operator is $n^2\,\frac{d}{ds}\big[\mathbf I/n^2\big]$. Directions are unit vectors of $\mathbb R^3$ with the solid-angle measure $d\Omega$ (total mass $4\pi$). The scattering source is $\frac1{4\pi}\int_{4\pi}\mathbf Z(\boldsymbol\Omega')\mathbf I(\boldsymbol\Omega')\,d\Omega'$. The derivative of a matrix-valued function of $s$ is taken entrywise.
--   6. **Frenet frame of a ray (Eq. 46).** For a ray with unit tangent $\boldsymbol\Omega(s)$: curvature $K=|d\boldsymbol\Omega/ds|$, principal normal $\boldsymbol\nu=K^{-1}d\boldsymbol\Omega/ds$, binormal $\mathbf b=\boldsymbol\Omega\times\boldsymbol\nu$, and torsion $\kappa=-\mathbf b\cdot d\boldsymbol\nu/ds$ (the paper's sign convention).
--   7. **Eulerian streaming operators (Eqs. 42, 49, 52, 55).** A field $\mathbf I(q,\theta,\varphi)$ depends on three spatial coordinates $q$ and the direction angles. In the local orthonormal frame of the coordinate system, $\boldsymbol\Omega=(\mu,\eta,\xi)=(\sin\theta\cos\varphi,\sin\theta\sin\varphi,\cos\theta)$, $\mathbf s_1=(-\sin\varphi,\cos\varphi,0)$, and the polar axis $\mathbf e_3$ is the third frame vector. The gradient components are
--      - Cartesian $(x,y,z)$: $(\partial_x,\partial_y,\partial_z)$;
--      - traditional cylindrical $(\rho,\Psi,z)$ with frame $(\mathbf e_\rho,\mathbf e_\Psi,\mathbf e_z)$: $(\partial_\rho,\rho^{-1}\partial_\Psi,\partial_z)$;
--      - new cylindrical $(\rho,\Psi,z)$ with frame $(\mathbf e_\Psi,\mathbf e_z,\mathbf e_\rho)$: $(\rho^{-1}\partial_\Psi,\partial_z,\partial_\rho)$;
--      - spherical $(\Theta,\Psi,\rho)$ with frame $(\mathbf e_\Theta,\mathbf e_\Psi,\mathbf e_\rho)$: $(\rho^{-1}\partial_\Theta,(\rho\sin\Theta)^{-1}\partial_\Psi,\partial_\rho)$.
--
--      With $\mathbf g=\nabla n/n$, each streaming operator is $\boldsymbol\Omega\cdot\nabla$, plus the coordinate terms printed in Eqs. (49), (52) and (55), plus $\frac1{\sin\theta}\{[(\xi\boldsymbol\Omega-\mathbf e_3)\cdot\mathbf g]\partial_\theta+[\mathbf s_1\cdot\mathbf g]\partial_\varphi\}$. The conservative angular term is $\frac1{\sin\theta}\{\partial_\theta[((\xi\boldsymbol\Omega-\mathbf e_3)\cdot\mathbf g)\mathbf I]+\partial_\varphi[(\mathbf s_1\cdot\mathbf g)\mathbf I]\}$.
--
--   **Formalization Note** Vectors of $\mathbb R^3$ are triples of components, with $|v|=\sqrt{v\cdot v}$ and the cross product of Mathlib. Partial derivatives are derivatives of one-variable slices. The modified rotation matrix is encoded with $\tfrac12$ in front of both terms; as printed, Eq. (31) puts $\tfrac12$ before the first term only (see the report). The streaming operators of Eqs. (42), (49), (52) and (55) are quoted by the paper from Refs. [26], [29], [30] and are taken here as definitions.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), Sections 2.1, 3.1-3.3, 4.1-4.2 and Appendix A: Eqs. (1), (14), (20), (23), (31), (42), (46), (49), (52), (55), (64)

import Mathlib

/-!
J. M. Zhao, J. Y. Tan and L. H. Liu, *On the Derivation of Vector Radiative Transfer Equation for
Polarized Radiative Transport in Graded Index Media*, arXiv:1110.5134v1 (2011).

Objects of the paper: the Stokes vector of a polarization ellipse (Eq. 1), the torsion matrix
`R` (Eq. 14), the Stokes rotation matrix (Eq. 23) and the modified rotation matrix (Eq. 31), the
right-hand/left-hand transformation `T` (Eq. 64), the transport operator `n² d/ds [I/n²]` and the
scattering source term of Eq. (20), the Frenet frame and torsion of a ray (Eq. 46), and the
Eulerian streaming operators of Section 4.2.2 (Eqs. 42, 49, 52, 55).
-/

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Arxiv1110_5134

/-- Section 2.1: a Stokes vector `(I, Q, U, V)`. -/
abbrev Stokes := Fin 4 → ℝ

/-- Eq. (1): the Stokes vector of an elliptically polarized beam of intensity `I`, ellipticity angle
`χ` and orientation angle `ψ`, defined in a right-hand frame:
`(I, I cos 2χ cos 2ψ, I cos 2χ sin 2ψ, I sin 2χ)`. -/
def stokesVec (I χ ψ : ℝ) : Stokes :=
  ![I, I * Real.cos (2 * χ) * Real.cos (2 * ψ), I * Real.cos (2 * χ) * Real.sin (2 * ψ),
    I * Real.sin (2 * χ)]

/-- Eq. (14): the matrix `R` accounting for the rotation of the polarization ellipse by Rytov's law,
with `R₂₃ = 2κ`, `R₃₂ = -2κ` and all other entries zero (`κ` the torsion of the ray). -/
def rytovMatrix (κ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, 0, 2 * κ, 0; 0, -(2 * κ), 0, 0; 0, 0, 0, 0]

/-- Eq. (23): the rotation matrix `ℜ(φ)` of Stokes vectors. -/
def stokesRot (φ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, Real.cos (2 * φ), Real.sin (2 * φ), 0;
     0, -Real.sin (2 * φ), Real.cos (2 * φ), 0;
     0, 0, 0, 1]

/-- Text after Eq. (23): the rotation matrix `ℜ(φ)` written through `c = cos φ` alone, using
`cos 2φ = 2c² - 1` and `sin 2φ = 2 sin φ cos φ` with `sin φ = √(1 - c²)` for `φ ∈ [0, π]`. -/
def stokesRotOfCos (c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, 2 * c ^ 2 - 1, 2 * c * Real.sqrt (1 - c ^ 2), 0;
     0, -(2 * c * Real.sqrt (1 - c ^ 2)), 2 * c ^ 2 - 1, 0;
     0, 0, 0, 1]

/-- Eqs. (26), (29), (31): the modified rotation matrix `ℜ̃(φ_G)`, where `σ = (Ω × ν)·e_z`:
`ℜ̃(φ_G) = ½ (1 + sgn σ) ℜ(φ_G) + ½ (1 - sgn σ) ℜ(-φ_G)`, so that it equals `ℜ(φ_G)` when `σ > 0`
(Eq. 26) and `ℜ(-φ_G)` when `σ < 0` (Eq. 29). (Eq. (31) as printed places the factor `½` before
the first term only; see the mission description.) -/
def modRot (σ φ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 2 : ℝ) • ((1 + Real.sign σ) • stokesRot φ + (1 - Real.sign σ) • stokesRot (-φ))

/-- Eq. (64): the matrix `T = diag(1, 1, -1, 1)` transforming a Stokes vector defined in the
right-hand frame into the Stokes vector defined in the left-hand frame (Eq. 63). -/
def handT : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, 1, -1, 1]

/-- Eqs. (13), (20): the transport operator `n² d/ds [I/n²]` applied to a Stokes vector `S(s)`
along a ray with refractive index `n(s)`, at ray coordinate `s`. -/
def transportOp (n : ℝ → ℝ) (S : ℝ → Stokes) (s : ℝ) : Stokes :=
  (n s ^ 2) • deriv (fun t => (n t ^ 2)⁻¹ • S t) s

/-- Directions of propagation: unit vectors `Ω ∈ ℝ³`. -/
abbrev Dir : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The solid-angle measure `dΩ` on the unit sphere (total mass `4π`). -/
def solidAngle : Measure Dir :=
  (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere

/-- Eqs. (18), (20): the scattering source `(1/4π) ∫_{4π} Z(Ω', Ω) I(Ω') dΩ'`, for the phase matrix
`Z(·, Ω)` of the current direction `Ω` and the Stokes vectors `I(Ω')` of the incident directions at
the current point. -/
def scatSource (Z : Dir → Matrix (Fin 4) (Fin 4) ℝ) (L : Dir → Stokes) : Stokes :=
  (1 / (4 * Real.pi)) • ∫ ω, Z ω *ᵥ L ω ∂solidAngle

/-- Eqs. (37), (38): the derivative `dM/ds` of a matrix-valued function of the ray coordinate,
taken entrywise. -/
def matDeriv (M : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => deriv (fun t => M t i j) s

/-- Vectors of `ℝ³` in Cartesian (or local orthonormal) components. -/
abbrev Vec3 := Fin 3 → ℝ

/-- The Euclidean length `|v| = √(v·v)` of a vector of `ℝ³`. -/
def vlen (v : Vec3) : ℝ :=
  Real.sqrt (v ⬝ᵥ v)

/-- Eq. (46): the curvature `K = |dΩ/ds|` of a ray with unit tangent `Ω(s)`. -/
def rayCurvature (Ω : ℝ → Vec3) (s : ℝ) : ℝ :=
  vlen (deriv Ω s)

/-- Fig. 2, Eq. (46): the principal normal `ν = (dΩ/ds)/K` of a ray with unit tangent `Ω(s)`. -/
def frenetNormal (Ω : ℝ → Vec3) (s : ℝ) : Vec3 :=
  (rayCurvature Ω s)⁻¹ • deriv Ω s

/-- Fig. 2, Eq. (46): the binormal `b = Ω × ν`, so that `ν, b, Ω` is a right-hand frame. -/
def frenetBinormal (Ω : ℝ → Vec3) (s : ℝ) : Vec3 :=
  Ω s ⨯₃ frenetNormal Ω s

/-- Eq. (46): the torsion of the ray in the paper's sign convention, `κ = -b · dν/ds`. -/
def rayTorsion (Ω : ℝ → Vec3) (s : ℝ) : ℝ :=
  -(frenetBinormal Ω s ⬝ᵥ deriv (frenetNormal Ω) s)

section Streaming

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The partial derivative `∂f/∂qᵢ` of a function of three spatial coordinates `q = (q₀, q₁, q₂)`. -/
def pd (f : Vec3 → E) (i : Fin 3) (q : Vec3) : E :=
  deriv (fun r => f (Function.update q i r)) (q i)

/-- Eq. (42) and Figs. 6-8: the components `(μ, η, ξ) = (sin θ cos φ, sin θ sin φ, cos θ)` of the
direction `Ω` in the local orthonormal frame of the coordinate system. -/
def dirVec (θ φ : ℝ) : Vec3 :=
  ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- Eq. (42) and Figs. 6-8: the auxiliary vector `s₁ = (-sin φ, cos φ, 0)` in the local frame. -/
def auxS1 (φ : ℝ) : Vec3 :=
  ![-Real.sin φ, Real.cos φ, 0]

/-- The polar axis of the angles `θ, φ` in the local frame: `k` (Eq. 42), `e_z` (Eq. 49),
`e_ρ` (Eqs. 52, 55); it is the third vector of the local frame in each case. -/
def polarAxis : Vec3 :=
  ![0, 0, 1]

/-- Eq. (42): the gradient in Cartesian coordinates `q = (x, y, z)`. -/
def cartGrad (f : Vec3 → E) (q : Vec3) : Fin 3 → E :=
  fun i => pd f i q

/-- Eq. (49): the gradient in the traditional cylindrical coordinates `q = (ρ, Ψ, z)` of Fig. 7(a),
in the local frame `(e_ρ, e_Ψ, e_z)`: `(∂/∂ρ, ρ⁻¹ ∂/∂Ψ, ∂/∂z)`. -/
def tradCylGrad (f : Vec3 → E) (q : Vec3) : Fin 3 → E :=
  ![pd f 0 q, (q 0)⁻¹ • pd f 1 q, pd f 2 q]

/-- Eq. (52): the gradient in the new cylindrical coordinates `q = (ρ, Ψ, z)` of Fig. 7(b), in the
local frame `(e_Ψ, e_z, e_ρ)`: `(ρ⁻¹ ∂/∂Ψ, ∂/∂z, ∂/∂ρ)`. -/
def newCylGrad (f : Vec3 → E) (q : Vec3) : Fin 3 → E :=
  ![(q 0)⁻¹ • pd f 1 q, pd f 2 q, pd f 0 q]

/-- Eq. (55): the gradient in the spherical coordinates `q = (Θ, Ψ, ρ)` of Fig. 8, in the local
frame `(e_Θ, e_Ψ, e_ρ)`: `(ρ⁻¹ ∂/∂Θ, (ρ sin Θ)⁻¹ ∂/∂Ψ, ∂/∂ρ)`. -/
def sphGrad (f : Vec3 → E) (q : Vec3) : Fin 3 → E :=
  ![(q 2)⁻¹ • pd f 0 q, (q 2 * Real.sin (q 0))⁻¹ • pd f 1 q, pd f 2 q]

/-- `Ω · G` for a vector `G` given by its components in the local frame. -/
def dirDot (θ φ : ℝ) (G : Fin 3 → E) : E :=
  ∑ i, dirVec θ φ i • G i

end Streaming

/-- `∂I/∂θ` for a field `I(q, θ, φ)` of position and direction angles. -/
def dTheta (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  deriv (fun θ' => F q θ' φ) θ

/-- `∂I/∂φ` for a field `I(q, θ, φ)` of position and direction angles. -/
def dPhi (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  deriv (fun φ' => F q θ φ') φ

/-- Eqs. (42), (44), (49), (50), (52), (53), (55), (56): the angular-redistribution term
`(1/sin θ) {[(ξΩ - e₃)·g] ∂I/∂θ + [s₁·g] ∂I/∂φ}`, where `g` holds the local components of `∇n/n`
and `e₃` is the polar axis. -/
def angularStream (g : Vec3) (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  (Real.sin θ)⁻¹ • (((Real.cos θ • dirVec θ φ - polarAxis) ⬝ᵥ g) • dTheta F q θ φ +
    (auxS1 φ ⬝ᵥ g) • dPhi F q θ φ)

/-- Eqs. (45), (48), (51), (54), (57): the angular term in conservative form,
`(1/sin θ) {∂/∂θ [((ξΩ - e₃)·g) I] + ∂/∂φ [(s₁·g) I]}`, with `g` the local components of `∇n/n`. -/
def angularCons (g : Vec3) (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  (Real.sin θ)⁻¹ •
    (deriv (fun θ' => ((Real.cos θ' • dirVec θ' φ - polarAxis) ⬝ᵥ g) • F q θ' φ) θ +
      deriv (fun φ' => (auxS1 φ' ⬝ᵥ g) • F q θ φ') φ)

/-- Eq. (42) (quoted from Ref. [26]): the Eulerian streaming operator `∂/∂s` in Cartesian
coordinates, `Ω·∇ + (1/sin θ){[(ξΩ - k)·∇n/n] ∂/∂θ + [s₁·∇n/n] ∂/∂φ}`. -/
def cartStream (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  dirDot θ φ (cartGrad (fun y => F y θ φ) q) + angularStream ((n q)⁻¹ • cartGrad n q) F q θ φ

/-- Eq. (49) (quoted from Ref. [29]): the Eulerian streaming operator in the traditional cylindrical
coordinates, `Ω·∇ - (η/ρ) ∂/∂φ + (1/sin θ){[(ξΩ - e_z)·∇n/n] ∂/∂θ + [s₁·∇n/n] ∂/∂φ}`. -/
def tradCylStream (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  dirDot θ φ (tradCylGrad (fun y => F y θ φ) q) -
    (Real.sin θ * Real.sin φ / q 0) • dPhi F q θ φ +
    angularStream ((n q)⁻¹ • tradCylGrad n q) F q θ φ

/-- Eq. (52) (quoted from Ref. [30]): the Eulerian streaming operator in the new cylindrical
coordinates, `Ω·∇ - μ (cos φ/ρ) ∂/∂θ + ξ (sin φ cos φ/ρ) ∂/∂φ
+ (1/sin θ){[(ξΩ - e_ρ)·∇n/n] ∂/∂θ + [s₁·∇n/n] ∂/∂φ}`. -/
def newCylStream (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  dirDot θ φ (newCylGrad (fun y => F y θ φ) q) -
    (Real.sin θ * Real.cos φ * Real.cos φ / q 0) • dTheta F q θ φ +
    (Real.cos θ * Real.sin φ * Real.cos φ / q 0) • dPhi F q θ φ +
    angularStream ((n q)⁻¹ • newCylGrad n q) F q θ φ

/-- Eq. (55) (quoted from Ref. [29]): the Eulerian streaming operator in the spherical coordinates,
`Ω·∇ - (sin θ/ρ) ∂/∂θ - (η cot Θ/ρ) ∂/∂φ + (1/sin θ){[(ξΩ - e_ρ)·∇n/n] ∂/∂θ + [s₁·∇n/n] ∂/∂φ}`. -/
def sphStream (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3) (θ φ : ℝ) : Stokes :=
  dirDot θ φ (sphGrad (fun y => F y θ φ) q) -
    (Real.sin θ / q 2) • dTheta F q θ φ -
    (Real.sin θ * Real.sin φ * Real.cot (q 0) / q 2) • dPhi F q θ φ +
    angularStream ((n q)⁻¹ • sphGrad n q) F q θ φ

end Arxiv1110_5134


