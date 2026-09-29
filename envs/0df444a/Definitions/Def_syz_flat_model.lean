-- Prove2me | Definitions.Def_syz_flat_model
-- name    : syz_flat_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T03:50:26.569061+00:00
-- url     : https://prove2.me/theorems/cca0c375-345d-4e58-9a8c-726dad59a06c
-- title:
--   SYZ D-brane moduli space: the flat ambient model
-- statement:
--   This file fixes the setting in which Section 3 of Strominger–Yau–Zaslow is formalized.
--
--   The ambient Calabi–Yau manifold is modelled by $\mathbb C^n$ with its flat Calabi–Yau structure: the metric $g(u,v)=\operatorname{Re}\langle u,v\rangle$, the Kähler form $\omega(u,v)=\operatorname{Im}\langle u,v\rangle=g(iu,v)$, the holomorphic volume form $\Omega=dz^1\wedge\cdots\wedge dz^n$ and its imaginary part $\kappa=\operatorname{Im}\Omega$.
--
--   A brane is an $n$-torus, presented by its universal cover: a map $f:\mathbb R^n\to\mathbb C^n$ which is periodic up to translation, $f(x+e_a)=f(x)+\lambda_a$ for a fixed period family $\lambda$. Such a map is the same thing as a map of $\mathbb R^n/\mathbb Z^n$ into the complex torus $\mathbb C^n/\Lambda$, and integration over the brane is integration over the unit cube.
--
--   From an immersion $f$ the file builds the induced metric $g_{ij}=g(\partial_i f,\partial_j f)$, the volume density $\sqrt{\det g}$, the Lagrangian condition $f^{*}\omega=0$ and the special Lagrangian condition $f^{*}\omega=f^{*}\kappa=0$, and the second fundamental form $h_{ijk}=\omega(\partial_i\partial_j f,\partial_k f)$ of a Lagrangian immersion. For a family of such maps it builds the deformation $1$-forms $\theta_i=\omega(\dot f,\partial_i f)$, the notions of a closed, co-closed and harmonic $1$-form for the induced metric, the periods of a $1$-form, the $L^2$ (McLean) metric $g_{ab}$ on the moduli parameters, and the natural $n$-form $\Theta(\theta^{a_1},\dots,\theta^{a_n})=\int_L\theta^{a_1}\wedge\cdots\wedge\theta^{a_n}$.
--
--   Finally it defines the moduli space $\mathcal M=\mathbb R^m\times\mathbb R^m$ of branes together with their flat $U(1)$ connections, carrying the block-diagonal metric $G=g_{ab}(dt^a dt^b+ds^a ds^b)$, the constant almost complex structure $\mathcal J(\partial_{t^a})=\partial_{s^a}$, $\mathcal J(\partial_{s^a})=-\partial_{t^a}$ and the fundamental $2$-form $\omega_{\mathcal M}(X,Y)=G(\mathcal JX,Y)$; closedness of a $2$-form is expressed by the Palais formula on constant vector fields. The bundle of hypotheses used by the moduli-level statements of Section 3 — smoothness, periodicity, the special Lagrangian condition, the immersion condition, the harmonic gauge and constancy of the cohomology classes — is packaged as a single structure.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, Section 2 (supersymmetry conditions) and Section 3 (D-brane moduli space), pp. 245-254

import Mathlib

/-!
# SYZ: the D-brane moduli space, flat ambient model

Formalization setting for A. Strominger, S.-T. Yau, E. Zaslow,
*Mirror symmetry is T-duality*, Nucl. Phys. B 479 (1996) 243-259, Section 3.

The ambient Calabi-Yau is modelled by `ℂ^n` with its standard flat Calabi-Yau
structure, and the brane `L` by an `n`-torus, realised as maps `ℝ^n → ℂ^n` that
are periodic up to translation by a fixed period lattice.
-/

noncomputable section

open Complex Matrix MeasureTheory

namespace SYZ

/-- The Euclidean parameter space `ℝ^k`. -/
abbrev Dom (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The ambient Calabi-Yau, modelled by `ℂ^n`. -/
abbrev Amb (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The `i`-th standard basis vector of `ℝ^k`. -/
def basis {k : ℕ} (i : Fin k) : Dom k := EuclideanSpace.single i (1 : ℝ)

/-- The `i`-th partial derivative of a map defined on `ℝ^k`. -/
def D {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : Dom k → V) (i : Fin k) (x : Dom k) : V :=
  fderiv ℝ u x (basis i)

/-- The Riemannian metric of `ℂ^n`: `g(u,v) = Re ⟪u,v⟫`. -/
def gAmb {n : ℕ} (u v : Amb n) : ℝ := (inner ℂ u v).re

/-- The Kähler form of `ℂ^n`: `ω(u,v) = Im ⟪u,v⟫ = g(iu, v)`. -/
def kForm {n : ℕ} (u v : Amb n) : ℝ := (inner ℂ u v).im

/-- The holomorphic volume form `Ω = dz¹ ∧ ⋯ ∧ dzⁿ` of `ℂ^n`, evaluated on `n` vectors. -/
def hVol {n : ℕ} (v : Fin n → Amb n) : ℂ := Matrix.det (Matrix.of fun i j => v j i)

/-- `κ = Im Ω`, the imaginary part of the holomorphic volume form. -/
def kappa {n : ℕ} (v : Fin n → Amb n) : ℝ := (hVol v).im

/-- The induced (first fundamental form) metric `g_{ij} = g(∂_i f, ∂_j f)` of an immersion. -/
def gInd {n : ℕ} (f : Dom n → Amb n) (x : Dom n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => gAmb (D f i x) (D f j x)

/-- The Riemannian volume density `√(det g)` of the induced metric. -/
def volDens {n : ℕ} (f : Dom n → Amb n) (x : Dom n) : ℝ := Real.sqrt (gInd f x).det

/-- `f` pulls back the Kähler form to `0` at `x`: the Lagrangian condition `f*ω = 0`. -/
def IsLagrangianAt {n : ℕ} (f : Dom n → Amb n) (x : Dom n) : Prop :=
  ∀ i j, kForm (D f i x) (D f j x) = 0

/-- The special Lagrangian condition `f*ω = 0` and `f*κ = 0` at `x`. -/
def IsSpecialLagrangianAt {n : ℕ} (f : Dom n → Amb n) (x : Dom n) : Prop :=
  IsLagrangianAt f x ∧ kappa (fun i => D f i x) = 0

/-- The second fundamental form `h_{ijk} = ω(∂_i∂_j f, ∂_k f)` of a Lagrangian immersion. -/
def hTen {n : ℕ} (f : Dom n → Amb n) (i j k : Fin n) (x : Dom n) : ℝ :=
  kForm (D (D f j) i x) (D f k x)

/-- The deformation 1-form `θ_i = ω(∂_t f, ∂_i f)` of a one-parameter family. -/
def theta1 {n : ℕ} (F : ℝ → Dom n → Amb n) (t : ℝ) (x : Dom n) (i : Fin n) : ℝ :=
  kForm (deriv (fun s => F s x) t) (D (F t) i x)

/-- The deformation 1-forms `θ^a_i = ω(∂_{t^a} f, ∂_i f)` of an `m`-parameter family. -/
def thetaM {n m : ℕ} (F : Dom m → Dom n → Amb n) (a : Fin m) (t : Dom m)
    (x : Dom n) (i : Fin n) : ℝ :=
  kForm (D (fun s => F s x) a t) (D (F t) i x)

/-- The fundamental domain `[0,1]^n` of the torus `L = ℝ^n / ℤ^n`. -/
def cube (n : ℕ) : Set (Dom n) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- `f : ℝ^n → ℂ^n` descends to a map of the torus `ℝ^n/ℤ^n` into `ℂ^n / Λ`,
where `Λ` is generated by the periods `lam`. -/
def QuasiPeriodic {n : ℕ} (lam : Fin n → Amb n) (f : Dom n → Amb n) : Prop :=
  ∀ (a : Fin n) (x : Dom n), f (x + basis a) = f x + lam a

/-- The pointwise inner product `g^{ij} α_i β_j` of two 1-forms in the induced metric. -/
def formPair {n : ℕ} (f : Dom n → Amb n) (α β : Dom n → Fin n → ℝ) (x : Dom n) : ℝ :=
  ∑ i, ∑ j, (gInd f x)⁻¹ i j * α x i * β x j

/-- The `L²` inner product `∫_L g^{ij} α_i β_j dvol` of two 1-forms on the torus. -/
def L2pair {n : ℕ} (f : Dom n → Amb n) (α β : Dom n → Fin n → ℝ) : ℝ :=
  ∫ x in cube n, formPair f α β x * volDens f x

/-- `dα = 0` for a 1-form `α` on `ℝ^n`. -/
def IsClosed1Form {n : ℕ} (α : Dom n → Fin n → ℝ) : Prop :=
  ∀ i j x, D (fun y => α y j) i x = D (fun y => α y i) j x

/-- `d†α = 0`: the coordinate form of co-closedness, `∂_i(√g g^{ij} α_j) = 0`. -/
def IsCoclosed1Form {n : ℕ} (f : Dom n → Amb n) (α : Dom n → Fin n → ℝ) : Prop :=
  ∀ x, ∑ i, D (fun y => volDens f y * ∑ j, (gInd f y)⁻¹ i j * α y j) i x = 0

/-- `α` is harmonic for the induced metric: closed and co-closed. -/
def IsHarmonic1Form {n : ℕ} (f : Dom n → Amb n) (α : Dom n → Fin n → ℝ) : Prop :=
  IsClosed1Form α ∧ IsCoclosed1Form f α

/-- The period of a 1-form over the `b`-th cycle of the torus. -/
def period {n : ℕ} (α : Dom n → Fin n → ℝ) (b : Fin n) : ℝ := ∫ x in cube n, α x b

/-- The `L²` (McLean) metric `g_{ab}` on the moduli parameters. -/
def gMod {n m : ℕ} (F : Dom m → Dom n → Amb n) (a b : Fin m) (t : Dom m) : ℝ :=
  L2pair (F t) (thetaM F a t) (thetaM F b t)

/-- The natural `n`-form `Θ(θ^{a₁},…,θ^{aₙ}) = ∫_L θ^{a₁} ∧ ⋯ ∧ θ^{aₙ}` on moduli space. -/
def bigTheta {n m : ℕ} (F : Dom m → Dom n → Amb n) (a : Fin n → Fin m) (t : Dom m) : ℝ :=
  ∫ x in cube n, Matrix.det (Matrix.of fun p q : Fin n => thetaM F (a p) t x q)

/-- The moduli space `ℝ^m × ℝ^m` of branes together with their flat `U(1)` connections. -/
abbrev Mod (m : ℕ) := Dom m × Dom m

/-- The block diagonal moduli metric `g_{ab}(dt^a dt^b + ds^a ds^b)`. -/
def moduliMetric {m : ℕ} (g : Dom m → Matrix (Fin m) (Fin m) ℝ)
    (p : Mod m) (X Y : Mod m) : ℝ :=
  ∑ a, ∑ b, g p.1 a b * (X.1 a * Y.1 b + X.2 a * Y.2 b)

/-- The constant almost complex structure `J(∂_{t^a}) = ∂_{s^a}`, `J(∂_{s^a}) = -∂_{t^a}`. -/
def moduliJ {m : ℕ} (X : Mod m) : Mod m := (-X.2, X.1)

/-- The fundamental 2-form `ω(X,Y) = G(JX, Y) = g_{ab} dt^a ∧ ds^b` of the moduli metric. -/
def moduliKahler {m : ℕ} (g : Dom m → Matrix (Fin m) (Fin m) ℝ)
    (p : Mod m) (X Y : Mod m) : ℝ :=
  ∑ a, ∑ b, g p.1 a b * (X.1 a * Y.2 b - Y.1 a * X.2 b)

/-- The exterior derivative of a 2-form, evaluated on constant vector fields. -/
def d2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E → E → E → ℝ) (p X Y Z : E) : ℝ :=
  fderiv ℝ (fun q => w q Y Z) p X + fderiv ℝ (fun q => w q Z X) p Y
    + fderiv ℝ (fun q => w q X Y) p Z

/-- A 2-form is closed. -/
def IsClosed2Form {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E → E → E → ℝ) : Prop :=
  ∀ p X Y Z, d2 w p X Y Z = 0

/-- The data of Section 3: a smooth `m`-parameter family of special Lagrangian tori in
`ℂ^n / Λ`, in the harmonic gauge with constant periods. -/
structure SYZFamily (n m : ℕ) where
  /-- the period lattice generators of the ambient torus -/
  lam : Fin n → Amb n
  /-- the family of maps -/
  F : Dom m → Dom n → Amb n
  /-- joint smoothness in the moduli parameters and the brane coordinates -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) (fun p : Dom m × Dom n => F p.1 p.2)
  /-- every member descends to the torus, with the same periods -/
  periodic : ∀ t, QuasiPeriodic lam (F t)
  /-- every member is special Lagrangian -/
  slag : ∀ t x, IsSpecialLagrangianAt (F t) x
  /-- every member is an immersion -/
  immersed : ∀ t x, (gInd (F t) x).det ≠ 0
  /-- harmonic gauge: each deformation 1-form is harmonic -/
  harmonic : ∀ t a, IsHarmonic1Form (F t) (thetaM F a t)
  /-- the cohomology class of each deformation 1-form is constant along the family -/
  periodConst : ∀ (a : Fin m) (b : Fin n) (c : Fin m) (t : Dom m),
      D (fun s => period (thetaM F a s) b) c t = 0

end SYZ


