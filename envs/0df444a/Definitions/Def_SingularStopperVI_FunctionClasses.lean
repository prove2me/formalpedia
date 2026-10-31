-- Prove2me | Definitions.Def_SingularStopperVI_FunctionClasses
-- name    : SingularStopperVI_FunctionClasses
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:13.147994+00:00
-- url     : https://prove2.me/theorems/341dff32-1874-4a6f-9490-eb9c44b872bd
-- title:
--   Parabolic Hölder classes $C^{j,k,\alpha}$, $C^{j,k,\alpha}_{\ell oc}$, $C^{j,k,\alpha}_{Loc}$ and the Sobolev class $W^{1,2,p}_{\ell oc}$
-- statement:
--   The function spaces of §2 on $\mathbb R^{d+1}_{0,T}=[0,T]\times\mathbb R^d$.
--
--   The **parabolic distance** is $\mathrm d((t,x),(s,y))=(|t-s|+|x-y|_d^2)^{1/2}$. For $\alpha\in(0,1)$ the Hölder norm is
--
--   $$
--   \|f\|_{C^\alpha(\bar{\mathcal O})}=\|f\|_{C^0(\bar{\mathcal O})}+\sup_{z_1\ne z_2}\frac{|f(z_1)-f(z_2)|}{\mathrm d^\alpha(z_1,z_2)}.
--   $$
--
--   The norms $\|f\|_{C^{0,1,\alpha}}$ and $\|f\|_{C^{1,2,\alpha}}$ add the Hölder norms of $\partial_{x_i}f$, and of $\partial_tf$ and $\partial_{x_ix_j}f$. A function lies in $C^{j,k,\alpha}_{\ell oc}(\mathbb R^{d+1}_{0,T})$ if it has finite norm on every bounded set, up to $t=T$, and in $C^{j,k,\alpha}_{Loc}(\mathbb R^{d+1}_{0,T})$ if it is continuous and has finite norm on $[0,S]\times\bar B$ for every $S<T$: derivatives of such a function may blow up at $T$. The class $W^{1,2,p}_{\ell oc}$ holds the functions with weak derivatives $\partial_tu,\partial_{x_i}u,\partial_{x_ix_j}u$ in $L^p$ of every bounded set, with norm the sum of the $L^p$ norms.
--
--   These classes state the regularity of $f,g,h$ and of the solutions of Problems A, B and C.
--
--   **Formalization Note** A class names its derivatives through a `Jet`, so that no `fderiv` junk value occurs. Bounded sets are replaced by the exhausting cylinders $[0,T]\times\bar B_R$. Norms take values in $[0,\infty]$.
-- source:
--   Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, §2, pp.3–4

import Mathlib

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace SingularStopperVI

/-- The state space `ℝ^d`, with its Euclidean norm `|·|_d`. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The `i`-th coordinate unit vector of `ℝ^d`. -/
noncomputable def unitVec (i : Fin d) : Euc d := EuclideanSpace.single i 1

/-- `ℝ^{d+1}_{0,T} := [0,T] × ℝ^d`. Bovo, De Angelis, Issoglio, arXiv:2203.06247v3, §2, p.3. -/
def stateDomain (d : ℕ) (T : ℝ) : Set (ℝ × Euc d) := Icc 0 T ×ˢ univ

/-- The cylinder `O_R = [0,T) × B_R`, with `B_R` the open ball of radius `R` about the origin.
arXiv:2203.06247v3, §2, p.3 and §4.1, p.8. -/
def openCyl (d : ℕ) (T R : ℝ) : Set (ℝ × Euc d) := Ico 0 T ×ˢ Metric.ball 0 R

/-- The closed cylinder `Ō_R = [0,T] × B̄_R`. -/
def closedCyl (d : ℕ) (T R : ℝ) : Set (ℝ × Euc d) := Icc 0 T ×ˢ Metric.closedBall 0 R

/-- The parabolic distance `d(z₁,z₂) = (|t−s| + |x−y|_d²)^{1/2}`. arXiv:2203.06247v3, §2, p.4. -/
noncomputable def parabolicDist (z₁ z₂ : ℝ × Euc d) : ℝ :=
  Real.sqrt (|z₁.1 - z₂.1| + ‖z₁.2 - z₂.2‖ ^ 2)

/-- `‖φ‖_{C⁰(A)} = sup_{z ∈ A} |φ(z)|`, (2.1), p.3, valued in `[0,∞]` so that an unbounded `φ` has
norm `∞` and not a junk value. -/
noncomputable def supNorm (A : Set (ℝ × Euc d)) (φ : ℝ → Euc d → ℝ) : ℝ≥0∞ :=
  ⨆ z ∈ A, ENNReal.ofReal |φ z.1 z.2|

/-- The parabolic Hölder norm `‖φ‖_{C^α(A)} = ‖φ‖_{C⁰(A)} + sup_{z₁≠z₂} |φ(z₁)−φ(z₂)| / d^α(z₁,z₂)`,
arXiv:2203.06247v3, §2, p.4, valued in `[0,∞]`. -/
noncomputable def holderNorm (α : ℝ) (A : Set (ℝ × Euc d)) (φ : ℝ → Euc d → ℝ) : ℝ≥0∞ :=
  supNorm A φ + ⨆ z₁ ∈ A, ⨆ z₂ ∈ A, ⨆ _ : z₁ ≠ z₂,
    ENNReal.ofReal (|φ z₁.1 z₁.2 - φ z₂.1 z₂.2| / parabolicDist z₁ z₂ ^ α)

/-- Names for the derivatives of a function `u` on `ℝ^{d+1}_{0,T}`: `ut` for `∂_t u`, `Du` for the
spatial gradient `∇u` and `D2u` for the spatial Hessian `D²u`.

**Formalization Note** A class below says of which function these are the derivatives. Naming them
avoids `deriv` and `fderiv`, which return `0` where no derivative exists. -/
structure Jet (d : ℕ) where
  /-- the time derivative -/
  ut : ℝ → Euc d → ℝ
  /-- the spatial gradient -/
  Du : ℝ → Euc d → Euc d
  /-- the spatial Hessian -/
  D2u : ℝ → Euc d → Matrix (Fin d) (Fin d) ℝ

/-- On `O`, the spatial partial derivatives of `u` exist and equal `Du`; `u` and `Du` are continuous
on `O`. This is `C^{0,1}(O)` of §2, p.3, with named derivatives. -/
structure IsClassical01On (O : Set (ℝ × Euc d)) (u : ℝ → Euc d → ℝ) (Du : ℝ → Euc d → Euc d) :
    Prop where
  grad : ∀ z ∈ O, ∀ i, HasDerivAt (fun y : ℝ => u z.1 (z.2 + y • unitVec i)) (Du z.1 z.2 i) 0
  cont_u : ContinuousOn (fun z : ℝ × Euc d => u z.1 z.2) O
  cont_Du : ContinuousOn (fun z : ℝ × Euc d => Du z.1 z.2) O

/-- On `O`, `u` is classically `C^{1,2}` with derivatives `K`: `C^{1,2}(O)` of §2, p.3. The time
derivative is taken along `[0,T]`, hence one-sided at `t = 0`. -/
structure IsClassical12On (T : ℝ) (O : Set (ℝ × Euc d)) (u : ℝ → Euc d → ℝ) (K : Jet d) :
    Prop where
  space : IsClassical01On O u K.Du
  time : ∀ z ∈ O, HasDerivWithinAt (fun s => u s z.2) (K.ut z.1 z.2) (Icc 0 T) z.1
  hess : ∀ z ∈ O, ∀ i j,
    HasDerivAt (fun y : ℝ => K.Du z.1 (z.2 + y • unitVec j) i) (K.D2u z.1 z.2 i j) 0
  cont_ut : ContinuousOn (fun z : ℝ × Euc d => K.ut z.1 z.2) O
  cont_D2u : ∀ i j, ContinuousOn (fun z : ℝ × Euc d => K.D2u z.1 z.2 i j) O

/-- `‖φ‖_{C^{0,1,α}(A)} = ‖φ‖_{C^α(A)} + Σ_i ‖∂_{x_i}φ‖_{C^α(A)}`, §2, p.4. -/
noncomputable def c01Norm (α : ℝ) (A : Set (ℝ × Euc d)) (φ : ℝ → Euc d → ℝ)
    (Dφ : ℝ → Euc d → Euc d) : ℝ≥0∞ :=
  holderNorm α A φ + ∑ i, holderNorm α A (fun t x => Dφ t x i)

/-- `‖φ‖_{C^{1,2,α}(A)} = ‖φ‖_{C^{0,1,α}(A)} + ‖∂_tφ‖_{C^α(A)} + Σ_{ij} ‖∂_{x_i x_j}φ‖_{C^α(A)}`,
§2, p.4. -/
noncomputable def c12Norm (α : ℝ) (A : Set (ℝ × Euc d)) (φ : ℝ → Euc d → ℝ) (K : Jet d) : ℝ≥0∞ :=
  c01Norm α A φ K.Du + holderNorm α A K.ut +
    ∑ i, ∑ j, holderNorm α A (fun t x => K.D2u t x i j)

/-- `u ∈ C^{0,1,α}(Ō)` with gradient `Du`: classical derivatives on `O` and finite norm on the
closure `Ō`, where `Du` is the continuous extension. arXiv:2203.06247v3, §2, p.4. -/
def IsC01AlphaOn (α : ℝ) (O Obar : Set (ℝ × Euc d)) (u : ℝ → Euc d → ℝ)
    (Du : ℝ → Euc d → Euc d) : Prop :=
  IsClassical01On O u Du ∧ c01Norm α Obar u Du < ⊤

/-- `u ∈ C^{1,2,α}(Ō)` with derivatives `K`: classical derivatives on `O` and finite norm on the
closure `Ō`, where `K` is the continuous extension. arXiv:2203.06247v3, §2, p.4. -/
def IsC12AlphaOn (T α : ℝ) (O Obar : Set (ℝ × Euc d)) (u : ℝ → Euc d → ℝ) (K : Jet d) : Prop :=
  IsClassical12On T O u K ∧ c12Norm α Obar u K < ⊤

/-- `u ∈ C^{0,1,α}_{ℓoc}(ℝ^{d+1}_{0,T})`, §2, p.4: `C^{0,1,α}` on every bounded part of
`[0,T] × ℝ^d`. **Formalization Note** Bounded sets are exhausted by the cylinders `Ō_R`. -/
def IsC01AlphaEll (T α : ℝ) (u : ℝ → Euc d → ℝ) (Du : ℝ → Euc d → Euc d) : Prop :=
  ∀ R : ℝ, 0 < R → IsC01AlphaOn α (openCyl d T R) (closedCyl d T R) u Du

/-- `u ∈ C^{1,2,α}_{ℓoc}(ℝ^{d+1}_{0,T})`, §2, p.4: `C^{1,2,α}` on every bounded part of
`[0,T] × ℝ^d`, up to `t = T`. **Formalization Note** Bounded sets are exhausted by the cylinders
`Ō_R`. -/
def IsC12AlphaEll (T α : ℝ) (u : ℝ → Euc d → ℝ) (K : Jet d) : Prop :=
  ∀ R : ℝ, 0 < R → IsC12AlphaOn T α (openCyl d T R) (closedCyl d T R) u K

/-- `u ∈ C^{1,2,α}_{Loc}(ℝ^{d+1}_{0,T})`, §2, p.4: `u` is continuous on `[0,T] × ℝ^d`, and
`C^{1,2,α}` on `[0,S] × B̄_R` for each `S < T` and each ball. The derivatives may blow up at `T`.
This class, with the capital `L`, differs from `IsC12AlphaEll`. -/
def IsC12AlphaCapLoc (T α : ℝ) (u : ℝ → Euc d → ℝ) (K : Jet d) : Prop :=
  ContinuousOn (fun z : ℝ × Euc d => u z.1 z.2) (stateDomain d T) ∧
    ∀ S R : ℝ, 0 < S → S < T → 0 < R →
      IsC12AlphaOn T α (openCyl d S R) (closedCyl d S R) u K

/-- A test function: `φ ∈ C_c^∞((0,T) × ℝ^d)`. -/
structure IsTestFunction (T : ℝ) (φ : ℝ × Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ
  support : tsupport φ ⊆ Ioo 0 T ×ˢ univ

/-- The partial derivative of a test function in `t`. -/
noncomputable def dtTest (φ : ℝ × Euc d → ℝ) (z : ℝ × Euc d) : ℝ :=
  fderiv ℝ φ z (1, 0)

/-- The partial derivative of a test function in `x_i`. -/
noncomputable def dxTest (i : Fin d) (φ : ℝ × Euc d → ℝ) (z : ℝ × Euc d) : ℝ :=
  fderiv ℝ φ z (0, unitVec i)

/-- `u ∈ W^{1,2,p}_{ℓoc}(ℝ^{d+1}_{0,T})` with weak derivatives `K`, §2, p.4: `u` and `K` lie in `L^p` of
every cylinder, and `K` is the weak derivative of `u` against test functions. -/
structure IsW12pLoc (T p : ℝ) (u : ℝ → Euc d → ℝ) (K : Jet d) : Prop where
  memLp_u : ∀ R : ℝ, 0 < R → MemLp (fun z : ℝ × Euc d => u z.1 z.2) (ENNReal.ofReal p)
    (volume.restrict (closedCyl d T R))
  memLp_ut : ∀ R : ℝ, 0 < R → MemLp (fun z : ℝ × Euc d => K.ut z.1 z.2) (ENNReal.ofReal p)
    (volume.restrict (closedCyl d T R))
  memLp_Du : ∀ R : ℝ, 0 < R → ∀ i, MemLp (fun z : ℝ × Euc d => K.Du z.1 z.2 i) (ENNReal.ofReal p)
    (volume.restrict (closedCyl d T R))
  memLp_D2u : ∀ R : ℝ, 0 < R → ∀ i j,
    MemLp (fun z : ℝ × Euc d => K.D2u z.1 z.2 i j) (ENNReal.ofReal p)
      (volume.restrict (closedCyl d T R))
  weak_t : ∀ φ, IsTestFunction T φ →
    ∫ z : ℝ × Euc d, u z.1 z.2 * dtTest φ z = -∫ z : ℝ × Euc d, K.ut z.1 z.2 * φ z
  weak_x : ∀ φ, IsTestFunction T φ → ∀ i,
    ∫ z : ℝ × Euc d, u z.1 z.2 * dxTest i φ z = -∫ z : ℝ × Euc d, K.Du z.1 z.2 i * φ z
  weak_xx : ∀ φ, IsTestFunction T φ → ∀ i j,
    ∫ z : ℝ × Euc d, u z.1 z.2 * dxTest i (dxTest j φ) z = ∫ z : ℝ × Euc d, K.D2u z.1 z.2 i j * φ z

/-- `‖u‖_{W^{1,2,p}(O)} = ‖u‖_{L^p(O)} + ‖∂_t u‖_{L^p(O)} + Σ_i ‖∂_{x_i}u‖_{L^p(O)} + Σ_{ij} ‖∂_{x_i x_j}u‖_{L^p(O)}`,
§2, p.4, valued in `[0,∞]`. -/
noncomputable def w12pNorm (p : ℝ) (O : Set (ℝ × Euc d)) (u : ℝ → Euc d → ℝ) (K : Jet d) : ℝ≥0∞ :=
  eLpNorm (fun z : ℝ × Euc d => u z.1 z.2) (ENNReal.ofReal p) (volume.restrict O) +
    eLpNorm (fun z : ℝ × Euc d => K.ut z.1 z.2) (ENNReal.ofReal p) (volume.restrict O) +
    ∑ i, eLpNorm (fun z : ℝ × Euc d => K.Du z.1 z.2 i) (ENNReal.ofReal p) (volume.restrict O) +
    ∑ i, ∑ j,
      eLpNorm (fun z : ℝ × Euc d => K.D2u z.1 z.2 i j) (ENNReal.ofReal p) (volume.restrict O)

end SingularStopperVI


