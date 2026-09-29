-- Prove2me | Definitions.Def_HilbertSixth_Geometry
-- name    : HilbertSixth_Geometry
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T03:31:27.309822+00:00
-- url     : https://prove2.me/theorems/7f964dc8-6f49-46e1-bc0c-805b039db873
-- title:
--   Torus geometry and differential operators for the hard-sphere model
-- statement:
--   Ambient conventions for the derivation of fluid equations from hard-sphere dynamics.
--
--   Velocities and positions live in $\mathbb{R}^d$ with its Euclidean structure. The torus $\mathbb{T}^d = \mathbb{R}^d/\mathbb{Z}^d$ is represented through representatives in $\mathbb{R}^d$: the quotient distance is
--
--   $$|x-y|_{\mathbb{T}} \;=\; \min_{k \in \mathbb{Z}^d} |x - y - k|,$$
--
--   computed by rounding each coordinate of $x-y$ to the nearest integer, and positions are integrated over the fundamental domain $[0,1)^d$; functions on the torus are functions on $\mathbb{R}^d$ that are $\mathbb{Z}^d$-periodic. The whole-space model of arXiv:2408.07818 is recovered by replacing the quotient distance with the Euclidean one and the fundamental domain with all of $\mathbb{R}^d$.
--
--   An $N$-particle configuration is a family $z_N = (x_j, v_j)_{j < N}$ of positions and velocities; the non-overlapping domain is $\mathcal{D}_N = \{z_N : \operatorname{sep}(x_i, x_j) \ge \varepsilon \text{ for } i \ne j\}$, where $\operatorname{sep}$ is the chosen separation function. The file also fixes the elementary differential operators used for the fluid equations — partial derivative, gradient, Laplacian, divergence and advection, all defined as derivatives along straight lines — and the Japanese bracket $\langle v\rangle = (1+|v|^2)^{1/2}$.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, Section 1.2.1, Definition 1.1; Deng--Hani--Ma, Long time derivation of the Boltzmann equation from hard sphere dynamics, https://arxiv.org/abs/2408.07818, Section 1.1.1

import Mathlib

/-!
# Geometry and calculus conventions for the hard-sphere / Boltzmann / fluid setting

This file fixes the ambient spaces and the elementary differential operators used to
formalize Deng–Hani–Ma, *Hilbert's sixth problem: derivation of fluid equations via
Boltzmann's kinetic theory* (arXiv:2503.01800), and its companion
arXiv:2408.07818.

Positions are always described by representatives in `ℝ^d`.  The periodic setting
(the torus `T^d = ℝ^d / ℤ^d` of the paper) is encoded by

* measuring distances between particle centres with `torusDist`, the quotient
  distance `|x - y|_T = min {|x - y - k| : k ∈ ℤ^d}`, and
* integrating positions over the fundamental domain `box d = [0,1)^d`, and
  requiring the relevant densities to be `ℤ^d`-periodic.

The whole-space setting of arXiv:2408.07818 is obtained from the very same
definitions by using `euclSep` instead of `torusDist` and `Set.univ` instead of
`box d`.
-/

open MeasureTheory

namespace HilbertSixth

/-- `Vec d` is `ℝ^d` carrying its Euclidean inner product structure. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The vector of `ℝ^d` with the prescribed coordinates. -/
noncomputable def vecOf {d : ℕ} (f : Fin d → ℝ) : Vec d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm f

/-- The `i`-th standard basis vector of `ℝ^d`. -/
noncomputable def basisVec {d : ℕ} (i : Fin d) : Vec d := EuclideanSpace.single i (1 : ℝ)

/-- The Euclidean inner product `v · w = ∑ i, v i * w i` on `ℝ^d`. -/
def dotp {d : ℕ} (v w : Vec d) : ℝ := ∑ i, v i * w i

/-- `repVec x` is the representative of `x` modulo `ℤ^d` whose coordinates all lie in
`[-1/2, 1/2]`; it realises the minimum in the definition of `torusDist`. -/
noncomputable def repVec {d : ℕ} (x : Vec d) : Vec d :=
  vecOf (fun i => x i - (round (x i) : ℝ))

/-- The distance `|x - y|_T` on the torus `T^d = ℝ^d / ℤ^d`, computed on representatives:
the Euclidean length of the shortest representative of `x - y` modulo `ℤ^d`. -/
noncomputable def torusDist {d : ℕ} (x y : Vec d) : ℝ := ‖repVec (x - y)‖

/-- The plain Euclidean distance on `ℝ^d`, used for the whole-space model. -/
noncomputable def euclSep {d : ℕ} (x y : Vec d) : ℝ := ‖x - y‖

/-- The fundamental domain `[0,1)^d` of `T^d = ℝ^d / ℤ^d`. -/
def box (d : ℕ) : Set (Vec d) := {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

/-- `ℤ^d`-periodicity of a scalar function of the position variable. -/
def PeriodicPos {d : ℕ} (f : Vec d → ℝ) : Prop :=
  ∀ (k : Fin d → ℤ) (x : Vec d), f (x + vecOf (fun i => (k i : ℝ))) = f x

/-- `ℤ^d`-periodicity in the position variable of a function of position and velocity. -/
def PeriodicPos₂ {d : ℕ} (f : Vec d → Vec d → ℝ) : Prop :=
  ∀ v : Vec d, PeriodicPos (fun x => f x v)

/-- The one-particle state space: a position and a velocity. -/
abbrev Phase (d : ℕ) := Vec d × Vec d

/-- The state vector `z_N = (z_1, …, z_N)` of an `N`-particle configuration. -/
abbrev Config (d N : ℕ) := Fin N → Phase d

/-- The set of one-particle states whose position lies in `R`. -/
def phaseRegion {d : ℕ} (R : Set (Vec d)) : Set (Phase d) := {z | z.1 ∈ R}

/-- The set of `N`-particle configurations all of whose positions lie in `R`. -/
def region {d : ℕ} (R : Set (Vec d)) (N : ℕ) : Set (Config d N) := {z | ∀ j, (z j).1 ∈ R}

/-- The non-overlapping domain
`D_N = {z_N : sep (x_i) (x_j) ≥ ε for all i ≠ j}`,
where `sep` is the separation used for the particle centres (`torusDist` in the
periodic model, `euclSep` in the whole-space model). -/
def domain {d : ℕ} (sep : Vec d → Vec d → ℝ) (N : ℕ) (ε : ℝ) : Set (Config d N) :=
  {z | ∀ i j, i ≠ j → ε ≤ sep (z i).1 (z j).1}

/-- The indicator function `1_{D_N}` of the non-overlapping domain. -/
noncomputable def domainIndicator {d : ℕ} (sep : Vec d → Vec d → ℝ) (N : ℕ) (ε : ℝ)
    (z : Config d N) : ℝ :=
  (domain sep N ε).indicator (fun _ => (1 : ℝ)) z

/-- The partial derivative `∂_i f` of a scalar function on `ℝ^d`. -/
noncomputable def partialD {d : ℕ} (f : Vec d → ℝ) (i : Fin d) (x : Vec d) : ℝ :=
  deriv (fun s : ℝ => f (x + s • basisVec i)) 0

/-- The gradient `∇ f` of a scalar function on `ℝ^d`. -/
noncomputable def gradVec {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  vecOf (fun i => partialD f i x)

/-- The Laplacian `Δ f = ∑ i, ∂_i^2 f`. -/
noncomputable def laplacian {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, iteratedDeriv 2 (fun s : ℝ => f (x + s • basisVec i)) 0

/-- The divergence `div u = ∑ i, ∂_i u_i` of a vector field on `ℝ^d`. -/
noncomputable def divergence {d : ℕ} (u : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∑ i, partialD (fun y => u y i) i x

/-- The advection term `(u · ∇) f` of a scalar `f` along a vector field `u`. -/
noncomputable def advect {d : ℕ} (u : Vec d → Vec d) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, u x i * partialD f i x

/-- The Japanese bracket `⟨v⟩ = (1 + |v|²)^{1/2}`. -/
noncomputable def jbracket {d : ℕ} (v : Vec d) : ℝ := Real.sqrt (1 + ‖v‖ ^ 2)

end HilbertSixth


