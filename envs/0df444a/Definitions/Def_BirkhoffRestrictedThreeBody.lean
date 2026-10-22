-- Prove2me | Definitions.Def_BirkhoffRestrictedThreeBody
-- name    : BirkhoffRestrictedThreeBody
-- status  : Definition
-- author  : @Yivy Yu
-- created : 2026-09-10T02:26:56.85077+00:00
-- url     : https://prove2.me/theorems/d552c0e5-6185-4a08-966f-a8d579d6abad
-- title:
--   Levi-Civita model and disk-like global sections
-- statement:
--   This definition module fixes a Lean model for the planar circular restricted three-body problem and for Birkhoff's global-section conjecture.
--
--   For a mass ratio $\mu$, the rotating Jacobi Hamiltonian on phase coordinates $(q_1,q_2,p_1,p_2)\in\mathbb R^4$ is
--
--   $$
--   H_\mu=\frac{p_1^2+p_2^2}{2}+q_1p_2-q_2p_1
--   -\frac{1-\mu}{\sqrt{(q_1+\mu)^2+q_2^2}}
--   -\frac{\mu}{\sqrt{(q_1-1+\mu)^2+q_2^2}}.
--   $$
--
--   The module defines collision-free states, the canonical Hamiltonian vector field, collision-free critical points, and the first critical value as the infimum of their Hamiltonian values. The source's subcritical condition is represented as $-c<h_1(\mu)$.
--
--   After Levi-Civita regularization, phase coordinates are read as $(z_1,z_2,w_1,w_2)$. Writing $|z|^2=z_1^2+z_2^2$, $|w|^2=w_1^2+w_2^2$, and
--
--   $$D(z)=\bigl(2(z_1^2-z_2^2)-1\bigr)^2+(4z_1z_2)^2,$$
--
--   the regularized Hamiltonian is
--
--   $$
--   K_{\mu,c}=\frac{|w|^2}{2}+c|z|^2-\frac{1-\mu}{2}
--   +2|z|^2(z_1w_2-z_2w_1)-\mu(z_1w_2+z_2w_1)
--   -\frac{\mu|z|^2}{\sqrt{D(z)}}.
--   $$
--
--   The distinguished energy component is the connected component of $\{K_{\mu,c}=0,\ D>0\}$ containing $(0,0,\sqrt{1-\mu},0)$. The condition $D>0$ removes the remaining, unregularized collision.
--
--   The module also defines continuous Hamiltonian flows on this component, positive-period orbit data, orbit sets, and a disk-like global surface of section. Such a section is a smooth embedded unit disk whose boundary image is the periodic orbit, whose interior has locally isolated intersections with the flow, and which every nonbinding trajectory meets at both a positive and a negative time. Finally, strict convexity of an energy level is represented by positivity of the tangential Hessian in every nonzero direction annihilated by the first derivative.
--
--   **Formalization Note.** `Phase` is `Fin 4 → ℝ` and the parameter plane is `Fin 2 → ℝ`. Fréchet derivatives are used throughout. The flow and global-section predicates make the dynamical quantifiers explicit rather than treating “global surface of section” as an opaque assertion.
--
--   **Correction notice.** The original `DiskLikeGlobalSurfaceOfSection` predicate in this module accidentally requests analytic regularity and omits pointwise transversality. The Hamiltonian, regularization, component, and convexity definitions remain valid and are retained for the published milestone theorems. For Birkhoff's conjecture, use `DiskLikeGlobalSurfaceOfSectionV2` from `Definitions.Def_BirkhoffRestrictedThreeBodyGlobalSection`.
-- source:
--   Joung--van Koert, Computational symplectic topology and symmetric orbits in the restricted three-body problem, https://arxiv.org/abs/2407.19159, p. 2 Eq. (1.1), p. 5 Section 2.1, p. 6 Eq. (2.2), and pp. 1--3 (global sections); Hryniewicz, https://arxiv.org/abs/0812.4076.

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Connected.Basic

namespace BirkhoffRestrictedThreeBody

noncomputable section

/-- Four real coordinates, ordered as `(q₁,q₂,p₁,p₂)` for the Jacobi Hamiltonian
and as `(z₁,z₂,w₁,w₂)` after Levi-Civita regularization. -/
abbrev Phase := Fin 4 → ℝ

/-- Two real coordinates, used for the parameter disk of a global section. -/
abbrev Plane := Fin 2 → ℝ

def qNormSq (s : Phase) : ℝ := s 0 ^ 2 + s 1 ^ 2

def zNormSq (s : Phase) : ℝ := s 0 ^ 2 + s 1 ^ 2

def wNormSq (s : Phase) : ℝ := s 2 ^ 2 + s 3 ^ 2

/-- Equation (1.1) of Joung--van Koert for the planar circular restricted
three-body problem in rotating coordinates. -/
def jacobiHamiltonian (μ : ℝ) (s : Phase) : ℝ :=
  (s 2 ^ 2 + s 3 ^ 2) / 2 + s 0 * s 3 - s 1 * s 2
    - (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
    - μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)

def collisionFree (μ : ℝ) (s : Phase) : Prop :=
  0 < (s 0 + μ) ^ 2 + s 1 ^ 2 ∧
  0 < (s 0 - 1 + μ) ^ 2 + s 1 ^ 2

def coordinateVector (i : Fin 4) : Phase :=
  fun j => if j = i then 1 else 0

def partialDerivative (F : Phase → ℝ) (s : Phase) (i : Fin 4) : ℝ :=
  fderiv ℝ F s (coordinateVector i)

/-- The canonical Hamiltonian vector field `(∂H/∂p, -∂H/∂q)`. -/
def hamiltonianVectorField (F : Phase → ℝ) (s : Phase) : Phase :=
  ![partialDerivative F s 2, partialDerivative F s 3,
    -partialDerivative F s 0, -partialDerivative F s 1]

def isCriticalPoint (F : Phase → ℝ) (s : Phase) : Prop :=
  fderiv ℝ F s = 0

/-- The smallest critical value of the collision-free Jacobi Hamiltonian.
This is `H(L₁)` in the source's energy convention. -/
def firstCriticalValue (μ : ℝ) : ℝ :=
  sInf {e : ℝ | ∃ s : Phase,
    collisionFree μ s ∧ isCriticalPoint (jacobiHamiltonian μ) s ∧
      jacobiHamiltonian μ s = e}

/-- The source writes a Jacobi energy level as `H = -c`; being below the first
critical value therefore means `-c < H(L₁)`. -/
def belowFirstCriticalValue (μ c : ℝ) : Prop :=
  -c < firstCriticalValue μ

/-- Squared distance to the second collision after the complex squaring map. -/
def secondCollisionDistanceSq (s : Phase) : ℝ :=
  (2 * (s 0 ^ 2 - s 1 ^ 2) - 1) ^ 2 + (4 * s 0 * s 1) ^ 2

/-- Equation (2.2) of Joung--van Koert. -/
def leviCivitaHamiltonian (μ c : ℝ) (s : Phase) : ℝ :=
  wNormSq s / 2 + c * zNormSq s - (1 - μ) / 2
    + 2 * zNormSq s * (s 0 * s 3 - s 1 * s 2)
    - μ * (s 0 * s 3 + s 1 * s 2)
    - μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)

/-- A canonical point over collision with the primary at `q=(-μ,0)`. -/
def leftCollisionPoint (μ : ℝ) : Phase :=
  ![0, 0, Real.sqrt (1 - μ), 0]

def regularEnergyLocus (μ c : ℝ) : Set Phase :=
  {s | leviCivitaHamiltonian μ c s = 0 ∧ 0 < secondCollisionDistanceSq s}

/-- The regularized energy component corresponding to the primary at `q=(-μ,0)`. -/
def leftEnergyComponent (μ c : ℝ) : Set Phase :=
  connectedComponentIn (regularEnergyLocus μ c) (leftCollisionPoint μ)

abbrev LeftEnergyState (μ c : ℝ) := {s : Phase // s ∈ leftEnergyComponent μ c}

/-- A continuous flow on the left regularized energy component whose time derivative
is the Hamiltonian vector field of the Levi-Civita Hamiltonian. -/
def IsLeviCivitaHamiltonianFlow (μ c : ℝ)
    (φ : Flow ℝ (LeftEnergyState μ c)) : Prop :=
  ∀ s : LeftEnergyState μ c,
    HasDerivAt (fun t : ℝ => ((φ t s : LeftEnergyState μ c) : Phase))
      (hamiltonianVectorField (leviCivitaHamiltonian μ c) (s : Phase)) 0

structure PeriodicOrbit {X : Type*} [TopologicalSpace X]
    (φ : Flow ℝ X) where
  point : X
  period : ℝ
  period_pos : 0 < period
  closed : φ period point = point

def orbitSet {μ c : ℝ} {φ : Flow ℝ (LeftEnergyState μ c)}
    (γ : PeriodicOrbit φ) : Set Phase :=
  Set.range (fun t : ℝ => ((φ t γ.point : LeftEnergyState μ c) : Phase))

def planeNormSq (u : Plane) : ℝ := u 0 ^ 2 + u 1 ^ 2

def closedUnitDisk : Set Plane := {u | planeNormSq u ≤ 1}

def openUnitDisk : Set Plane := {u | planeNormSq u < 1}

def unitCircle : Set Plane := {u | planeNormSq u = 1}

/-- A smooth embedded disk whose boundary is a periodic orbit, whose interior is a
local cross-section, and which every other trajectory meets in both time directions. -/
def DiskLikeGlobalSurfaceOfSection {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c)) (γ : PeriodicOrbit φ) : Prop :=
  ∃ page : Plane → Phase,
    ContDiffOn ℝ ⊤ page closedUnitDisk ∧
    (∀ u ∈ closedUnitDisk, page u ∈ leftEnergyComponent μ c) ∧
    Set.InjOn page closedUnitDisk ∧
    (∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ page u)) ∧
    page '' unitCircle = orbitSet γ ∧
    (∀ s : LeftEnergyState μ c,
      (s : Phase) ∈ page '' openUnitDisk →
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
        ((φ t s : LeftEnergyState μ c) : Phase) ∈ page '' openUnitDisk → t = 0) ∧
    (∀ s : LeftEnergyState μ c, (s : Phase) ∉ orbitSet γ →
      (∃ t : ℝ, 0 < t ∧
        ((φ t s : LeftEnergyState μ c) : Phase) ∈ page '' openUnitDisk) ∧
      (∃ t : ℝ, t < 0 ∧
        ((φ t s : LeftEnergyState μ c) : Phase) ∈ page '' openUnitDisk))

/-- Positive tangential Hessian on a regular level hypersurface. -/
def IsStrictlyConvexLevel (F : Phase → ℝ) (S : Set Phase) : Prop :=
  ∀ s ∈ S, ∀ v : Phase, v ≠ 0 → fderiv ℝ F s v = 0 →
    0 < fderiv ℝ (fun x => fderiv ℝ F x v) s v

end

end BirkhoffRestrictedThreeBody


