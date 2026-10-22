-- Prove2me | Definitions.Def_BirkhoffGlobalSection_TransverseHopf
-- name    : BirkhoffGlobalSection_TransverseHopf
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-27T02:08:58.631944+00:00
-- url     : https://prove2.me/theorems/9efb13ba-5661-4a71-b3b5-3e6d4e6ca52a
-- title:
--   Equivariant transverse Hopf isotopies and model periodic orbits
-- statement:
--   In coordinates $(q_1,q_2,p_1,p_2)$, define the radial contact form and Euclidean radial normalization by
--
--   $$
--   \alpha_y(v)=-\tfrac12\omega_0(y,v),\qquad N(y)=\frac{y}{\sqrt{|q|^2+|p|^2}}.
--   $$
--
--   The sign of $\alpha$ is compatible with the Hamiltonian convention $X_H=(H_p,-H_q)$. The positive standard Hopf circle is parametrized by
--
--   $$
--   h(u_0,u_1)=(u_0,0,-u_1,0),\qquad (u_0,u_1)\in S^1.
--   $$
--
--   An equivariant transverse Hopf isotopy to a set $K\subset S^3$ is a smooth family $k_t:S^1\to S^3$, for $0\le t\le1$, of injective circle maps satisfying
--
--   $$
--   k_0=h,\qquad k_1(S^1)=K,\qquad k_t(-u)=-k_t(u),\qquad
--   \alpha_{k_t(u)}\bigl(Dk_t(u)(-u_1,u_0)\bigr)>0.
--   $$
--
--   The ambient map is smooth near the closed parameter cylinder. Positivity supplies immersion along the circle. The certificate records a transverse knot class; it contains no spanning disk, page, or global return assertion.
--
--   The file also records the geometric trace of a model periodic orbit and the closed orbit obtained by transporting an LC orbit through its increasing complete clock. Its period is the clock applied to the original period. A half-period antipodal relation is deliberately not asserted for the model Hamiltonian time.
--
--   **Formalization Note.** Radial normalization is totalized at zero; applying the geometric interpretation on a convex boundary requires its nonzero-point property. The isotopy itself takes values in the unit sphere.
-- source:
--   Coordinate realization of the transverse Hopf-fiber condition in Liu--Salomao, https://arxiv.org/html/2506.17867v2, Theorem 1.16(ii). The standard radial contact form and Hopf links are described in Hryniewicz--Salomao, https://arxiv.org/html/1505.02713v3, Section 1.2, equation (3) and the paragraph after Corollary 1.8. The sign here accounts explicitly for phase coordinates (q,p) and X_H=(H_p,-H_q). Orbit-clock constructors are elementary consequences of the published ConvexModelDynamics interface.

import Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- The radial contact form with the sign compatible with the workspace's
Hamiltonian field `(H_p,-H_q)`: it evaluates positively on an outward radial
Hamiltonian such as one half the squared radius. -/
noncomputable def phaseRadialContact (y v : Phase) : ℝ :=
  -(phaseSymplecticForm y v) / 2

noncomputable def radialNormalize (y : Phase) : Phase :=
  (Real.sqrt (zNormSq y + wNormSq y))⁻¹ • y

/-- Counterclockwise tangent vector on the parameter circle. -/
def circleTangent (u : Plane) : Plane := ![-u 1, u 0]

/-- A positively transverse Hopf circle for `phaseRadialContact`. -/
def standardHopfCircle (u : Plane) : Phase := ![u 0, 0, -u 1, 0]

/-- An explicit equivariant transverse isotopy from the positive standard
Hopf circle to a specified subset of the round three-sphere. It records knot
type only: no spanning disk, flow transversality, or return clause is assumed. -/
structure EquivariantTransverseHopfIsotopy (K : Set Phase) where
  isotopy : ℝ × Plane → Phase
  smooth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
    ContDiffAt ℝ ∞ isotopy (t, u)
  sphere : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
    isotopy (t, u) ∈ unitThreeSphere
  injective : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Set.InjOn (fun u => isotopy (t, u)) unitCircle
  antipodal : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
    isotopy (t, -u) = -isotopy (t, u)
  positive : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ unitCircle,
    0 < phaseRadialContact (isotopy (t, u))
      (fderiv ℝ (fun v => isotopy (t, v)) u (circleTangent u))
  start : ∀ u ∈ unitCircle, isotopy (0, u) = standardHopfCircle u
  finish : (fun u => isotopy (1, u)) '' unitCircle = K

/-- The geometric trace of an orbit of a convex model flow. -/
def convexModelOrbitSet {μ c : ℝ} {M : ConvexRegularizationModel μ c}
    {ψ : Flow ℝ (ConvexModelState M)} (Γ : PeriodicOrbit ψ) : Set Phase :=
  Set.range (fun t : ℝ => ((ψ t Γ.point : ConvexModelState M) : Phase))

/-- Transport a closed orbit by its complete regularization clock. Its model
period need not have an antipodal return at half that period. -/
def ConvexModelDynamics.mapPeriodicOrbit {μ c : ℝ}
    {M : ConvexRegularizationModel μ c} {φ : Flow ℝ (LeftEnergyState μ c)}
    (D : ConvexModelDynamics M φ) (γ : PeriodicOrbit φ) : PeriodicOrbit D.flow where
  point := M.mapState γ.point
  period := D.clock γ.point γ.period
  period_pos := by
    have h := (D.clock γ.point).strictMono γ.period_pos
    simpa only [D.clock_zero] using h
  closed := by
    apply Subtype.ext
    change ((D.flow (D.clock γ.point γ.period) (M.mapState γ.point) :
      ConvexModelState M) : Phase) = M.toModel (γ.point : Phase)
    rw [D.conjugacy, γ.closed]

end BirkhoffGlobalSection


