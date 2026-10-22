-- Prove2me | Definitions.Def_BirkhoffGlobalSection_ConvexModelDynamics
-- name    : BirkhoffGlobalSection_ConvexModelDynamics
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-27T01:49:27.937029+00:00
-- url     : https://prove2.me/theorems/264b7dde-5485-4fed-a4e6-553d4c3a5cfa
-- title:
--   Convex-model Hamiltonian dynamics, complete clocks, and rational pages
-- statement:
--   Let $M$ be a convex regularization model with coordinate map $F$, inverse $G$, model Hamiltonian $H$, convex body $B$, and positive regularized clock factor $\tau$. Its model state space is $\partial B$. The coordinate maps induce a homeomorphism between the Levi-Civita component and this state space.
--
--   For a complete Levi-Civita flow $\varphi$, model dynamics consist of a complete Hamiltonian flow $\psi$ on $\partial B$ and, for each initial state $s$, an increasing order isomorphism $C_s:\mathbb R\to\mathbb R$ satisfying
--
--   $$
--   C_s(0)=0,\qquad C_s'(t)=\tau(\varphi_t(s)),\qquad
--   \psi_{C_s(t)}(F(s))=F(\varphi_t(s)).
--   $$
--
--   A model rational page for a periodic LC orbit $\gamma$ is a smooth immersed disk $p:D^2\to\partial B$, injective on the closed disk, transverse to $X_H$ in its interior, with boundary $F(\gamma)$. Its only antipodal identifications are opposite boundary parameters:
--
--   $$
--   p(u)=-p(v)\quad\Longleftrightarrow\quad u,v\in S^1\ \text{and}\ v=-u.
--   $$
--
--   Every model trajectory outside the binding meets the open disk or its antipode at arbitrarily large positive and negative model times.
--
--   These interfaces separate complete time reparametrization, contact-topological page construction in the convex model, and smooth pullback to the original coordinates. The dynamics data contain no page assertion; the model page contains no inverse-coordinate derivative or LC return assertion.
--
--   **Formalization Note.** The page is represented by an ambient map from the plane, smooth at each point of the closed disk. Order-isomorphism clocks express both strict time orientation and completeness.
-- source:
--   Transport interfaces for Liu--Salomao, https://arxiv.org/html/2506.17867v2, Section 4 and Theorem 1.16(ii)/Section 10; rational disk pages as in Hryniewicz--Salomao, https://arxiv.org/html/1505.02713v3, Section 1.2 (rational disks and rational open books) and Corollary 1.8. These explicit model-clock and smooth lifted-page interfaces are introduced for the Prove2Me coordinate-transport proof, not quoted definitions from those papers.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
import Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage

namespace BirkhoffGlobalSection

open scoped ContDiff

abbrev ConvexModelState {μ c : ℝ} (M : ConvexRegularizationModel μ c) :=
  {y : Phase // y ∈ frontier M.body}

/-- The point correspondence induced by the regularization coordinates. -/
def ConvexRegularizationModel.mapState {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) (s : LeftEnergyState μ c) :
    ConvexModelState M :=
  ⟨M.toModel s, by rw [← M.image_frontier]; exact ⟨s, s.property, rfl⟩⟩

/-- The regularization coordinate maps give the corresponding state-space
homeomorphism; smoothness and the inverse identities are supplied by the model. -/
def ConvexRegularizationModel.stateHomeomorph {μ c : ℝ}
    (M : ConvexRegularizationModel μ c) :
    LeftEnergyState μ c ≃ₜ ConvexModelState M where
  toFun := M.mapState
  invFun := fun y => ⟨M.fromModel y, by
    have hy : (y : Phase) ∈ M.toModel '' leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact y.property
    obtain ⟨s, hs, hsy⟩ := hy
    rw [← hsy, M.left_inverse s (M.contains_component hs)]
    exact hs⟩
  left_inv := by
    intro s
    apply Subtype.ext
    exact M.left_inverse s (M.contains_component s.property)
  right_inv := by
    intro y
    apply Subtype.ext
    apply M.right_inverse
    have hy : (y : Phase) ∈ M.toModel '' leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact y.property
    obtain ⟨s, hs, hsy⟩ := hy
    rw [← hsy]
    exact M.toModel_mapsTo (M.contains_component hs)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact M.toModel_smooth.continuousOn.comp_continuous continuous_subtype_val
      (fun s => M.contains_component s.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply M.fromModel_smooth.continuousOn.comp_continuous continuous_subtype_val
    intro y
    have hy : (y : Phase) ∈ M.toModel '' leftEnergyComponent μ c := by
      rw [M.image_frontier]
      exact y.property
    obtain ⟨s, hs, hsy⟩ := hy
    rw [← hsy]
    exact M.toModel_mapsTo (M.contains_component hs)

/-- A complete model Hamiltonian flow with an orientation-preserving change
of the time variable on each trajectory. The clock derivative is the positive
regularization factor, including at collision points. -/
structure ConvexModelDynamics {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c)) where
  flow : Flow ℝ (ConvexModelState M)
  hamiltonian : ∀ y : ConvexModelState M,
    HasDerivAt (fun t : ℝ => ((flow t y : ConvexModelState M) : Phase))
      (hamiltonianVectorField M.modelHamiltonian (y : Phase)) 0
  clock : LeftEnergyState μ c → (ℝ ≃o ℝ)
  clock_zero : ∀ s, clock s 0 = 0
  clock_deriv : ∀ s t,
    HasDerivAt (clock s) (M.timeScale ((φ t s : LeftEnergyState μ c) : Phase)) t
  conjugacy : ∀ s t,
    ((flow (clock s t) (M.mapState s) : ConvexModelState M) : Phase) =
      M.toModel ((φ t s : LeftEnergyState μ c) : Phase)

/-- A rational two-disk page in the convex model, before applying the inverse
regularization. Returns use model Hamiltonian time. No LC page or derivative
of the inverse coordinate map is part of these data. -/
structure ConvexModelRationalPage {μ c : ℝ} (M : ConvexRegularizationModel μ c)
    {φ : Flow ℝ (LeftEnergyState μ c)} (D : ConvexModelDynamics M φ)
    (γ : PeriodicOrbit φ) where
  page : Plane → Phase
  mapsTo : ∀ u ∈ closedUnitDisk, page u ∈ frontier M.body
  smooth : ∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ page u
  injective : Set.InjOn page closedUnitDisk
  immersion : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ page u)
  transverse : ∀ u ∈ openUnitDisk,
    hamiltonianVectorField M.modelHamiltonian (page u) ∉
      Set.range (fderiv ℝ page u)
  boundary : page '' unitCircle = M.toModel '' orbitSet γ
  antipodal_fibers : ∀ u ∈ closedUnitDisk, ∀ v ∈ closedUnitDisk,
    (page u = -page v ↔ u ∈ unitCircle ∧ v ∈ unitCircle ∧ v = -u)
  returns : ∀ y : ConvexModelState M, (y : Phase) ∉ M.toModel '' orbitSet γ →
    (∀ R : ℝ, ∃ t : ℝ, R < t ∧ ∃ u ∈ openUnitDisk,
      ((D.flow t y : ConvexModelState M) : Phase) = page u ∨
      ((D.flow t y : ConvexModelState M) : Phase) = -page u) ∧
    (∀ R : ℝ, ∃ t : ℝ, t < R ∧ ∃ u ∈ openUnitDisk,
      ((D.flow t y : ConvexModelState M) : Phase) = page u ∨
      ((D.flow t y : ConvexModelState M) : Phase) = -page u)

end BirkhoffGlobalSection


