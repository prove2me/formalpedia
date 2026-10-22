-- Prove2me | Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel
-- name    : BirkhoffGlobalSection_ConvexRegularizationModel
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-27T01:34:50.445392+00:00
-- url     : https://prove2.me/theorems/516d7a75-137b-4e4f-b32f-c910954c30a9
-- title:
--   Smooth symplectic convex regularization with a positive clock
-- statement:
--   Let $\Sigma_{\mu,c}$ be the selected Levi-Civita energy component. A convex regularization model consists of smooth inverse maps $F:U\to V$ and $G:V\to U$ on open neighborhoods, a compact convex body $B\subset\mathbb R^4$ containing the origin in its interior, a smooth model Hamiltonian $H$ on $V$, and a continuous positive regularized clock $\tau$ along $\Sigma_{\mu,c}$.
--
--   The maps and vector fields satisfy
--
--   $$
--   \Sigma_{\mu,c}\subset U,\qquad F(\Sigma_{\mu,c})=\partial B,\qquad F(-s)=-F(s),
--   $$
--
--   $$
--   \omega_0(DF_s v,DF_s w)=\kappa\,\omega_0(v,w),\qquad \kappa>0,
--   $$
--
--   $$
--   DF_s X_{K_{\mu,c}}(s)=\tau(s)X_H(F(s)),\qquad \tau(s)>0.
--   $$
--
--   The symplectic identity holds on $U$; the antipodal identity and vector-field relation hold on $\Sigma_{\mu,c}$. On $\partial B$, the Hamiltonian vanishes, its differential is nonzero, and its tangential Hessian is positive definite. Thus the geometric convexity and its differential strengthening are both part of the data.
--
--   This interface separates local convex regularization from the contact-topological construction of pages. The time factor compares two regularized systems and must remain positive at collisions. No orbit, spanning disk, page, or return property is assumed. Neither global smooth coordinate maps on all of phase space nor evenness of $H$ is required.
--
--   **Formalization Note.** Maps are total functions smooth on the specified open sets. The standard symplectic form uses coordinate order $(q_1,q_2,p_1,p_2)$; the positive constant permits different regularization normalizations.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2, Section 4 (elliptic-hyperbolic regularization), Theorem 1.12, and Section 10 (local persistence of convexity). This is an explicit transport interface for the Prove2Me Levi-Civita model, rather than a definition quoted verbatim from the paper.

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- The standard symplectic form in the coordinate order `(q₁,q₂,p₁,p₂)`. -/
def phaseSymplecticForm (v w : Phase) : ℝ :=
  v 0 * w 2 - v 2 * w 0 + v 1 * w 3 - v 3 * w 1

/-- A convex Hamiltonian realization of the selected Levi-Civita component.

The coordinate maps are smooth inverses on open neighborhoods and preserve the
symplectic form up to a positive constant, allowing different normalizations of
regularized coordinates. The model surface bounds a compact convex body and
has positive tangential Hessian. The vector-field relation records the positive
regularized-to-regularized time change, including at collision points.

This is geometric transport data only: no periodic orbit, page, or return
property is a field of this structure. Existence near equal mass and the
retrograde binding criterion are separate theorem obligations. -/
structure ConvexRegularizationModel (μ c : ℝ) where
  source : Set Phase
  target : Set Phase
  source_open : IsOpen source
  target_open : IsOpen target
  contains_component : leftEnergyComponent μ c ⊆ source
  toModel : Phase → Phase
  fromModel : Phase → Phase
  toModel_mapsTo : Set.MapsTo toModel source target
  fromModel_mapsTo : Set.MapsTo fromModel target source
  left_inverse : ∀ s ∈ source, fromModel (toModel s) = s
  right_inverse : ∀ y ∈ target, toModel (fromModel y) = y
  toModel_smooth : ContDiffOn ℝ ∞ toModel source
  fromModel_smooth : ContDiffOn ℝ ∞ fromModel target
  symplecticScale : ℝ
  symplecticScale_pos : 0 < symplecticScale
  symplectic : ∀ s ∈ source, ∀ v w : Phase,
    phaseSymplecticForm (fderiv ℝ toModel s v) (fderiv ℝ toModel s w) =
      symplecticScale * phaseSymplecticForm v w
  antipodal : ∀ s ∈ leftEnergyComponent μ c, toModel (-s) = -toModel s
  body : Set Phase
  body_compact : IsCompact body
  body_convex : Convex ℝ body
  origin_interior : (0 : Phase) ∈ interior body
  image_frontier : toModel '' leftEnergyComponent μ c = frontier body
  modelHamiltonian : Phase → ℝ
  model_smooth : ContDiffOn ℝ ∞ modelHamiltonian target
  model_zero : ∀ y ∈ frontier body, modelHamiltonian y = 0
  model_regular : ∀ y ∈ frontier body, fderiv ℝ modelHamiltonian y ≠ 0
  model_hessian : HasPositiveTangentialHessianOn modelHamiltonian (frontier body)
  timeScale : Phase → ℝ
  timeScale_continuous : ContinuousOn timeScale source
  timeScale_pos : ∀ s ∈ leftEnergyComponent μ c, 0 < timeScale s
  vectorField : ∀ s ∈ leftEnergyComponent μ c,
    fderiv ℝ toModel s (hamiltonianVectorField (leviCivitaHamiltonian μ c) s) =
      timeScale s • hamiltonianVectorField modelHamiltonian (toModel s)

end BirkhoffGlobalSection


