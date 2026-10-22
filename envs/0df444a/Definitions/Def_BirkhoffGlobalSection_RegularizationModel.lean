-- Prove2me | Definitions.Def_BirkhoffGlobalSection_RegularizationModel
-- name    : BirkhoffGlobalSection_RegularizationModel
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-28T03:05:25.300089+00:00
-- url     : https://prove2.me/theorems/6fdae80c-2cc7-488a-8cf6-a40476cde680
-- title:
--   Regularization models and strictly convex star-shaped points
-- statement:
--   Regularization models of the selected Levi-Civita component, and strictly convex star-shaped points of a level set.
--
--   Let $\Sigma_{\mu,c}\subset\mathbb{R}^4$ be the selected Levi-Civita component, with Levi-Civita Hamiltonian $K_{\mu,c}$ and Hamiltonian vector field $X_{K_{\mu,c}}$. A **regularization model** of $\Sigma_{\mu,c}$ consists of the following data.
--
--   1. Open sets $V\supset\Sigma_{\mu,c}$ and $W$ in $\mathbb{R}^4$, and mutually inverse smooth maps $\Phi:V\to W$ and $\Phi^{-1}:W\to V$.
--   2. A constant $\kappa>0$ with $\omega_0(d\Phi_s v,d\Phi_s w)=\kappa\,\omega_0(v,w)$ for all $s\in V$, where $\omega_0=\sum_i dq_i\wedge dp_i$.
--   3. Antipodal equivariance on the component: $\Phi(-s)=-\Phi(s)$ for $s\in\Sigma_{\mu,c}$.
--   4. A smooth model Hamiltonian $G$ on $W$ with $G(\Phi(s))=0$ and $dG_{\Phi(s)}\neq0$ for $s\in\Sigma_{\mu,c}$.
--   5. A continuous function $\lambda$ on $V$, positive on $\Sigma_{\mu,c}$, with
--
--   $$
--   d\Phi_s\big(X_{K_{\mu,c}}(s)\big)=\lambda(s)\,X_G\big(\Phi(s)\big)\qquad(s\in\Sigma_{\mu,c}).
--   $$
--
--   So $\Phi$ carries the Levi-Civita flow on $\Sigma_{\mu,c}$ to the model flow on $\Phi(\Sigma_{\mu,c})$ up to a positive change of time. These are the fields of `ConvexRegularizationModel` without the convex body. The notion covers other regularizations of the same component, such as the elliptic-hyperbolic coordinates used by Liu–Salomão, even where the model surface is convex only on part of the component.
--
--   A point $y$ is a **strictly convex star-shaped point** of $G$ if $G$ is $C^2$ near $y$ and
--
--   $$
--   dG_y(y)>0,\qquad D^2G_y(v,v)>0\quad\text{for all } v\neq0 \text{ with } dG_y(v)=0 .
--   $$
--
--   Geometrically, the level set of $G$ through $y$ is transverse to the ray through $y$, with $G$ increasing outward, and its second fundamental form is positive definite at $y$. This is the pointwise version of the strict convexity and star-shapedness used for dynamically convex energy surfaces.
--
--   **Formalization Note** The model is `RegularizationModel μ c`, with fields `toModel`, `fromModel`, `symplecticScale`, `modelHamiltonian` and `timeScale`. The pointwise predicate is `IsStrictlyConvexStarShapedAt G y`, defined as `HasPositiveTangentialHessianOn G {y}` together with `0 < fderiv ℝ G y y`. The symplectic form is `phaseSymplecticForm` from `Def_BirkhoffGlobalSection_ConvexRegularizationModel`.
-- source:
--   Liu--Salomao, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/html/2506.17867v2: Section 9.2 (elliptic-hyperbolic regularization of the component, a symplectic change of coordinates with a positive time change), Definition 1.10(ii) and Section 9.4 (strict convexity of the lifted surface). Pointwise convexity condition as in Hofer--Wysocki--Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998). Fields follow Def_BirkhoffGlobalSection_ConvexRegularizationModel.

import Definitions.Def_BirkhoffGlobalSection_ConvexRegularizationModel

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- A smooth change of regularized coordinates for the selected Levi-Civita
component, with no convexity requirement.

The coordinate maps are smooth inverses on open neighborhoods, commute with the
antipodal map on the component, and preserve the symplectic form up to a
positive constant. The component lands in the regular zero level of a model
Hamiltonian, and the Levi-Civita field is carried to a positive multiple of the
model Hamiltonian field, including at collision points. The fields are those of
`ConvexRegularizationModel` without the convex body, so an alternative
regularization such as elliptic-hyperbolic coordinates can be recorded even
where it is only partially convex. -/
structure RegularizationModel (μ c : ℝ) where
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
  modelHamiltonian : Phase → ℝ
  model_smooth : ContDiffOn ℝ ∞ modelHamiltonian target
  model_zero : ∀ s ∈ leftEnergyComponent μ c, modelHamiltonian (toModel s) = 0
  model_regular : ∀ s ∈ leftEnergyComponent μ c,
    fderiv ℝ modelHamiltonian (toModel s) ≠ 0
  timeScale : Phase → ℝ
  timeScale_continuous : ContinuousOn timeScale source
  timeScale_pos : ∀ s ∈ leftEnergyComponent μ c, 0 < timeScale s
  vectorField : ∀ s ∈ leftEnergyComponent μ c,
    fderiv ℝ toModel s (hamiltonianVectorField (leviCivitaHamiltonian μ c) s) =
      timeScale s • hamiltonianVectorField modelHamiltonian (toModel s)

/-- The level set of `G` through `y` is strictly convex and star-shaped at `y`:
`G` is `C²` near `y`, its Hessian is positive on nonzero vectors annihilated by
`dG_y`, and `dG_y(y) > 0`, so the radial direction leaves the level set toward
increasing `G`. -/
def IsStrictlyConvexStarShapedAt (G : Phase → ℝ) (y : Phase) : Prop :=
  HasPositiveTangentialHessianOn G {y} ∧ 0 < fderiv ℝ G y y

end BirkhoffGlobalSection


