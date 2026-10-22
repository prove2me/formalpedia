-- Prove2me | Definitions.Def_BirkhoffGlobalSection_LiftedRationalPage
-- name    : BirkhoffGlobalSection_LiftedRationalPage
-- status  : Definition
-- author  : @caleb
-- created : 2026-09-26T18:19:45.105658+00:00
-- url     : https://prove2.me/theorems/a413608f-ee99-4919-b042-29b8e684f165
-- title:
--   Lifted rational two-disk page with two-sided returns
-- statement:
--   Let $\Sigma_{\mu,c}$ be the selected Levi-Civita energy component, $\varphi$ a complete flow on it, and $\gamma$ a periodic orbit. A lifted rational page consists of a map
--
--   $$
--   p:\overline{\mathbb D}\longrightarrow\Sigma_{\mu,c}
--   $$
--
--   that extends smoothly near the closed disk, is injective and immersive there, has boundary image equal to the orbit of $\gamma$, and is transverse to the Levi-Civita Hamiltonian vector field on the open disk. Its antipodal identifications are exactly
--
--   $$
--   p(u)=-p(v)\quad\Longleftrightarrow\quad
--   u,v\in\partial\mathbb D\ \text{and}\ v=-u.
--   $$
--
--   Every trajectory outside the binding meets one of the two lifted page interiors at arbitrarily large positive and negative times:
--
--   $$
--   \forall s\notin\gamma\ \forall R\in\mathbb R,\qquad
--   \exists t_+>R,\ \exists t_-<R,\quad
--   \varphi_{t_\pm}(s)\in p(\mathbb D)\cup(-p(\mathbb D)).
--   $$
--
--   This records the cover-level data of a rational two-disk global section without assuming any quotient dynamics. It is an interface for the single-page conclusion of Liu–Salomão Theorem 1.16(ii). Existence and transport from their regularization are separate mathematical obligations.
--
--   **Formalization Note.** The map is defined on the ambient real plane, with smoothness required at each point of the closed disk. The structure imposes no conditions away from the closed disk.
-- source:
--   Liu?Salom?o, Finite energy foliations and global dynamics in the restricted three-body problem, https://arxiv.org/abs/2506.17867v2, Theorem 1.16(ii), Section 9.2 and Section 10; Joung?van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 2.4. The cover-level definitions and descent formulation are formalization interfaces; the model and positive-time-change transport are explicit obligations, not conclusions quoted verbatim from the source.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

open scoped ContDiff

/-- A smooth lift of a rational two-disk page. The only antipodal identifications
occur at opposite boundary parameters. Return times are recorded upstairs to
either lift of the page, so this data does not presuppose quotient dynamics.

This is the cover-level page data needed to transport the single-page consequence
of Liu--Salomão, Theorem 1.16(ii), to the Levi-Civita model. Existence of this data,
including its model and time-change transport, is a separate theorem obligation. -/
structure LiftedRationalPage {μ c : ℝ}
    (φ : Flow ℝ (LeftEnergyState μ c)) (γ : PeriodicOrbit φ) where
  page : Plane → Phase
  mapsTo : ∀ u ∈ closedUnitDisk, page u ∈ leftEnergyComponent μ c
  smooth : ∀ u ∈ closedUnitDisk, ContDiffAt ℝ ∞ page u
  injective : Set.InjOn page closedUnitDisk
  immersion : ∀ u ∈ closedUnitDisk, Function.Injective (fderiv ℝ page u)
  transverse : ∀ u ∈ openUnitDisk,
    hamiltonianVectorField (leviCivitaHamiltonian μ c) (page u) ∉
      Set.range (fderiv ℝ page u)
  boundary : page '' unitCircle = orbitSet γ
  antipodal_fibers : ∀ u ∈ closedUnitDisk, ∀ v ∈ closedUnitDisk,
    (page u = -page v ↔ u ∈ unitCircle ∧ v ∈ unitCircle ∧ v = -u)
  returns : ∀ s : LeftEnergyState μ c, (s : Phase) ∉ orbitSet γ →
    (∀ R : ℝ, ∃ t : ℝ, R < t ∧ ∃ u ∈ openUnitDisk,
      ((φ t s : LeftEnergyState μ c) : Phase) = page u ∨
      ((φ t s : LeftEnergyState μ c) : Phase) = -page u) ∧
    (∀ R : ℝ, ∃ t : ℝ, t < R ∧ ∃ u ∈ openUnitDisk,
      ((φ t s : LeftEnergyState μ c) : Phase) = page u ∨
      ((φ t s : LeftEnergyState μ c) : Phase) = -page u)

end BirkhoffGlobalSection


