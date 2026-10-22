-- Prove2me | Definitions.Def_EntFluctCDS_GreenKubo_Family
-- name    : EntFluctCDS_GreenKubo_Family
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:48.384686+00:00
-- url     : https://prove2.me/theorems/b72ea613-767d-42c1-bad3-6eb44e62340a
-- title:
--   §4.1–4.3 — regular force families, fluxes, time averages and the GES functional
-- statement:
--   Fix a positive number $N$ of control parameters and a measurable configuration space $M$. A family assigns to each force $X\in\mathbb R^N$ a regular continuous-time system $(M,\phi_X,\omega_X)$ and a measurable vector flux $\Phi_X:M\to\mathbb R^N$. The regular system includes the dynamics, equivalent evolved and reference states, and the differentiable density that defines its entropy-production observable $\sigma_X$. The defining flux relation is
--
--   $$\sigma_X=\sum_{j=1}^N X_j\Phi_X^{(j)}\quad\omega_X\text{-almost everywhere}. $$
--
--   Each flux coordinate is time-integrable along almost every trajectory on every finite interval, so the paper's integrated flux is defined. This file also defines the assumptions (T1), equilibrium stationarity only at $X=0$, and (T2), time reversal and odd flux for each $X$. It defines the integrated flux, its time-averaged law $P_X^t$, its reflected law, the actual extended log-Laplace functional
--
--   $$g_t(X,Y)=\log\int_M\exp\left(-\sum_jY_j\int_0^t\Phi_X^{(j)}(\phi_X^s x)\,ds\right)d\omega_X(x),$$
--
--   the $X$-system time average, the force derivative $L_{jkt}$, and the equilibrium correlation $\omega_0(\Phi_0^{(k)}\,\Phi_{0,s}^{(j)})$. The $C^{1,2}$ predicate requires existence and continuity of precisely the five families of partial derivatives specified before Lemma 4.4. A local space-time integrability predicate states the Fubini condition used for the time average.
--
--   These common definitions make the symmetry and linear-response statements refer to the same family and the same flux.
--
--   **Formalization Note** The log moment is extended-valued; conversion to a real number is used only under a local finiteness hypothesis. Coordinate partials use derivatives along coordinate lines. The time average uses both $\omega_X$ and $\phi_X$, as required by the first display of the proof on p. 21.
-- source:
--   Jakšić, Pillet & Rey-Bellet, Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, pp. 17–20, §§4.1–4.3, Definition 4.1, (4.26), (4.28)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace EntFluctCDS.GreenKubo

open QAlgorithms.Papers.Independent.Support21.P03

/-- A family from §4.1, with one regular system for every force and a measurable
flux relation satisfying (4.26) modulo the reference state. -/
structure Family (N : ℕ) (M : Type*) [MeasurableSpace M] where
  positive_dim : 0 < N
  sys : (Fin N → ℝ) → RegularSystem M
  flux : (Fin N → ℝ) → M → Fin N → ℝ
  flux_measurable : ∀ X, Measurable (flux X)
  flux_time_integrable : ∀ X t j,
    ∀ᵐ x ∂((sys X).omega : Measure M),
      IntervalIntegrable (fun s : ℝ => flux X ((sys X).flow s x) j) volume 0 t
  flux_relation : ∀ X, ∀ᵐ x ∂((sys X).omega : Measure M),
    continuousSigma (sys X) x = ∑ j, X j * flux X x j

variable {N : ℕ} {M : Type*} [MeasurableSpace M]

/-- Assumption (T1), only at equilibrium X=0. -/
def T1 (F : Family N M) : Prop :=
  IsStationary (F.sys 0).toNonsingularSystem (F.sys 0).omega

/-- Assumption (T2), with a possibly force-dependent time reversal. -/
def T2 (F : Family N M) : Prop :=
  ∀ X, ∃ θ : M ≃ᵐ M,
    IsTimeReversal (F.sys X).toNonsingularSystem θ ∧
      ∀ᵐ x ∂((F.sys X).omega : Measure M), F.flux X (θ x) = -F.flux X x

/-- The unnormalized time-integrated flux of §4.2. -/
def integratedFlux (F : Family N M) (X : Fin N → ℝ) (t : ℝ) (x : M) : Fin N → ℝ :=
  fun j => ∫ s in 0..t, F.flux X ((F.sys X).flow s x) j

/-- The law P_X^t of the time-averaged flux, for nonzero t. -/
def fluxLaw (F : Family N M) (X : Fin N → ℝ) (t : ℝ) : Measure (Fin N → ℝ) :=
  Measure.map (fun x => t⁻¹ • integratedFlux F X t x) (F.sys X).omega

/-- The reflected law of §4.2. -/
def reflectedFluxLaw (F : Family N M) (X : Fin N → ℝ) (t : ℝ) :
    Measure (Fin N → ℝ) :=
  Measure.map (fun s : Fin N → ℝ => -s) (fluxLaw F X t)

/-- The extended log-Laplace functional g_t(X,Y) of (4.28). -/
def gesFunctional (F : Family N M) (t : ℝ) (X Y : Fin N → ℝ) : EReal :=
  ENNReal.log
    (∫⁻ x, ENNReal.ofReal (Real.exp (-(∑ j, Y j * integratedFlux F X t x j)))
      ∂((F.sys X).omega : Measure M))

/-- The §4.3 time average in the X-system: both state and flow depend on X. -/
def timeAverage (F : Family N M) (t : ℝ) (X : Fin N → ℝ) : Fin N → ℝ :=
  fun j => t⁻¹ * ∫ s in 0..t, ∫ x, F.flux X ((F.sys X).flow s x) j
    ∂((F.sys X).omega : Measure M)

/-- L_jkt, the derivative of the X-system time average in force coordinate k. -/
def kineticCoeff (F : Family N M) (t : ℝ) (j k : Fin N) : ℝ :=
  deriv (fun h : ℝ => timeAverage F t (Pi.single k h) j) 0

/-- The equilibrium correlation with k at time zero and j at time s. -/
def correlation (F : Family N M) (j k : Fin N) (s : ℝ) : ℝ :=
  ∫ x, F.flux 0 x k * F.flux 0 ((F.sys 0).flow s x) j
    ∂((F.sys 0).omega : Measure M)

/-- Coordinate partial derivatives use the line through the given point. -/
def partialX (a : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) (i : Fin N)
    (X Y : Fin N → ℝ) : ℝ :=
  deriv (fun h : ℝ => a (X + Pi.single i h) Y) 0

def partialY (a : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) (i : Fin N)
    (X Y : Fin N → ℝ) : ℝ :=
  deriv (fun h : ℝ => a X (Y + Pi.single i h)) 0

/-- Exactly the five families of existing, continuous partials specified before
Lemma 4.4: X, Y, YY, XY, and YX. No second X derivative is required. -/
def IsC12On (a : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (O : Set ((Fin N → ℝ) × (Fin N → ℝ))) : Prop :=
  (∀ p ∈ O, ∀ i,
    HasDerivAt (fun h : ℝ => a (p.1 + Pi.single i h) p.2)
      (partialX a i p.1 p.2) 0 ∧
    HasDerivAt (fun h : ℝ => a p.1 (p.2 + Pi.single i h))
      (partialY a i p.1 p.2) 0) ∧
  (∀ i, ContinuousOn (fun p : (Fin N → ℝ) × (Fin N → ℝ) => partialX a i p.1 p.2) O ∧
    ContinuousOn (fun p : (Fin N → ℝ) × (Fin N → ℝ) => partialY a i p.1 p.2) O) ∧
  (∀ p ∈ O, ∀ i j,
    HasDerivAt (fun h : ℝ => partialY a j p.1 (p.2 + Pi.single i h))
      (partialY (partialY a j) i p.1 p.2) 0 ∧
    HasDerivAt (fun h : ℝ => partialY a i (p.1 + Pi.single j h) p.2)
      (partialX (partialY a i) j p.1 p.2) 0 ∧
    HasDerivAt (fun h : ℝ => partialX a j p.1 (p.2 + Pi.single i h))
      (partialY (partialX a j) i p.1 p.2) 0) ∧
  (∀ i j,
    ContinuousOn (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      partialY (partialY a j) i p.1 p.2) O ∧
    ContinuousOn (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      partialX (partialY a i) j p.1 p.2) O ∧
    ContinuousOn (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      partialY (partialX a j) i p.1 p.2) O)

/-- The local space-time Fubini condition used in §4.3. -/
def FluxIntegrableNear (F : Family N M) (t : ℝ)
    (U : Set (Fin N → ℝ)) : Prop :=
  ∀ X ∈ U, ∀ j,
    Integrable (fun p : ℝ × M => F.flux X ((F.sys X).flow p.1 p.2) j)
      ((volume.restrict (Icc 0 t)).prod ((F.sys X).omega : Measure M))

end EntFluctCDS.GreenKubo


