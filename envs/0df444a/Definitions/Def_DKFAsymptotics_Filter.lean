-- Prove2me | Definitions.Def_DKFAsymptotics_Filter
-- name    : DKFAsymptotics_Filter
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-15T20:51:38.615515+00:00
-- url     : https://prove2.me/theorems/6c3f5641-fdd2-40fd-9b8a-0f83d0b195af
-- title:
--   Stationary Gaussian model and standard DKF recursion
-- statement:
--   The model consists of $A,\Gamma,S$ with positive-definite noise and stationary covariances and $S=ASA^\top+\Gamma$. It defines the stationary density, Gaussian transition, prediction integral, and discriminative update $u\tau s/p$ normalized by its $L^1$ norm. Update validity means a measurable weight with finite, strictly positive normalizer. The standard DKF matrix step uses prediction covariance $AVA^\top+\Gamma$, updated precision $U^{-1}+(AVA^\top+\Gamma)^{-1}-S^{-1}$, its inverse covariance, and the corresponding precision-weighted mean. The recursive DKF starts at mean zero and covariance $S$ and incorporates the observation functions $f,Q$ at each positive time. Matrix expressions are total; a separate validity predicate requires invertible precision and positive-definite updated covariance. No universal step-validity condition is imposed by the recursion.
-- source:
--   M. C. Burkhart, D. M. Brandman, B. Franco, L. R. Hochberg and M. T. Harrison, The Discriminative Kalman Filter for Bayesian Filtering with Nonlinear and Nongaussian Observation Models, Neural Computation 32(5), 969–1017 (2020), doi:10.1162/neco_a_01275; https://burkh4rt.github.io/pubs/Burkhart-et-al-2020-Neural-Comput.pdf; Section 2.1, equations (2.1), (2.4)–(2.7), pp. 972–974; Appendix B, equation (B.1), p. 1003; Lemma 1, pp. 1007–1008.

import Definitions.Def_DKFAsymptotics_Densities

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics

structure Model (d : ℕ) where
  A : Covariance d
  Γ : Covariance d
  S : Covariance d
  Γ_posDef : Γ.PosDef
  S_posDef : S.PosDef
  stationary : S = A * S * A.transpose + Γ

variable {d : ℕ}

def prior (M : Model d) : Density d := gaussianPDF 0 M.S

def transition (M : Model d) (y z : State d) : ℝ :=
  gaussianPDF (M.A *ᵥ y) M.Γ z

def predictDensity (M : Model d) (s : Density d) : Density d :=
  fun z => ∫ y, transition M y z * s y ∂volume

def updateWeight (M : Model d) (s u : Density d) : Density d :=
  fun z => u z * predictDensity M s z / prior M z

def UpdateDefined (M : Model d) (s u : Density d) : Prop :=
  AEStronglyMeasurable (updateWeight M s u) volume ∧
    0 < l1Norm (updateWeight M s u) ∧ l1Norm (updateWeight M s u) < ⊤

def updateDensity (M : Model d) (s u : Density d) : Density d :=
  fun z => updateWeight M s u z / (l1Norm (updateWeight M s u)).toReal

structure GaussianState (d : ℕ) where
  mean : State d
  covariance : Covariance d

def predictedCovariance (M : Model d) (V : Covariance d) : Covariance d :=
  M.A * V * M.A.transpose + M.Γ

def updatePrecision (M : Model d) (V U : Covariance d) : Covariance d :=
  U⁻¹ + (predictedCovariance M V)⁻¹ - M.S⁻¹

def dkfStep (M : Model d) (previous observation : GaussianState d) : GaussianState d :=
  let G := predictedCovariance M previous.covariance
  let T := (updatePrecision M previous.covariance observation.covariance)⁻¹
  ⟨T *ᵥ (observation.covariance⁻¹ *ᵥ observation.mean +
    G⁻¹ *ᵥ (M.A *ᵥ previous.mean)), T⟩

def ValidStep (M : Model d) (previous observation : GaussianState d) : Prop :=
  IsUnit (updatePrecision M previous.covariance observation.covariance).det ∧
    (dkfStep M previous observation).covariance.PosDef

def dkf {X : Type} (M : Model d) (f : X → State d) (Q : X → Covariance d)
    (observations : ℕ+ → X) : ℕ → GaussianState d
  | 0 => ⟨0, M.S⟩
  | t + 1 => dkfStep M (dkf M f Q observations t)
      ⟨f (observations ⟨t + 1, Nat.succ_pos t⟩), Q (observations ⟨t + 1, Nat.succ_pos t⟩)⟩

end DKFAsymptotics


