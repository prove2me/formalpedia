-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_ChapterCertification10to12AndGP
-- name    : AppliedSDE_SarkkaSolin_ChapterCertification10to12AndGP
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T18:03:39.596243+00:00
-- url     : https://prove2.me/theorems/94ad63e9-7fb2-4eb7-bff3-16fb010b91b1
-- title:
--   Certification propositions for 10to12AndGP
-- statement:
--   Named propositions for chapter certification: Chapters 10–12 and the OU/GP/Kalman application. Each declaration is a Prop-valued abbreviation of the exact published-goal candidate statement from the current textbook Draft. It is not a theorem, axiom, proof or verified result. All quantified mathematical hypotheses are preserved.
--
--   Representative mathematical obligation:
--
--   $$
--   \mathcal{P}_{10to12AndGP}
--   $$
-- source:
--   Original derived formal certification definitions from Simo Särkkä and Arno Solin (2019), Applied Stochastic Differential Equations, Chapters 10–12, printed pp. 199–268. https://doi.org/10.1017/9781108186735

import Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormula
import Mathlib
open MeasureTheory Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal Topology BigOperators
open LevyStochCalc
open MeasureTheory
open scoped BigOperators Topology
open scoped BigOperators
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Filter
open Matrix
open scoped BigOperators Matrix
set_option autoImplicit false
universe u

def private_sde_cert_ch10 : Prop :=
  ∀ 
    (F H Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 < R)
    (P : ℝ → ℝ) (hP0 : 0 ≤ P 0)
    (hcont : Continuous P)
    (hdiff : ∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ P t)
    (hode : ∀ t : ℝ, 0 ≤ t →
      deriv P t = 2 * F * P t + Q - (H ^ 2 / R) * (P t) ^ 2),
    ∀ t : ℝ, 0 ≤ t → 0 ≤ P t

def private_sde_cert_ch11 : Prop :=
  ∀ 
    (rate q Δ : ℝ) (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ)
    {n : ℕ} (hn : 0 < n) (x : Fin (n + 1) → ℝ),
    let a : ℝ := Real.exp (-rate * Δ)
    let v : ℝ := q / (2 * rate) * (1 - Real.exp (-(2 * rate * Δ)))
    let ρ : Fin n → ℝ := fun k =>
      Real.exp (-((x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2) / (2 * v)) /
        Real.sqrt (2 * Real.pi * v)
    0 < v ∧
      (∀ k : Fin n, 0 < ρ k) ∧
      (-Real.log (∏ k : Fin n, ρ k) =
        ∑ k : Fin n,
          (Real.log (2 * Real.pi * v) / 2 +
            (x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2 / (2 * v)))

def private_sde_cert_ch12 : Prop :=
  ∀ 
    (C₁ C₂ : ℝ → ℝ → ℝ)
    (hsym₁ : ∀ s t : ℝ, C₁ s t = C₁ t s)
    (hsym₂ : ∀ s t : ℝ, C₂ s t = C₂ t s)
    (hpsd₁ : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * C₁ (t i) (t j))
    (hpsd₂ : ∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * C₂ (t i) (t j)),
    (∀ s t : ℝ, C₁ s t + C₂ s t = C₁ t s + C₂ t s) ∧
    (∀ s t : ℝ, C₁ s t * C₂ s t = C₁ t s * C₂ t s) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (C₁ (t i) (t j) + C₂ (t i) (t j))) ∧
    (∀ (n : ℕ) (t : Fin n → ℝ) (a : Fin n → ℝ),
      0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        a i * a j * (C₁ (t i) (t j) * C₂ (t i) (t j)))

def private_sde_cert_gp : Prop :=
  ∀ 
    (n : ℕ) (rate q Δ r : ℝ)
    (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ) (hr : 0 < r)
    (y : Fin (n + 1) → ℝ) (m P : Fin (n + 1) → ℝ),
    let V : ℝ := q / (2 * rate)
    let a : ℝ := AppliedSDE.SarkkaSolin.ouStepFactor rate Δ
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      fun i j => AppliedSDE.SarkkaSolin.stationaryOUCovariance rate q ((i.val : ℝ) * Δ) ((j.val : ℝ) * Δ)
    (P 0 = V * r / (V + r)) →
    (m 0 = V / (V + r) * y 0) →
    (∀ k : Fin n,
      let predicted : ℝ := AppliedSDE.SarkkaSolin.ouPredictedVariance rate q Δ (P k.castSucc)
      P k.succ = AppliedSDE.SarkkaSolin.scalarUpdatedVariance predicted r ∧
      m k.succ = a * m k.castSucc +
        AppliedSDE.SarkkaSolin.scalarKalmanGain predicted r * (y k.succ - a * m k.castSucc)) →
    m (Fin.last n) =
      AppliedSDE.SarkkaSolin.gpBatchPosteriorMean K r y
        (Fin.last n)


