-- Prove2me | Definitions.Def_MinimaxWass_DataDep_Setting
-- name    : MinimaxWass_DataDep_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:26.775742+00:00
-- url     : https://prove2.me/theorems/331dc173-2f59-49ed-88bb-b49ee6d26cc3
-- title:
--   §1–§3.1, App. C.1, pp. 1–5, 13–14 — risk R, local risks R_{ϱ,p}, R*_{ϱ,p}, φ_{λ,f} (8), empirical law P_n, covering number, entropy integral 𝔆(ℱ), X_λ, Rademacher supremum
-- statement:
--   On a metric instance space $\mathcal Z$, a probability law $Q$, and a real-valued loss $f$, the risk is $R(Q,f)=\int f\,dQ$. The local worst-case risk $R_{\varrho,p}(P,f)$ is the supremum of this risk over the published $p$-Wasserstein ball of radius $\varrho$ around $P$; the local minimax risk is $\inf_{f\in\mathcal F}R_{\varrho,p}(P,f)$ for a nonempty class $\mathcal F$. The dual envelope in (8) is
--
--   $$\varphi_{\lambda,f}(z)=\sup_{z'\in\mathcal Z}\{f(z')-\lambda d_{\mathcal Z}(z,z')^p\}.$$
--
--   The empirical law of a nonempty sample is $P_n=n^{-1}\sum_{i=1}^n\delta_{Z_i}$. The internal uniform covering number $\mathcal N(\mathcal F,\|\cdot\|_\infty,u)$ uses finitely many centres from $\mathcal F$; its entropy integral is $\mathfrak C(\mathcal F)=\int_0^\infty\sqrt{\log\mathcal N(\mathcal F,\|\cdot\|_\infty,u)}\,du$. The file also defines the independent sample law, the supremum deviation $X_\lambda$ of Appendix C.1, and the expected supremum of its Rademacher average.
--
--   These definitions are the shared model of all three missions of this paper (Theorem 1, Theorem 2, Theorem 3) and of the appendix milestones; $X_\lambda$ and the Rademacher supremum are the processes of the proof of Theorem 1 in Appendix C.1. The entropy integral is extended nonnegative, so an infinite covering number remains infinite.
--
--   **Formalization Note** The empirical probability law is the normalized finite sum of Dirac measures. Internal covering centres are used because the paper does not specify their location. Real suprema are used only under the boundedness and nonemptiness hypotheses stated in the theorems.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, https://arxiv.org/abs/1705.07815, pp. 1–5, risk, Definition 1, local risks, (8), Assumptions 1–2; Appendix C.1, pp. 13–14

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinBall

open MeasureTheory
open scoped ENNReal

namespace MinimaxWass.DataDep

/-! The objects in Lee--Raginsky, Sections 1--3.1 and Appendix C.1. -/

/-- Expected risk, Section 1, p. 1. -/
noncomputable def risk {𝒵 : Type*} [MeasurableSpace 𝒵]
    (Q : ProbabilityMeasure 𝒵) (f : 𝒵 → ℝ) : ℝ :=
  ∫ z, f z ∂(Q : Measure 𝒵)

/-- Local worst-case risk, Section 2, p. 3. -/
noncomputable def localRisk {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    (p ϱ : ℝ) (P : ProbabilityMeasure 𝒵) (f : 𝒵 → ℝ) : ℝ :=
  ⨆ Q : WassersteinLinOpt.Ball.wassersteinBall p ϱ P, risk Q.1 f

/-- Local minimax risk, Section 2, p. 3.  Used for nonempty loss classes. -/
noncomputable def localMinimaxRisk {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    (p ϱ : ℝ) (P : ProbabilityMeasure 𝒵) (ℱ : Set (𝒵 → ℝ))
    (_hF : ℱ.Nonempty) : ℝ :=
  ⨅ f : ℱ, localRisk p ϱ P f.1

/-- The envelope φ_{λ,f} of (8), p. 4. -/
noncomputable def phi {𝒵 : Type*} [MetricSpace 𝒵]
    (p lam : ℝ) (f : 𝒵 → ℝ) (z : 𝒵) : ℝ :=
  ⨆ z' : 𝒵, f z' - lam * dist z z' ^ p

/-- Empirical law P_n = n⁻¹ Σ_i δ_{ω_i}, Section 1, p. 1.
The positive sample size supplies a point of 𝒵 for `FiniteMeasure.normalize`. -/
noncomputable def empiricalPM {𝒵 : Type*} [MeasurableSpace 𝒵]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → 𝒵) : ProbabilityMeasure 𝒵 := by
  letI : Nonempty 𝒵 := ⟨ω ⟨0, hn⟩⟩
  let fm : FiniteMeasure 𝒵 := ⟨∑ i : Fin n, Measure.dirac (ω i), inferInstance⟩
  exact FiniteMeasure.normalize fm

/-- Uniform-metric internal covering number, Section 3.1, p. 5. -/
noncomputable def coveringNumberSup {𝒵 : Type*} (ℱ : Set (𝒵 → ℝ)) (u : ℝ) : ℕ∞ :=
  sInf {m : ℕ∞ | ∃ s : Finset (𝒵 → ℝ),
    (∀ g ∈ s, g ∈ ℱ) ∧
    (∀ f ∈ ℱ, ∃ g ∈ s, ∀ z, |f z - g z| ≤ u) ∧
    m = s.card}

/-- The entropy integral 𝔆(ℱ), Section 3.1, p. 5.  An infinite covering number
gives an infinite integrand rather than `ENNReal.toReal ⊤ = 0`. -/
noncomputable def entropyIntegral {𝒵 : Type*} (ℱ : Set (𝒵 → ℝ)) : ℝ≥0∞ :=
  ∫⁻ u : ℝ in Set.Ioi 0,
    if coveringNumberSup ℱ u = ⊤ then ⊤
    else ENNReal.ofReal (Real.sqrt (Real.log ((coveringNumberSup ℱ u).getD 0 : ℝ)))

/-- Joint law of n independent P-distributed observations, Section 3, p. 4. -/
noncomputable def sampleLaw {𝒵 : Type*} [MeasurableSpace 𝒵]
    (n : ℕ) (P : ProbabilityMeasure 𝒵) : Measure (Fin n → 𝒵) :=
  Measure.pi (fun _ : Fin n => (P : Measure 𝒵))

/-- X_λ of Appendix C.1, p. 13. -/
noncomputable def Xlam {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    {n : ℕ} (p lam : ℝ) (P : ProbabilityMeasure 𝒵) (ℱ : Set (𝒵 → ℝ))
    (ω : Fin n → 𝒵) : ℝ :=
  ⨆ f : ℱ, (∫ z, phi p lam f.1 z ∂(P : Measure 𝒵)) -
    (1 / (n : ℝ)) * ∑ i : Fin n, phi p lam f.1 (ω i)

/-- Expected supremum of the Rademacher average in Appendix C.1, pp. 13--14.
`Bool` encodes independent uniform signs, +1 for true and -1 for false. -/
noncomputable def rademacherSup {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵]
    (n : ℕ) (p lam : ℝ) (P : ProbabilityMeasure 𝒵) (ℱ : Set (𝒵 → ℝ)) : ℝ :=
  ∫ ω, (1 / (2 : ℝ) ^ n) *
    ∑ ε : Fin n → Bool,
      (⨆ f : ℱ, (1 / (n : ℝ)) * ∑ i : Fin n,
        (if ε i then (1 : ℝ) else -1) * phi p lam f.1 (ω i))
    ∂(sampleLaw n P)

end MinimaxWass.DataDep


