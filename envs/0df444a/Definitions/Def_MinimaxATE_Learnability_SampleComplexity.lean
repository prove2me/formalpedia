-- Prove2me | Definitions.Def_MinimaxATE_Learnability_SampleComplexity
-- name    : MinimaxATE_Learnability_SampleComplexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:01:06.118011+00:00
-- url     : https://prove2.me/theorems/89fdad4f-1b66-41c2-9c3f-cb472bd19ef6
-- title:
--   Randomized estimators, the sample complexity $N_{\mathrm{ATE}}(\varepsilon,\delta;\mathcal P,\mathcal M,c)$ (eq. (1)) and learnability (Problem 1)
-- statement:
--   An **estimator based on $n$ samples** is a measurable map $\hat\tau_n:(\mathcal X\times\{0,1\}\times\mathbb R)^n\times\mathbb R\to\mathbb R$; its input is $n$ independent observations from the observed law $C_D$ together with an independent internal seed $U\sim\mathrm{Uniform}[0,1]$, which carries the estimator's internal randomness. Its **failure probability** at accuracy $\varepsilon$ is
--   $$\Pr_D\{|\hat\tau_n-\tau_D|>\varepsilon\}=(C_D^{\otimes n}\otimes\mathrm{Unif}[0,1])\big(\{|\hat\tau_n-\tau_D|>\varepsilon\}\big).$$
--   The **sample complexity** (eq. (1)) is
--   $$N_{\mathrm{ATE}}(\varepsilon,\delta;\mathcal P,\mathcal M,c)=\min\Big\{n\in\mathbb N_0:\ \exists\text{ measurable }\hat\tau_n,\ \sup_{D\in\mathcal D(\mathcal P,\mathcal M,c)}\Pr_D\{|\hat\tau_n-\tau_D|>\varepsilon\}\le\delta\Big\},$$
--   and $N_{\mathrm{ATE}}=\infty$ if no such $n$ exists. The ATE is **learnable** (Problem 1) if $N_{\mathrm{ATE}}(\varepsilon,\delta;\mathcal P,\mathcal M,c)<\infty$ for every $\varepsilon,\delta\in(0,1)$.
--
--   **Formalization Note.** Samples are indexed by `Fin n`; the seed space is `ℝ` with the uniform law on `[0, 1]` (one uniform variable carries any countable amount of randomness). `NATE` is an infimum in `ℕ∞`, so it is `⊤` when no sample size suffices; the supremum over $\mathcal D(\mathcal P,\mathcal M,c)$ is written as "for every $D$ in the class", so an empty class makes every $n$ (in particular $n=0$) suffice.
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 19 (PDF 21), eq. (1); p. 2 (PDF 4), Problem 1

import Mathlib
import Definitions.Def_MinimaxATE_Learnability_Model

open MeasureTheory

namespace MinimaxATE.Learnability

/-- The law of the input of an estimator based on `n` samples: `n` independent observations from
`C_D` (indexed by `Fin n`) together with an independent internal seed `U ~ Uniform[0, 1]`, which
carries the estimator's internal randomness (§3, p. 19). -/
noncomputable def sampleLaw {X : Type*} [MeasurableSpace X] (D : Study X) (n : ℕ) :
    Measure ((Fin n → Obs X) × ℝ) :=
  (Measure.pi fun _ : Fin n => observedLaw D).prod (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The failure probability `Pr_D{|τ̂_n − τ_D| > ε}` of an estimator
`τ̂_n : (X × {0,1} × ℝ)^n × [0, 1] → ℝ` (§3, eq. (1), p. 19), as the measure of the failure set. -/
noncomputable def failureProb {X : Type*} [MeasurableSpace X] (D : Study X) (n : ℕ)
    (τhat : (Fin n → Obs X) × ℝ → ℝ) (ε : ℝ) : ENNReal :=
  sampleLaw D n {z | ε < |τhat z - ate D|}

/-- `n` samples suffice for accuracy `ε` and confidence `δ`: some measurable estimator based on
`n` samples has failure probability at most `δ` for every study in `D(P, M, c)` (eq. (1)). -/
def SampleSuffices {X : Type*} [MeasurableSpace X] (P M : Set (X → ℝ)) (c ε δ : ℝ) (n : ℕ) :
    Prop :=
  ∃ τhat : (Fin n → Obs X) × ℝ → ℝ, Measurable τhat ∧
    ∀ D ∈ DClass P M c, failureProb D n τhat ε ≤ ENNReal.ofReal δ

/-- The sample complexity `N_ATE(ε, δ; P, M, c)` (eq. (1), p. 19): the least `n ∈ ℕ₀` such that
`n` samples suffice, and `∞` (`⊤ : ℕ∞`) if there is none. -/
noncomputable def NATE {X : Type*} [MeasurableSpace X] (ε δ : ℝ) (P M : Set (X → ℝ)) (c : ℝ) :
    ℕ∞ :=
  ⨅ (n : ℕ) (_ : SampleSuffices P M c ε δ n), (n : ℕ∞)

/-- The ATE is learnable (Problem 1, p. 2): for every `ε, δ ∈ (0, 1)`, `N_ATE(ε, δ) < ∞`. -/
def Learnable {X : Type*} [MeasurableSpace X] (P M : Set (X → ℝ)) (c : ℝ) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → NATE ε δ P M c < ⊤

end MinimaxATE.Learnability


