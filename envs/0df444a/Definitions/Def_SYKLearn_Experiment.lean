-- Prove2me | Definitions.Def_SYKLearn_Experiment
-- name    : SYKLearn_Experiment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:28.896185+00:00
-- url     : https://prove2.me/theorems/2def8930-ecd9-406d-9872-1ed227d6d26d
-- title:
--   The ideal scale-learning experiment: law $\nu$ of the energy difference, $\mathrm{Score}_a(\delta)$ and $\mathrm{AvgScore}(a)$
-- statement:
--   **Experiment 1.** Given a sample of a state $\sigma$ and a known Hamiltonian $\tilde H$: (1) measure the energy of $\tilde H$, obtaining an eigenvalue $\lambda$; (2) choose $i\in[n]$ uniformly at random and apply the Majorana operator $\psi_i$; (3) measure the energy again, obtaining $\lambda'$; (4) record $\delta=\lambda'-\lambda$. With the spectral projections $P_\lambda$ of $\tilde H$, the law of $\delta$ is
--
--   $$\nu=\frac1n\sum_{i=1}^n\ \sum_{\lambda,\lambda'\in\mathrm{spec}\,\tilde H}\mathrm{tr}\big[P_{\lambda'}\psi_iP_\lambda\,\sigma\,P_\lambda\psi_iP_{\lambda'}\big]\ \delta_{\lambda'-\lambda}.$$
--
--   For $\sigma=\rho_{\beta\alpha}(\tilde H)$ this is Lemma 4.1's $\nu(\delta)=\frac1n\sum_{i,\ \lambda_b-\lambda_a=\delta}\mu(a)|\langle b|\psi_i|a\rangle|^2$.
--
--   **Scores (Definition 4).** For a candidate $a$ and an outcome $\delta$,
--
--   $$\mathrm{Score}_a(\delta)=\begin{cases}\min(|\delta|,\beta^{-1})&\delta<0,\\-e^{-\beta a\delta}\min(|\delta|,\beta^{-1})&\delta>0,\\0&\delta=0,\end{cases}\qquad \mathrm{AvgScore}(a)=\mathbb E_{\delta\sim\nu}\mathrm{Score}_a(\delta).$$
--
--   By detailed balance the average score vanishes exactly at the true scale, which the paper locates by binary search.
--
--   **Formalization Note** The law is defined with spectral projections (continuous functional calculus), so it does not depend on a choice of eigenbasis; it is the zero measure if $\tilde H$ is not Hermitian, a case no statement uses. The input $\sigma$ is the physical state (trace one). The candidate $a$ ranges over all reals.
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Experiment 1, p.8; Lemma 4.1 and Definition 4, p.35

import Mathlib
import Definitions.Def_SYKLearn_Basic

noncomputable section
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace SYKLearn

/-!
# The ideal scale-learning experiment, its law, and the experiment scores

A. Anshu, S. Arunachalam, S. Chen, Y. Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission (held file sha256 5d7d199a…), Experiment 1, p.8; Lemma 4.1 and Definition 4, p.35.

**Formalization Note.**
* Experiment 1 measures the energy of the measured Hamiltonian `K` (projectively), applies a
  uniformly random Majorana `ψ_i`, `i ∈ [n]`, and measures the energy again; it records
  `δ = E_b − E_a`. With the spectral projections `P_λ` of `K` and the physical input state `σ`
  (trace one), the joint probability of `(i, λ, λ′)` is
  `(1/n) tr[P_{λ′} ψ_i P_λ σ P_λ ψ_i P_{λ′}]`. `energyLaw γ K σ` is the law of `δ = λ′ − λ`:
  `ν = (1/n) Σ_i Σ_{λ,λ′ ∈ spec K} tr[P_{λ′} ψ_i P_λ σ P_λ ψ_i P_{λ′}] · δ_{λ′−λ}`. This is defined
  without choosing an eigenbasis; for `σ = f(K)` (in particular `σ = e^{−βαK}/tr e^{−βαK}`) it is
  Lemma 4.1's `ν(δ) = (1/n) Σ_{i, λ_b − λ_a = δ} µ(a)|⟨b|ψ_i|a⟩|²` summed over any eigenbasis.
  `spec K` is the finite set of eigenvalues and `P_λ = 1_{\{λ\}}(K)` (continuous functional
  calculus). The law is the zero measure when `K` is not Hermitian (no statement uses that case).
* `score β a δ` is Definition 4's `Score_a(δ)`: `min(|δ|, β⁻¹)` for `δ < 0`,
  `−e^{−βaδ} min(|δ|, β⁻¹)` for `δ > 0`, `0` for `δ = 0`; `avgScore β a ν = E_{δ∼ν} Score_a(δ)`.
  The candidate `a` is any real number.
-/

open SYKFastMix.FastMixing

/-- The spectral projection `P_λ = 1_{\{λ\}}(K)` of a matrix `K`. -/
def specProj {ι : Type} [Fintype ι] [DecidableEq ι] (K : Mat ι) (l : ℝ) : Mat ι :=
  cfc (fun x : ℝ => if x = l then (1 : ℝ) else 0) K

/-- The law `ν` of the energy difference `δ` in the ideal Experiment 1 (p.8; Lemma 4.1, p.35),
for Majoranas `γ`, measured Hamiltonian `K` and physical input state `σ`. -/
def energyLaw {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (γ : Fin N → Mat ι) (K : Mat ι)
    (σ : Mat ι) : Measure ℝ :=
  if hK : K.IsHermitian then
    ∑ i : Fin N, ∑ l ∈ Finset.univ.image hK.eigenvalues, ∑ l' ∈ Finset.univ.image hK.eigenvalues,
      (ENNReal.ofReal ((N : ℝ)⁻¹ *
        (Matrix.trace (specProj K l' * γ i * specProj K l * σ * specProj K l * γ i *
          specProj K l')).re)) • Measure.dirac (l' - l)
  else 0

/-- `Score_a(δ)` (Definition 4, p.35). -/
def score (β a δ : ℝ) : ℝ :=
  if δ < 0 then min |δ| β⁻¹ else if 0 < δ then -Real.exp (-(β * a * δ)) * min |δ| β⁻¹ else 0

/-- `AvgScore(a) = E_{δ∼ν} Score_a(δ)` (Definition 4, p.35). -/
def avgScore (β a : ℝ) (ν : Measure ℝ) : ℝ :=
  ∫ δ, score β a δ ∂ν

end SYKLearn


