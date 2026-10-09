-- Prove2me | Definitions.Def_StochKolmogorov_Classify_Classification
-- name    : StochKolmogorov_Classify_Classification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:31:45.782008+00:00
-- url     : https://prove2.me/theorems/8057da41-0f92-4995-8168-571c014efab0
-- title:
--   §1.1, pp. 7–8, Lemma 5.9, p. 26 — occupation measures Π̃_t, the limit set U(ω), Assumptions 1.4 and 1.5, the event of P^µ_x, the boxes K^{k,Δ}_µ
-- statement:
--   This module defines the objects of Theorem 1.3 on top of the model of (1.1).
--
--   1. The **random normalized occupation measure** of the path started at $x$ (Remark 1.7, p. 7):
--   $$
--   \widetilde\Pi_t(\cdot) = \frac1t\int_0^t \mathbf 1_{\{X(s)\in\cdot\}}\,ds,\qquad t > 0.
--   $$
--   2. The **weak\*-limit set** $\mathcal U(\omega)$ of the family $\{\widetilde\Pi_t(\omega), t \ge 1\}$ (p. 8): the probability measures $\pi$ such that $\int h\,d\widetilde\Pi_{t_k}(\omega) \to \int h\,d\pi$ for every bounded continuous $h$, along some sequence $t_k \ge 1$ with $t_k \to \infty$.
--   3. **Assumption 1.4** (p. 7): there is $\delta_1 > 0$ with
--   $$
--   \lim_{\|x\|\to\infty,\ x\in\mathbb R^n_+}\frac{\|x\|^{\delta_1}\sum_i g_i^2(x)}{1+\sum_i(|f_i(x)|+|g_i(x)|^2)} = 0 .
--   $$
--   4. **Assumption 1.5** (p. 8): either $\mathcal M^2 = \emptyset$, or $\max_{i}\lambda_i(\nu) > 0$ for every $\nu \in \mathrm{Conv}(\mathcal M^2)$.
--   5. For $\mu \in \mathcal M^1$ and $x$, the **event of $P^\mu_x$**: $\mathcal U(\omega) = \{\mu\}$ and $\lim_{t\to\infty}\ln X_i(t)/t = \lambda_i(\mu) < 0$ for every $i \in I^c_\mu$.
--   6. The **boxes** of Lemma 5.9: $\mathcal K^{k,\Delta}_\mu = \{x \in \mathbb R^{n,\circ}_+ : k^{-1} \le x_i \le k \text{ for } i \in I_\mu,\ x_i < \Delta \text{ for } i \in I^c_\mu\}$.
--   7. Two auxiliary functions: the weight $(1+c^\top x)^\delta(1+\sum_i(|f_i(x)|+|g_i(x)|^2))$ of Lemmas 3.3, 5.4, 5.6, and the Brownian integrands $\sum_i c_i x_i g_i(x)\Gamma_{ji}/(1+c^\top x)$, $j = 1,\dots,n$, of the stochastic integral in (5.17).
--
--   **Formalization Note** Weak convergence is tested against bounded continuous functions on $\mathbb R^n$; all the measures involved live on the closed set $\mathbb R^n_+$, so this is weak convergence on $\mathbb R^n_+$. Since probability measures on $\mathbb R^n$ with the weak topology form a metrizable space, sequential limit points are the limit points. The limit in Assumption 1.4 is taken along $\|x\| \to \infty$ within $\mathbb R^n_+$; the paper's convention "without loss of generality $\delta_1 \le \delta_0$" is not part of this definition and is added as a hypothesis in the lemmas that use the exponent $\delta_1$. The Brownian integrands read the state at $x^+$, as the coefficients of (1.1) do; on $\mathbb R^n_+$ this is $x$.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Remark 1.7, p. 7 (Π̃_t), Assumption 1.4, p. 7, Assumption 1.5 and U(ω), p. 8, Theorem 1.3, p. 8 (P^µ_x), Lemma 5.9, p. 26 (K^{k,Δ}_µ), (5.17), p. 24

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Classify_Faces

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify

open EthierKurtz

/-- The random normalized occupation measure `Π̃_t(·) = (1/t) ∫₀ᵗ 1_{X(s) ∈ ·} ds` of the path
`s ↦ X x s ω` (Remark 1.7, p. 7). -/
noncomputable def occ {n : ℕ} {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (t : ℝ) (ω : Ω) : Measure (SDEState n) :=
  (ENNReal.ofReal t)⁻¹ •
    (volume.restrict (Set.Icc (0 : ℝ) t)).map (fun s => X x s.toNNReal ω)

/-- `U(ω)` (p. 8): the weak*-limit set of the family `{Π̃_t(ω), t ≥ 1}`, i.e. the probability
measures `π` with `Π̃_{t_k}(ω) → π` weakly along some sequence `t_k ≥ 1`, `t_k → ∞`. -/
def limitSet {n : ℕ} {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (ω : Ω) : Set (Measure (SDEState n)) :=
  {π | IsProbabilityMeasure π ∧ ∃ ts : ℕ → ℝ, (∀ k, 1 ≤ ts k) ∧ Tendsto ts atTop atTop ∧
    ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occ X x (ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))}

/-- Assumption 1.4 (p. 7): `δ₁ > 0` and
`‖x‖^{δ₁} ∑ᵢ gᵢ²(x) / (1 + ∑ᵢ (|fᵢ(x)| + |gᵢ(x)|²)) → 0` as `‖x‖ → ∞` in `ℝⁿ₊`
(`‖·‖` the `ℓ¹` norm of p. 4). -/
def Assumption14 {n : ℕ} (C : Coeffs n) (δ₁ : ℝ) : Prop :=
  0 < δ₁ ∧
    Tendsto (fun x => l1 x ^ δ₁ * (∑ i, C.g i x ^ 2) / (1 + ∑ i, (|C.f i x| + C.g i x ^ 2)))
      (comap l1 atTop ⊓ 𝓟 (orthant n)) (𝓝 0)

/-- Assumption 1.5 (p. 8): `M² = ∅`, or `max_i λᵢ(ν) > 0` for every `ν ∈ Conv(M²)`. -/
def Assumption15 {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  M2 P C X = ∅ ∨ ∀ ν ∈ conv (M2 P C X), ∃ i, 0 < lyap C i ν

/-- The event of `P^μ_x` (p. 8): `U(ω) = {μ}` and `lim_{t→∞} ln Xᵢ(t)/t = λᵢ(μ) < 0` for every
`i ∈ I^c_μ`. -/
def extinctEvent {n : ℕ} {Ω : Type*} (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (μ : Measure (SDEState n)) : Set Ω :=
  {ω | limitSet X x ω = {μ} ∧ ∀ i, i ∉ supp μ →
    Tendsto (fun t : ℝ≥0 => Real.log (X x t ω i) / t) atTop (𝓝 (lyap C i μ)) ∧ lyap C i μ < 0}

/-- `K^{k,Δ}_μ = {x ∈ ℝⁿ,◦₊ : k⁻¹ ≤ xᵢ ≤ k for i ∈ I_μ, xᵢ < Δ for i ∈ I^c_μ}` (Lemma 5.9, p. 26). -/
def Kbox {n : ℕ} (μ : Measure (SDEState n)) (k : ℕ) (Δ : ℝ) : Set (SDEState n) :=
  {x | x ∈ openOrthant n ∧ (∀ i ∈ supp μ, (k : ℝ)⁻¹ ≤ x i ∧ x i ≤ k) ∧
    ∀ i, i ∉ supp μ → x i < Δ}

/-- The weight `(1 + cᵀx)^δ (1 + ∑ᵢ (|fᵢ(x)| + |gᵢ(x)|²))` of Lemmas 3.3, 5.4 and 5.6. -/
noncomputable def growthWeight {n : ℕ} (C : Coeffs n) (c : SDEState n) (δ : ℝ)
    (x : SDEState n) : ℝ :=
  (1 + ∑ i, c i * x i) ^ δ * (1 + ∑ i, (|C.f i x| + C.g i x ^ 2))

/-- The `j`-th Brownian integrand of `∫ ∑ᵢ cᵢXᵢgᵢ(X)/(1 + cᵀX) dEᵢ` in (5.17): since
`dEᵢ = ∑ⱼ Γⱼᵢ dBⱼ`, it is `∑ᵢ cᵢxᵢgᵢ(x)Γⱼᵢ/(1 + cᵀx)`, read at `x⁺` like the coefficients
of (1.1). -/
noncomputable def itoIntegrand {n : ℕ} (C : Coeffs n) (c : SDEState n) (j : Fin n)
    (x : SDEState n) : ℝ :=
  (∑ i, c i * (posPart x) i * C.g i (posPart x) * C.Γ j i) / (1 + ∑ i, c i * (posPart x) i)

end StochKolmogorov.Classify


