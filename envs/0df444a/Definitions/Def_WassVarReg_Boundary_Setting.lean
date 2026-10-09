-- Prove2me | Definitions.Def_WassVarReg_Boundary_Setting
-- name    : WassVarReg_Boundary_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:49.301978+00:00
-- url     : https://prove2.me/theorems/50edd7cd-4428-44f3-be2a-03270b4bfe63
-- title:
--   pp. 4–8, ec4 — boundary gap (ρ − d(z, D))₊, class I_ρ, Rademacher complexity E_⊗[ℜ_n(H)], Assumption 3 (bounded density)
-- statement:
--   Let $(\mathcal Z, d)$ be a metric space with its Borel $\sigma$-algebra, $\mathcal F$ a set of real functions (losses) on $\mathcal Z$, and for each $f \in \mathcal F$ let $\mathcal D_f \subseteq \mathcal Z$ be a set (in the paper, the union of the intersections of the closures of the pieces of a piecewise smooth $f$, Assumption 1). For $z \in \mathcal Z$ and $D \subseteq \mathcal Z$ write $d(z, D) = \inf_{\tilde z \in D} d(z, \tilde z)$, with $d(z, \varnothing) = +\infty$.
--
--   1. The **boundary gap** at radius $\rho$ is $(\rho - d(z, D))_+$; it vanishes when $D = \varnothing$.
--   2. The **near indicator** is $\mathbf 1\{d(z, D) < \rho\}$, and the **indicator class** is
--   $$\mathcal I_\rho = \bigl\{ z \mapsto \mathbf 1\{d(z, \mathcal D_f) < \rho\} : f \in \mathcal F,\ \mathcal D_f \ne \varnothing \bigr\}.$$
--   3. For a class $\mathcal H$ of real functions and a sample $z_1, \dots, z_n$, the **empirical Rademacher complexity** is
--   $$\mathfrak R_n(\mathcal H) = \mathbb E_\sigma\Bigl[\sup_{h \in \mathcal H} \frac1n \sum_{i=1}^n \sigma_i h(z_i)\Bigr],$$
--   where $\sigma_1, \dots, \sigma_n$ are i.i.d. signs with $\mathbb P\{\sigma_i = \pm 1\} = \tfrac12$. The **Rademacher complexity** of $\mathcal H$ with respect to $P$ for sample size $n$ is $\mathbb E_\otimes[\mathfrak R_n(\mathcal H)]$, the expectation under the $n$-fold product $P^{\otimes n}$ of the sample.
--   4. The **uniform deviation** $\sup_{h \in \mathcal H}\{\mathbb E_{P_n}[h] - \mathbb E_P[h]\}$ and the **double-sample deviation** $\sup_{h \in \mathcal H} \frac1n\sum_i (h(z_i) - h(z_i'))$ are the random variables of the McDiarmid and symmetrization steps; the class $\mathcal H$ is called **Rademacher-measurable** at $(n, P)$ when these two and the empirical Rademacher complexity are measurable functions of the sample(s).
--   5. **Assumption 3 (bounded density)** holds when
--   $$\limsup_{\delta \downarrow 0}\ \sup_{f \in \mathcal F:\ \mathcal D_f \ne \varnothing} \frac{P\{z : 0 < d(z, \mathcal D_f) < \delta\}}{\delta} < \infty.$$
--
--   These are the objects of the high-probability bound Theorem 1(III) on the empirical mass of the data near the non-smooth points of the losses.
--
--   **Formalization Note** The distance to a set is the extended distance `Metric.infEDist` ($+\infty$ on $\varnothing$), so the boundary gap is $0$ and the near indicator is $0$ when $\mathcal D_f = \varnothing$. The expectation over signs is the uniform average over $\{\pm1\}^n$. Suprema over a class are real suprema: they are genuine suprema for classes with values in $[0, M]$, the only classes used, and $0$ for an empty class. The Rademacher complexity is a Bochner integral, which equals the expectation when the empirical Rademacher complexity is measurable (it is bounded); every theorem using it assumes Rademacher-measurability, which the paper leaves implicit and which holds for countable classes. Assumption 3 is computed in $[0, \infty]$, with $\delta \downarrow 0$ the right neighbourhood filter of $0$. The sample law $P^{\otimes n}$ is the published `MinimaxWass.DataDep.sampleLaw`.
-- source:
--   Gao, Chen & Kleywegt, arXiv:1712.06050 (2020-10-30 version), Notation P_⊗/E_⊗ (p. 4), Assumption 1's D_f (p. 6), Assumption 3 (p. 7), (1) and Rademacher complexity (p. 8), proof of Lemma EC.5 (p. ec4)

import Mathlib
import Definitions.Def_MinimaxWass_DataDep_Setting
import Definitions.Def_WassVarReg_PInf_Setting

open MeasureTheory Filter Topology
open scoped ENNReal

namespace WassVarReg.Boundary

/-- The indicator `1{d(z, D) < ρ}` of p. 8, (1), with `d(z, D)` as in `boundaryGap`. -/
noncomputable def nearIndicator {Z : Type*} [MetricSpace Z]
    (ρ : ℝ) (D : Set Z) (z : Z) : ℝ := by
  classical
  exact if Metric.infEDist z D < ENNReal.ofReal ρ then 1 else 0

/-- The class `I_ρ = {z ↦ 1{d(z, D_f) < ρ} : f ∈ F, D_f ≠ ∅}` of p. 8, (1).
`D f` is the set `D_f` of Assumption 1 attached to the loss `f`. -/
def indicatorClass {Z : Type*} [MetricSpace Z]
    (ρ : ℝ) (F : Set (Z → ℝ)) (D : (Z → ℝ) → Set Z) : Set (Z → ℝ) :=
  {h | ∃ f ∈ F, (D f).Nonempty ∧ h = nearIndicator ρ (D f)}

/-- The empirical Rademacher complexity `ℜ_n(H) = E_σ[sup_{h ∈ H} (1/n) Σ_i σ_i h(z_i)]` of p. 8,
at the sample `ω = (z_1, …, z_n)`. `E_σ` over i.i.d. uniform signs is the average over
`σ : Fin n → Bool` (`true ↦ +1`, `false ↦ -1`). The real `⨆` is bounded above for every class with
values in `[0, M]`, the only classes it is used for; for an empty class it is `0`. -/
noncomputable def empRademacher {Z : Type*} {n : ℕ}
    (H : Set (Z → ℝ)) (ω : Fin n → Z) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ σ : Fin n → Bool,
    ⨆ h : H, (1 / (n : ℝ)) * ∑ i : Fin n, (if σ i then (1 : ℝ) else -1) * (h : Z → ℝ) (ω i)

/-- The Rademacher complexity `E_⊗[ℜ_n(H)]` of `H` with respect to `P` for sample size `n` (p. 8):
the expectation of `empRademacher H` under the `n`-fold product `P^{⊗n}` (p. 4). The Bochner integral
is the expectation whenever `empRademacher H` is measurable (`RademacherMeasurable`), since it is
bounded for classes with values in `[0, M]`. -/
noncomputable def rademacher {Z : Type*} [MeasurableSpace Z]
    (n : ℕ) (P : ProbabilityMeasure Z) (H : Set (Z → ℝ)) : ℝ :=
  ∫ ω, empRademacher H ω ∂(MinimaxWass.DataDep.sampleLaw n P)

/-- The uniform deviation `sup_{h ∈ H} {E_{P_n}[h] - E_P[h]}` of the proof of Lemma EC.5, p. ec4. -/
noncomputable def uniformDeviation {Z : Type*} [MeasurableSpace Z] {n : ℕ}
    (P : ProbabilityMeasure Z) (H : Set (Z → ℝ)) (ω : Fin n → Z) : ℝ :=
  ⨆ h : H, ((1 / (n : ℝ)) * ∑ i : Fin n, (h : Z → ℝ) (ω i) - ∫ z, (h : Z → ℝ) z ∂(P : Measure Z))

/-- The double-sample deviation `sup_{h ∈ H} (1/n) Σ_i (h(z_i) - h(z'_i))` of the standard
symmetrization argument invoked in the proof of Lemma EC.5, p. ec4, at a sample and a ghost sample. -/
noncomputable def ghostDeviation {Z : Type*} {n : ℕ}
    (H : Set (Z → ℝ)) (ωω' : (Fin n → Z) × (Fin n → Z)) : ℝ :=
  ⨆ h : H, (1 / (n : ℝ)) * ∑ i : Fin n, ((h : Z → ℝ) (ωω'.1 i) - (h : Z → ℝ) (ωω'.2 i))

/-- Measurability guard (added technical hypothesis, implicit in the paper): the uniform deviation,
the empirical Rademacher complexity and the double-sample deviation of `H` at sample size `n` are
measurable. It holds, for instance, for countable `H`. -/
def RademacherMeasurable {Z : Type*} [MeasurableSpace Z]
    (n : ℕ) (P : ProbabilityMeasure Z) (H : Set (Z → ℝ)) : Prop :=
  Measurable (uniformDeviation (n := n) P H) ∧
  Measurable (empRademacher (n := n) H) ∧
  Measurable (ghostDeviation (n := n) H)

/-- Assumption 3 (Bounded density), p. 7:
`limsup_{δ ↓ 0} sup_{f ∈ F : D_f ≠ ∅} P{z : 0 < d(z, D_f) < δ} / δ < ∞`, computed in `ℝ≥0∞`,
with `δ ↓ 0` the filter `𝓝[>] 0`. -/
def Assumption3 {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    (P : ProbabilityMeasure Z) (F : Set (Z → ℝ)) (D : (Z → ℝ) → Set Z) : Prop :=
  Filter.limsup (fun δ : ℝ => ⨆ f ∈ F, ⨆ (_ : (D f).Nonempty),
      (P : Measure Z) {z | 0 < Metric.infEDist z (D f) ∧
        Metric.infEDist z (D f) < ENNReal.ofReal δ} / ENNReal.ofReal δ)
    (𝓝[>] (0 : ℝ)) < ⊤

end WassVarReg.Boundary


