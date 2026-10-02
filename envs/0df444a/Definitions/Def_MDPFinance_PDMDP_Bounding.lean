-- Prove2me | Definitions.Def_MDPFinance_PDMDP_Bounding
-- name    : MDPFinance_PDMDP_Bounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:05:52.396657+00:00
-- url     : https://prove2.me/theorems/7966c91a-a2d7-4bba-a636-c19a6c419841
-- title:
--   Upper bounding functions and the Continuity/Compactness Assumptions (Definition 8.2.4)
-- statement:
--   Definition 8.2.4 introduces an **upper bounding function** $b : E \to \mathbb R_{\ge0}$ for the Piecewise Deterministic Markov Decision Model: constants $c_r,c_Q,c_\varphi \ge 0$ with $r^+(x,u) \le c_rb(x)$, $\int b(z)Q(dz\mid x,u) \le c_Qb(x)$, and (already stated over the *relaxed* control space $R$, not just $A$) $\lambda\int_0^\infty e^{-(\lambda+\beta)t}b(\varphi\mathrm{Rel}^\alpha_t(x))\,dt \le c_\varphi b(x)$. The book's own remark that $b$ is then also an upper bounding function for the discrete-time embedded model with $\alpha_b \le c_Qc_\varphi$ is what lets `theorem_8_2_6` state its hypothesis as `cQ * cφ < 1` in place of an abstractly-defined $\alpha_b$. The **Continuity and Compactness Assumptions** immediately following (U compact; the relaxed flow jointly continuous in $(t,x,\alpha)$; the discounted bounding-function integral continuous in $(x,\alpha)$; the kernel integral upper semicontinuous for every usc $v \in IB_b^+$; $r$ upper semicontinuous) are the standing hypotheses of every theorem in §8.2 from Lemma 8.2.5 onward.
--
--   **Formalization Note.** Continuity of the relaxed flow and of the relaxed control itself is stated against the pointwise/product topology on $\mathbb R \to \mathbb P(U)$ rather than a reconstructed Young topology, per `MDPFinance.PDMDP.PDMDPModel`'s own convention.
--
--   **Moderation note.** The draft bounded `∫ b dQ` and `∫_0^∞ e^{-(λ+β)t} b(φ_t^α(x)) dt` as real Bochner integrals (which return `0` when `b` is not integrable, making the "bound" vacuous), and the continuity-and-compactness conditions used the product/pointwise topology on `R` instead of the Young topology. Now both bounds are Lebesgue integrals of `b ≥ 0`, the bounding-function version uses `|r| ≤ c_r b`, and the assumptions (i)–(v) of §8.2 are stated with `R` carrying the Young topology: `U` compact, `(t,α,x) ↦ φ_t^α(x)` continuous on `t ≥ 0`, `(x,α) ↦ ∫ e^{-(λ+β)t} b(φ_t^α(x)) dt` continuous, `(x,u) ↦ ∫ v dQ(·|x,u)` upper semicontinuous for usc `v ∈ IB_b^+`, `r` upper semicontinuous.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 251, PDF 262, Definition 8.2.4 and the unnumbered Continuity and Compactness Assumptions immediately following it

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U] [OpensMeasurableSpace U]

/-- Definition 8.2.4 (Bäuerle–Rieder, p. 251, PDF 262): a measurable `b : E → ℝ_{≥0}` is an
**upper bounding function** if there are `c_r, c_Q, c_φ ≥ 0` with (i) `r⁺(x,u) ≤ c_r b(x)`,
(ii) `∫ b(z) Q(dz|x,u) ≤ c_Q b(x)`, (iii) `λ ∫_0^∞ e^{-(λ+β)t} b(φ_t^α(x)) dt ≤ c_φ b(x)` for all
`x` and all **relaxed** `α ∈ R` (Lebesgue integrals, `b ≥ 0`). Then `α_b ≤ c_Q c_φ` for the
embedded model. -/
structure IsUpperBoundingFunctionPDMDP (Mk : PDMDPModel E U) (b : E → ℝ) (cr cQ cφ : ℝ) :
    Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcQ : 0 ≤ cQ
  hcφ : 0 ≤ cφ
  hr : ∀ x u, max (Mk.r (x, u)) 0 ≤ cr * b x
  hQ : ∀ x u, ∫⁻ z, ENNReal.ofReal (b z) ∂(Mk.Q (x, u)) ≤ ENNReal.ofReal (cQ * b x)
  hφ : ∀ x (α : ℝ → ProbabilityMeasure U), Measurable α →
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t) * b (Mk.φRel t α x))) ≤
      ENNReal.ofReal (cφ * b x)

/-- A **bounding function** (Bäuerle–Rieder, p. 255, PDF 266: "an upper bounding function with
`r` replaced by `|r|`"). -/
structure IsBoundingFunctionPDMDP (Mk : PDMDPModel E U) (b : E → ℝ) (cr cQ cφ : ℝ) :
    Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcQ : 0 ≤ cQ
  hcφ : 0 ≤ cφ
  hr : ∀ x u, |Mk.r (x, u)| ≤ cr * b x
  hQ : ∀ x u, ∫⁻ z, ENNReal.ofReal (b z) ∂(Mk.Q (x, u)) ≤ ENNReal.ofReal (cQ * b x)
  hφ : ∀ x (α : ℝ → ProbabilityMeasure U), Measurable α →
    (∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t) * b (Mk.φRel t α x))) ≤
      ENNReal.ofReal (cφ * b x)

/-- The **Continuity and Compactness Assumptions** of §8.2 (Bäuerle–Rieder, p. 251, PDF 262),
with `R` carrying the Young topology: (i) `U` compact, (ii) `(t,x,α) ↦ φ_t^α(x)` continuous on
`ℝ₊ × E × R`, (iii) `(x,α) ↦ ∫_0^∞ e^{-(λ+β)t} b(φ_t^α(x)) dt` continuous on `E × R`, (iv)
`(x,u) ↦ ∫ v(z) Q(dz|x,u)` upper semicontinuous for all usc `v ∈ IB_b^+`, (v) `r` upper
semicontinuous. -/
def ContinuityCompactnessAssumptions (Mk : PDMDPModel E U) (b : E → ℝ) : Prop :=
  IsCompact (Set.univ : Set U) ∧
  (letI : TopologicalSpace (ℝ → ProbabilityMeasure U) := youngTopology U;
    ContinuousOn (fun p : ℝ × (ℝ → ProbabilityMeasure U) × E => Mk.φRel p.1 p.2.1 p.2.2)
      {p | 0 ≤ p.1}) ∧
  (letI : TopologicalSpace (ℝ → ProbabilityMeasure U) := youngTopology U;
    Continuous (fun p : E × (ℝ → ProbabilityMeasure U) =>
      ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(Mk.lam + Mk.β) * t) * b (Mk.φRel t p.2 p.1))) ∧
  (∀ v ∈ IBbPlus b, UpperSemicontinuous v →
    UpperSemicontinuous fun p : E × U => erealIntegral (Mk.Q p) v) ∧
  UpperSemicontinuous Mk.r

end MDPFinance.PDMDP


