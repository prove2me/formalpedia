-- Prove2me | Definitions.Def_MDPFinance_PDMDP_Embedding
-- name    : MDPFinance_PDMDP_Embedding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:05:41.644547+00:00
-- url     : https://prove2.me/theorems/b9d6d0df-988b-45be-9565-49915325f095
-- title:
--   The embedded discrete-time reward r' and kernel Q' (Eq. 8.4-8.5, 8.7)
-- statement:
--   Section 8.2 embeds the continuous-time control problem into a discrete-time Markov Decision Model $(E,A,Q',r')$ by looking only at the post-jump states. The reward function $r'(x,\alpha) := \int_0^\infty e^{-(\beta+\lambda)t}r(\varphi^\alpha_t(x),\alpha_t)\,dt$ (Eq. (8.5)) and its relaxed extension $r'(x,\alpha) := \int_0^\infty e^{-(\beta+\lambda)t}\int_U r(\varphi\mathrm{Rel}^\alpha_t(x),u)\,\alpha_t(du)\,dt$ (Eq. (8.7)) are direct integrals against the model's own flow and reward, and are given as `def`s. The transition kernel $Q'(B\mid x,\alpha) := \lambda\int_0^\infty e^{-(\lambda+\beta)t}Q(B\mid\varphi^\alpha_t(x),\alpha_t)\,dt$ (Eq. (8.4)) and its relaxed extension (Eq. (8.7)) are genuine measures on $E$ for each $(x,\alpha)$; rather than literally constructing them as a mixture of pushforward measures (a routine but heavy argument adding no content beyond the formula itself), `EmbeddedKernel`/`EmbeddedKernelRelaxed` bundle $Q'$ as *data* satisfying its defining identity on every measurable set's mass, matching this book's series' convention for a quantity characterized by, rather than literally built from, a formula.
--
--   **Formalization Note.** `Qprime`/`QprimeR`'s existence (a genuine measure realizing the stated formula) is itself part of the book's own construction (§8.2's opening paragraphs); taking it as hypothesis data does not weaken any theorem using it, since every theorem in this chunk that cites $Q'$ already assumes such data is supplied.
--
--   **Moderation note.** The draft's embedded reward was a real Bochner integral over `[0,∞)` (junk `0` when `e^{-(β+λ)t} r(φ_t^α(x), α_t)` is not integrable) and its embedded kernel `Q'` was an arbitrary map carrying no measurability and no link to the formula `Q'(B|x,α) = ∫_0^∞ λ e^{-(λ+β)t} Q(B|φ_t^α(x), α_t) dt`. Now `r'(x,α)` and the relaxed `r'(x,α)` are `[-∞,∞]`-valued integrals over `(0,∞)`, and an embedded kernel is a *Markov kernel-valued* structure whose measure is pinned to the book's formula (as a Lebesgue integral) with `Q'` measurable.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 247, PDF 258, Eq. (8.4)-(8.5); p. 250-251, PDF 261-262, Eq. (8.7)

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U]

/-- `r'_{rew}(x,α) := ∫_0^∞ e^{-(β+λ)t} rew(φ_t^α(x),α_t) dt ∈ [-∞,∞]` for a one-stage reward rate
`rew` (`rew = r` gives Eq. (8.5); `rew = r⁺` the positive part used by the Integrability
Assumption). -/
noncomputable def PDMDPModel.rprimeWith (Mk : PDMDPModel E U) (rew : E × U → ℝ)
    (xα : E × ControlFn U) : EReal :=
  erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
    ((Real.exp (-(Mk.β + Mk.lam) * t) * rew (Mk.φ t xα.2.1 xα.1, xα.2.1 t) : ℝ) : EReal)

/-- `r'(x,α) := ∫_0^∞ e^{-(β+λ)t} r(φ_t^α(x),α_t) dt` (Bäuerle–Rieder, Eq. (8.5), p. 247, PDF
258), the reward of the embedded discrete-time model (nonrelaxed controls), in `[-∞,∞]`. -/
noncomputable def PDMDPModel.rprime (Mk : PDMDPModel E U) (xα : E × ControlFn U) : EReal :=
  Mk.rprimeWith Mk.r xα

/-- The relaxed analogue of `rprimeWith`: `∫_0^∞ e^{-(β+λ)t} ∫_U rew(φRel_t^α(x),u) α_t(du) dt`
(Eq. (8.7)). -/
noncomputable def PDMDPModel.rprimeRelaxedWith (Mk : PDMDPModel E U) (rew : E × U → ℝ)
    (xα : E × RelaxedControlFn U) : EReal :=
  erealIntegral (volume.restrict (Set.Ioi (0 : ℝ))) fun t =>
    ((Real.exp (-(Mk.β + Mk.lam) * t) : ℝ) : EReal) *
      erealIntegral (xα.2.1 t).toMeasure fun u => ((rew (Mk.φRel t xα.2.1 xα.1, u) : ℝ) : EReal)

/-- `r'(x,α)` for relaxed controls (Bäuerle–Rieder, Eq. (8.7), p. 250, PDF 261). -/
noncomputable def PDMDPModel.rprimeRelaxed (Mk : PDMDPModel E U) (xα : E × RelaxedControlFn U) :
    EReal :=
  Mk.rprimeRelaxedWith Mk.r xα

/-- The **embedded discrete-time kernel** `Q'` (nonrelaxed controls), bundled as data: a
measurable family of measures (a kernel) satisfying `Q'(B|x,α) = λ ∫_0^∞ e^{-(λ+β)t}
Q(B|φ_t^α(x),α_t) dt` (Bäuerle–Rieder, Eq. (8.4), p. 247, PDF 258) on every measurable `B`. -/
structure EmbeddedKernel (Mk : PDMDPModel E U) where
  Qprime : E × ControlFn U → Measure E
  hQprime_meas : Measurable Qprime
  hQprime : ∀ xα (B : Set E), MeasurableSet B →
    Qprime xα B = ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t)) *
        Mk.Q (Mk.φ t xα.2.1 xα.1, xα.2.1 t) B

/-- The relaxed analogue of `EmbeddedKernel`: `Q'(B|x,α) = λ ∫_0^∞ e^{-(λ+β)t} ∫_U
Q(B|φRel_t^α(x),u) α_t(du) dt` (Bäuerle–Rieder, Eq. (8.7), p. 250, PDF 261). -/
structure EmbeddedKernelRelaxed (Mk : PDMDPModel E U) where
  QprimeR : E × RelaxedControlFn U → Measure E
  hQprimeR_meas : Measurable QprimeR
  hQprimeR : ∀ xα (B : Set E), MeasurableSet B →
    QprimeR xα B = ∫⁻ t in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (Mk.lam * Real.exp (-(Mk.lam + Mk.β) * t)) *
        ∫⁻ u, Mk.Q (Mk.φRel t xα.2.1 xα.1, u) B ∂(xα.2.1 t).toMeasure

end MDPFinance.PDMDP


