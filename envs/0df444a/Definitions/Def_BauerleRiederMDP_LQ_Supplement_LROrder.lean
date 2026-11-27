-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_LROrder
-- name    : BauerleRiederMDP_LQ_Supplement_LROrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:21:13.646797+00:00
-- url     : https://prove2.me/theorems/ddbc6f56-8fb6-4fbd-88f5-740ed5d78280
-- title:
--   The likelihood ratio order
-- statement:
--   **The likelihood ratio order** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition B.3.5, p.360, PDF 366): $\mu  \le _lr \nu $ if $\mu $ and $\nu $ have densities $f_\mu $, $f_\nu $ with respect to some dominating measure such that $f_\mu (t) f_\nu (s) \le  f_\mu (s) f_\nu (t)$ for all $s \le  t$.
--
--   **Formalization Note.** Stated for measures on a preordered measurable space $\Theta $; the dominating measure is σ-finite and the densities are measurable and $[0, \infty ]$-valued (`withDensity`).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition B.3.5, p.360, PDF 366

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The likelihood ratio order** (Bäuerle & Rieder, *Markov Decision Processes with Applications
to Finance* (2011), Definition B.3.5, p.360, PDF 366): `μ ≤_lr ν` if `μ` and `ν` have densities
`f_μ`, `f_ν` with respect to some dominating measure such that `f_μ(t) f_ν(s) ≤ f_μ(s) f_ν(t)` for
all `s ≤ t`.

**Formalization Note.** Stated for measures on a preordered measurable space `Θ`; the dominating
measure is σ-finite and the densities are measurable and `[0, ∞]`-valued (`withDensity`). -/
def LROrder {Θ : Type*} [MeasurableSpace Θ] [Preorder Θ] (μ ν : Measure Θ) : Prop :=
  ∃ (dom : Measure Θ) (f g : Θ → ℝ≥0∞), SigmaFinite dom ∧ Measurable f ∧ Measurable g ∧
    μ = dom.withDensity f ∧ ν = dom.withDensity g ∧ ∀ s t : Θ, s ≤ t → f t * g s ≤ f s * g t

end BauerleRiederMDP.LQ.Supplement


