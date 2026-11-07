-- Prove2me | Definitions.Def_PolySampIso_Divergences
-- name    : PolySampIso_Divergences
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:23.349759+00:00
-- url     : https://prove2.me/theorems/a77c74e1-cb81-49f0-8a3b-0b2493d63b0b
-- title:
--   Total variation distance, χ²-divergence and essential oscillation
-- statement:
--   For probability measures $\mu,\nu$ on a measurable space, the **total variation distance** is
--
--   $$\mathrm{TV}(\mu,\nu)=\sup_{B\ \text{measurable}}|\mu(B)-\nu(B)|,$$
--
--   which equals $\tfrac12\int|d\mu-d\nu|$. The **$\chi^2$-divergence** is
--
--   $$\chi^2(\mu\|\nu)=\mathbb E_\nu\Big[\Big(\frac{d\mu}{d\nu}-1\Big)^2\Big]\in[0,\infty]$$
--
--   when $\mu\ll\nu$, and $+\infty$ otherwise. For a bounded function $f$, the **oscillation** is $\mathrm{osc}(f)=\operatorname{ess\,sup}f-\operatorname{ess\,inf}f$ with respect to the measure in context. The normalization of a finite nonzero measure $\mu$ is $\mu/\mu(\text{whole space})$.
--
--   These are the distances in which every guarantee of the paper is stated: warm starts are $\chi^2$ bounds, outputs are TV bounds, and the defect terms of §5 are multiples of $\mathrm{osc}(h)^2$.
--
--   **Formalization Note** $\chi^2$ takes values in $\mathbb R_{\ge0}\cup\{\infty\}$ and is $\infty$ off absolute continuity, so a hypothesis $\chi^2\le\beta$ with $\beta$ finite forces $\mu\ll\nu$.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.1, p.8 (PDF p.10); osc: §5.2, p.42 (PDF p.44)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace PolySampIso

/-!
# Total variation, χ²-divergence and oscillation

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), §2.1, p.8 (PDF p.10): "We use the following
distances between µ, ν ∈ P(X) with µ ≪ ν. The χ2-divergence is χ2(µ∥ν) := Eν[(dµ/dν − 1)²] and
their TV distance is TV(µ, ν) := ½ ∫_X |dµ − dν|." §5.2, p.42 (PDF p.44): "osc(f) := ess sup f −
ess inf f."

**Formalization Note.**
* `tvDist μ ν` is `sup_B |μ(B) − ν(B)|` over measurable `B`; for probability measures this equals
  `½ ∫ |dμ − dν|`. It is used only for probability measures (the supremum is then of a family
  bounded by `1`, so it is not a junk value).
* `chiSq μ ν` takes values in `ℝ≥0∞`: it is `∫ (dμ/dν − 1)² dν` when `μ ≪ ν` (possibly `∞`) and
  `∞` when `μ` is not absolutely continuous with respect to `ν`. So a hypothesis `χ² ≤ β` with
  `β` finite forces `μ ≪ ν`, as the paper intends.
* `osc f μ` is the essential oscillation with respect to `μ` (`essSup`, `essInf`), used only for
  bounded `f`.
* `normalize μ = μ(univ)⁻¹ • μ` turns a finite nonzero measure into a probability measure.
-/

/-- Total variation distance `TV(μ, ν) = sup_B |μ(B) − ν(B)|`, `B` measurable. -/
noncomputable def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ⨆ B : {B : Set α // MeasurableSet B}, |μ.real B.1 - ν.real B.1|

/-- The χ²-divergence `χ²(μ∥ν) = E_ν[(dμ/dν − 1)²]` if `μ ≪ ν`, and `∞` otherwise. -/
noncomputable def chiSq {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
  open Classical in
  if μ ≪ ν then ∫⁻ x, ‖(μ.rnDeriv ν x).toReal - 1‖ₑ ^ 2 ∂ν else ⊤

/-- The essential oscillation `osc(f) = ess sup f − ess inf f` with respect to `μ`. -/
noncomputable def osc {α : Type*} [MeasurableSpace α] (f : α → ℝ) (μ : Measure α) : ℝ :=
  essSup f μ - essInf f μ

/-- The normalization `μ(univ)⁻¹ • μ` of a measure. -/
noncomputable def normalize {α : Type*} [MeasurableSpace α] (μ : Measure α) : Measure α :=
  (μ Set.univ)⁻¹ • μ

end PolySampIso


