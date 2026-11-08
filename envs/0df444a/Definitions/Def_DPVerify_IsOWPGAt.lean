-- Prove2me | Definitions.Def_DPVerify_IsOWPGAt
-- name    : DPVerify_IsOWPGAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:10.287391+00:00
-- url     : https://prove2.me/theorems/cd30a535-20fd-4a2d-84f9-7caf2bec2683
-- title:
--   One-way perfect generalization at a distribution $D$
-- statement:
--   A randomized algorithm $\mathcal A:\mathcal X^m\to\mathcal Y$ satisfies the **$(\beta,\varepsilon,\delta)$-one-way perfect generalization condition at $D$** if there is a probability distribution $\mathrm{Sim}_D$ on $\mathcal Y$ such that, with probability at least $1-\beta$ over an i.i.d. sample $S\sim D^m$, every measurable output set $O\subseteq\mathcal Y$ satisfies
--
--   $$
--   \Pr[\mathcal A(S)\in O]\;\le\;e^{\varepsilon}\,\Pr_{\mathrm{Sim}_D}[O]+\delta .
--   $$
--
--   The algorithm is **$(\beta,\varepsilon,\delta)$-one-way perfectly generalizing** (Definition 2.4) if this holds at every distribution $D$ on $\mathcal X$; the module also defines that predicate. For most samples, the output of a one-way perfectly generalizing algorithm looks like a draw from a fixed simulator that does not see the sample.
--
--   **Formalization Note** "With probability at least $1-\beta$ over $S$" is encoded by a measurable set of good samples of $D^m$-probability at least $1-\beta$ on which the inequality holds for every $O$.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.4, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_DPVerify_RandAlg

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ}

/-- One-way perfect generalization at the distribution `D` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.4, p.5 = PDF p.8):
there is a probability distribution `Sim_D` on `Y` such that, with probability at least `1 − β`
over `S ∼ D^m`, every measurable output set `O` satisfies `Pr[A(S) ∈ O] ≤ e^ε Pr_{Sim_D}[O] + δ`.

**Formalization Note** "With probability at least `1 − β` over the draw of `S`" is encoded by a
measurable set `G` of good samples with `D^m(G) ≥ 1 − β` on which the inequality holds for
every `O`. Probabilities are in `ℝ≥0∞`. -/
def IsOWPGAt (A : RandAlg X Y m) (D : ProbabilityMeasure X) (β ε δ : ℝ) : Prop :=
  ∃ Sim : Measure Y, IsProbabilityMeasure Sim ∧
    ∃ G : Set (Fin m → X), MeasurableSet G ∧
      ENNReal.ofReal (1 - β) ≤ Measure.pi (fun _ : Fin m => (D : Measure X)) G ∧
      ∀ S ∈ G, ∀ O : Set Y, MeasurableSet O →
        A.law S O ≤ ENNReal.ofReal (Real.exp ε) * Sim O + ENNReal.ofReal δ

/-- `(β, ε, δ)`-one-way perfect generalization (Definition 2.4, p.5): `IsOWPGAt` at every
probability distribution `D` on `X`. -/
def IsOWPG (A : RandAlg X Y m) (β ε δ : ℝ) : Prop :=
  ∀ D : ProbabilityMeasure X, IsOWPGAt A D β ε δ

end DPVerify


