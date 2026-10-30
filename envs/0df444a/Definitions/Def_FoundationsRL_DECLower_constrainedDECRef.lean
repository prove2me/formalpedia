-- Prove2me | Definitions.Def_FoundationsRL_DECLower_constrainedDECRef
-- name    : FoundationsRL_DECLower_constrainedDECRef
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:13:11.015757+00:00
-- url     : https://prove2.me/theorems/8e3da149-8a6c-4c10-815b-a50ac46f97fc
-- title:
--   Constrained DEC $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)$ relative to a reference model
-- statement:
--   For a class $\mathcal M$ of models, a reference model $\widehat M$ and a radius $\varepsilon>0$, the **constrained Decision-Estimation Coefficient** is
--
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)=\inf_{p\in\Delta(\Pi)}\ \sup_{M\in\mathcal M}\Bigl\{\mathbb E_{\pi\sim p}\bigl[f^M(\pi_M)-f^M(\pi)\bigr]\ \Big|\ \mathbb E_{\pi\sim p}\bigl[D^2_{\mathrm H}(M(\pi),\widehat M(\pi))\bigr]\le\varepsilon^2\Bigr\},
--   $$
--
--   with the convention (footnote 15) that the value is $0$ if for some $p$ no $M\in\mathcal M$ satisfies the constraint.
--
--   The infimum player picks a decision distribution; the supremum player picks a model that is statistically close to $\widehat M$ under that distribution but has large regret.
--
--   **Formalization Note** The supremum of the empty set is $0$ in Lean's reals, and for a class of models every feasible value is nonnegative, so a single empty constraint set makes the infimum $0$: this is footnote 15. The expectation of the Hellinger distance is a Lebesgue integral in $[0,\infty]$; it is the notes' expectation whenever the integrand is measurable.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.5.1, p. 104, and footnote 15

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_gap
import Definitions.Def_FoundationsRL_DECLower_hellingerSq

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Constrained Decision-Estimation Coefficient relative to a reference model**
`dec^c_ε(M, M̂) = inf_{p∈Δ(Π)} sup_{M∈M} { E_{π∼p}[f^M(π_M) − f^M(π)] | E_{π∼p}[D²_H(M(π), M̂(π))] ≤ ε² }`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.5.1, p. 104, with footnote 15.

**Formalization Note.** `p` ranges over the probability measures on the decision space. For
each `p` the supremum is over the members `M` of the class with
`∫⁻ D²_H(M(π), M̂(π)) dp(π) ≤ ε²`. Footnote 15 sets the value to zero when for some `p` that set
is empty: here the real `sSup ∅ = 0`, and every feasible value is `≥ 0` for a class of models
(`IsModel`, so `g^M ≥ 0`), hence one empty constraint set makes the infimum `0` — exactly the
footnote, with no separate case split. For a class of models every value lies in `[0, 1]`, so the
`sSup` and `⨅` are over bounded sets. The expectation of the `ℝ≥0∞`-valued Hellinger distance is a
lower Lebesgue integral; it equals the paper's expectation whenever
`π ↦ D²_H(M(π), M̂(π))` is measurable (e.g. countably generated observation space). -/
noncomputable def constrainedDECRef {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (ε : ℝ) (Ms : Set (Kernel D (ℝ × O))) (Mhat : Kernel D (ℝ × O)) : ℝ :=
  ⨅ p : ProbabilityMeasure D, sSup ((fun M => ∫ d, gap M d ∂(p : Measure D)) ''
    {M | M ∈ Ms ∧ ∫⁻ d, hellingerSq (M d) (Mhat d) ∂(p : Measure D) ≤ ENNReal.ofReal (ε ^ 2)})

end FoundationsRL.DECLower


