-- Prove2me | Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDECRef
-- name    : FoundationsRL_DECLowerExamples_constrainedDECRef
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:25.277548+00:00
-- url     : https://prove2.me/theorems/33544036-b819-4ece-b25e-a0091944a731
-- title:
--   Constrained DEC $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)\in[0,\infty]$ for unbounded rewards
-- statement:
--   For a class $\mathcal M$ of models, a reference model $\widehat M$ and a radius $\varepsilon>0$, the **constrained Decision-Estimation Coefficient** is
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M,\widehat M)=\inf_{p\in\Delta(\Pi)}\ \sup_{M\in\mathcal M}\Bigl\{\mathbb E_{\pi\sim p}\bigl[f^M(\pi_M)-f^M(\pi)\bigr]\ \Big|\ \mathbb E_{\pi\sim p}\bigl[D^2_{\mathrm H}(M(\pi),\widehat M(\pi))\bigr]\le\varepsilon^2\Bigr\},
--   $$
--   with the convention (footnote 15) that the value is $0$ if for some $p$ no $M\in\mathcal M$ satisfies the constraint.
--
--   The minimizing player picks a distribution over decisions; the maximizing player picks a model whose observations are statistically close to those of $\widehat M$ under that distribution but which has large regret. Lower bounds on this quantity give lower bounds on the minimax regret (Proposition 28).
--
--   **Formalization Note** The value lies in $[0,\infty]$, and both expectations are lower Lebesgue integrals of $[0,\infty]$-valued functions; they equal the notes' expectations whenever the integrands are measurable. The supremum over an empty set is $0$, which gives footnote 15. $D^2_{\mathrm H}$ is the published squared Hellinger distance, without a factor $1/2$. The published `FoundationsRL.DECLower.constrainedDECRef` takes a real supremum of Bochner integrals, which is the true supremum only for rewards in $[0,1]$; the examples of this mission have Gaussian rewards, so this mission defines the coefficient in $[0,\infty]$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.5.1, p. 104, display and footnote 15

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_hellingerSq
import Definitions.Def_FoundationsRL_DECLowerExamples_suboptGap

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLowerExamples

/-- **Constrained Decision-Estimation Coefficient relative to a reference model, values in `[0, ∞]`**
`dec^c_ε(M, M̂) = inf_{p∈Δ(Π)} sup_{M∈M} { E_{π∼p}[f^M(π_M) − f^M(π)] | E_{π∼p}[D²_H(M(π), M̂(π))] ≤ ε² }`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.5.1, p. 104, with footnote 15.

**Formalization Note.** `p` ranges over all probability measures on the decision space. For each
`p` the supremum is over the members `M` of the class with `E_{π∼p}[D²_H(M(π), M̂(π))] ≤ ε²`, the
squared Hellinger distance being the published `FoundationsRL.DECLower.hellingerSq` (no factor
`1/2`). Both expectations are lower Lebesgue integrals of `[0, ∞]`-valued functions, so they equal
the notes' expectations whenever the integrands are measurable, and no integrability is needed.
All values are in `ℝ≥0∞`, so the supremum and infimum are the true ones even for unbounded rewards
(the published `FoundationsRL.DECLower.constrainedDECRef` takes a real `sSup`, which is the true
supremum only for rewards in `[0, 1]`). Footnote 15: the supremum over an empty set is `0` in
`ℝ≥0∞`, so if some `p` leaves no feasible model the infimum is `0`, as the footnote prescribes.
`ε` is the notes' radius `ε > 0`; for `ε ≤ 0` the value is that at `|ε|`. -/
noncomputable def constrainedDECRef {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (ε : ℝ) (Ms : Set (Kernel D (ℝ × O))) (Mhat : Kernel D (ℝ × O)) : ℝ≥0∞ :=
  ⨅ p : ProbabilityMeasure D, ⨆ M ∈ Ms,
    ⨆ (_ : ∫⁻ d, FoundationsRL.DECLower.hellingerSq (M d) (Mhat d) ∂(p : Measure D) ≤
        ENNReal.ofReal (ε ^ 2)),
      ∫⁻ d, suboptGap M d ∂(p : Measure D)

end FoundationsRL.DECLowerExamples


