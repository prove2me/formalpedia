-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_alphaG
-- name    : BauerleRiederMDP_LPDuality_alphaG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:51.033399+00:00
-- url     : https://prove2.me/theorems/fde706aa-7c41-474b-b9c3-111d3bba0bb2
-- title:
--   Module $\alpha_G$ of the grid bounding function
-- statement:
--   For a grid scheme with grid bounding function $b_G$,
--   $$
--   \alpha_G:=\sup_{(x,a)\in D}\frac{\int b_G(y)\,Q(dy\mid x,a)}{b_G(x)}.
--   $$
--   When $\beta\alpha_G<1$ the grid operator $\mathcal T_G$ is a contraction with modulus $\beta\alpha_G$ for $\|\cdot\|_G$.
--
--   **Formalization Note** The value lies in $[0,\infty]$, with the integral of the nonnegative function $b_G$ taken as a lower Lebesgue integral. The supremum ranges over $D$, where $Q(\cdot\mid x,a)$ is defined, as for $\alpha_b$ in Definition 7.3.1.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Proposition 7.5.11, p.222 (PDF 233), α_G := sup_{(x,a)} ∫ b_G(y)Q(dy|x,a)/b_G(x)

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_BauerleRiederMDP_LPDuality_GridScheme
import Definitions.Def_BauerleRiederMDP_LPDuality_gridBound

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- The module of the grid bounding function (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), proof of Proposition 7.5.11, p.222, PDF 233):
`α_G := sup_{(x,a)} ∫ b_G(y) Q(dy|x, a) / b_G(x)`, the supremum over `(x, a) ∈ D`.

**Formalization Note** The value lies in `[0, ∞]` (`ℝ≥0∞`) and the integral is the lower Lebesgue
integral of the nonnegative function `b_G`, so an unbounded ratio gives `∞`, not a junk real value.
The supremum ranges over `D`, where `Q(·|x, a)` is defined in the book (as for `α_b`, Definition
7.3.1). -/
noncomputable def alphaG {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [MeasurableSpace A] {S : Set V} (M : MarkovDecisionModel S A)
    (sch : GridScheme S) (b : S → ℝ) : ENNReal :=
  ⨆ xa ∈ M.D, (∫⁻ y, ENNReal.ofReal (gridBound sch b y) ∂(M.Q xa)) /
    ENNReal.ofReal (gridBound sch b xa.1)

end BauerleRiederMDP.LPDuality


