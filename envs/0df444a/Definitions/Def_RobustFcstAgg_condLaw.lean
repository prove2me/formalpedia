-- Prove2me | Definitions.Def_RobustFcstAgg_condLaw
-- name    : RobustFcstAgg_condLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:09.244055+00:00
-- url     : https://prove2.me/theorems/3686e078-a620-493f-8c04-cebf1da9fdf6
-- title:
--   Conditional law $\mathcal L_{\mathcal D}(\mathcal R\mid S_i)$ on a fibre
-- statement:
--   For a finite family $\mathcal R=(R_v)_v$ of random variables, an expert $i$ and a value $s$ of $S_i$, this is the law of $(R_v)_v$ given $S_i=s$: the image of the law of the hidden signals $y$ under $y\mapsto (R_v(s,y))_v$.
--
--   **Formalization Note** The signals are independent, so this is a regular version of the conditional law, defined for every $s$.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, Condition 1, p.25

import Mathlib
import Definitions.Def_RobustFcstAgg_Signals
import Definitions.Def_RobustFcstAgg_glue
import Definitions.Def_RobustFcstAgg_InfoStruct_restLaw
open MeasureTheory

namespace RobustFcstAgg

/-- **Conditional law `L_D(R | S_i)` on a fibre.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, Condition 1, p.25: the law of the scored variables
`R = (R v)_v` given `S_i = s`.

**Formalization Note.** Signals are independent, so this is the image of the law of the hidden signals under
`y ↦ (R v (glue i s y))_v`: a regular version of the conditional law, defined for every `s`. `Measure.map` is
the zero measure if that map is not a.e.-measurable; on a DAG, Condition 1 rules this out for a.e. `s`, by
induction from `Y`. -/
noncomputable def condLaw {n : ℕ} (D : InfoStruct n) (i : Fin n) {N : Type}
    (R : N → Signals n → ℝ) (s : AgentSig i → ℝ) : Measure (N → ℝ) :=
  (D.restLaw i).map fun y v => R v (glue i s y)

end RobustFcstAgg


