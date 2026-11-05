-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_normG
-- name    : BauerleRiederMDP_LPDuality_normG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:01.492075+00:00
-- url     : https://prove2.me/theorems/4dc09510-fb25-415c-a1cc-8052f02cfb88
-- title:
--   Grid weighted supremum norm $\|v\|_G$
-- statement:
--   For a grid scheme with grid bounding function $b_G$ and $v:E\to\mathbb R$,
--   $$
--   \|v\|_G:=\sup_{x\in E}\frac{|v(x)|}{b_G(x)}.
--   $$
--   Theorem 7.5.12 measures the error of value iteration on the grid in this norm.
--
--   **Formalization Note** The value lies in $[0,\infty]$, so an unbounded quotient gives $\infty$ rather than a default real value.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.3, p.221 (PDF 232), ‖v‖_G := sup_{x∈E} |v(x)|/b_G(x)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LPDuality_GridScheme
import Definitions.Def_BauerleRiederMDP_LPDuality_gridBound

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LPDuality

/-- The grid weighted supremum norm (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), §7.5.3, p.221, PDF 232): `‖v‖_G := sup_{x ∈ E} |v(x)| / b_G(x)`.

**Formalization Note** The value lies in `[0, ∞]` (`ℝ≥0∞`), so an unbounded quotient gives `∞`
rather than the junk value `0` of a real supremum. -/
noncomputable def normG {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] {S : Set V} (sch : GridScheme S) (b : S → ℝ) (v : S → ℝ) : ENNReal :=
  ⨆ x, ENNReal.ofReal (|v x| / gridBound sch b x)

end BauerleRiederMDP.LPDuality


