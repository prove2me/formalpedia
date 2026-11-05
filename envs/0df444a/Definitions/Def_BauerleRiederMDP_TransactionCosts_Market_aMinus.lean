-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aMinus
-- name    : BauerleRiederMDP_TransactionCosts_Market_aMinus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:00.826727+00:00
-- url     : https://prove2.me/theorems/366fa7d4-05ab-4979-991f-86aa99bbc9f8
-- title:
--   Largest maximum point $a_-$
-- statement:
--   $a_-$ is the largest maximum point of the buying problem at $(1,0)$: the supremum of the set of its maximum points.
--
--   **Formalization Note** Defined as the real supremum of the set; it is the largest maximum point exactly when the set has a greatest element, which the statements using $a_-$ assert.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Proposition 4.5.2, step (iv), p.111 (PDF 125)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxMinus

namespace BauerleRiederMDP.TransactionCosts

/-- The largest maximum point `a₋` of the buying problem at `x = (1, 0)` (Bäuerle & Rieder
2011, proof of Proposition 4.5.2, step (iv), p.111, PDF 125: "We denote by a₋ the largest
maximum point of this problem").

**Formalization Note.** Defined as the real `sSup` of `argmaxMinus`; this is the largest maximum
point exactly when that set has a greatest element, which the statements using `aMinus` assert
(`IsGreatest`). -/
noncomputable def Market.aMinus {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) : ℝ :=
  sSup (M.argmaxMinus n v)

end BauerleRiederMDP.TransactionCosts


