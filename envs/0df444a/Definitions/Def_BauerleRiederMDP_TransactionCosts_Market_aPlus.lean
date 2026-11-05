-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_aPlus
-- name    : BauerleRiederMDP_TransactionCosts_Market_aPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:28:16.207663+00:00
-- url     : https://prove2.me/theorems/7883fa0f-53eb-4b66-b299-7801d5f9f690
-- title:
--   Largest maximum point $a_+$
-- statement:
--   $a_+$ is the largest maximum point of the selling problem at $(0,1)$: the supremum of the set of its maximum points.
--
--   **Formalization Note** Defined as the real supremum of the set; it is the largest maximum point exactly when the set has a greatest element, which the statements using $a_+$ assert.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), proof of Proposition 4.5.2, step (ii), p.109 (PDF 123)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market
import Definitions.Def_BauerleRiederMDP_TransactionCosts_Market_argmaxPlus

namespace BauerleRiederMDP.TransactionCosts

/-- The largest maximum point `a₊` of the selling problem at `x = (0, 1)` (Bäuerle & Rieder
2011, proof of Proposition 4.5.2, step (ii), p.109, PDF 123: "we denote by a₊ the largest
maximum point of this problem").

**Formalization Note.** Defined as the real `sSup` of `argmaxPlus`; this is the largest maximum
point exactly when that set has a greatest element, which the statements using `aPlus` assert
(`IsGreatest`). -/
noncomputable def Market.aPlus {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (n : ℕ)
    (v : ℝ × ℝ → EReal) : ℝ :=
  sSup (M.argmaxPlus n v)

end BauerleRiederMDP.TransactionCosts


