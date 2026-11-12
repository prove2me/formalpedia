-- Prove2me | Definitions.Def_APFPaper1_SupportNovel
-- name    : APFPaper1_SupportNovel
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-10T20:01:47.165068+00:00
-- url     : https://prove2.me/theorems/dce0485b-3a2e-4692-9a94-4710bc638414
-- title:
--   Support novelty in a positive near-optimal window
-- statement:
--   For the same original Ledger L, finite family S and distinction d, some eta > 0 excludes carried sufficient records for d from every S-serving protocol whose complete price is at most cost L S + eta. This is the original source predicate; physical applicability of supplied Ledger data and the predicate remain explicit. It is neither universal novelty nor a uniform marginal-floor input.
-- source:
--   Paper 1 Supplement v9.27, lines 2615-2617; original predicate lines 53-54 in the pinned recovered Foundation definition. Current source-preserving CostLedger provider; FOUNDATION_INPUTS revision 2026-10-04.1 unchanged.

import Definitions.Def_APFPaper1_CostLedger

set_option autoImplicit false

namespace APFPaper1.Foundation

/-- Positive-window support novelty on the SAME original Ledger, protocol,
record, complete-price and infimal-cost domains. Paper 1 Supplement v9.27,
2615-2617. This predicate is a local hypothesis when consumed; it asserts
neither universal physical novelty nor a uniform marginal floor. -/
def SupportNovel {D P Record : Type*} (L : Ledger D P Record) (S : Finset D) (d : D) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ p, L.serves p S → L.price p ≤ cost L S + η → ¬ L.carries p d

end APFPaper1.Foundation


