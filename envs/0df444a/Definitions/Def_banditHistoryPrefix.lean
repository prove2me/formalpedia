-- Prove2me | Definitions.Def_banditHistoryPrefix
-- name    : banditHistoryPrefix
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-26T02:03:37.957529+00:00
-- url     : https://prove2.me/theorems/d2b34295-1c5b-4344-9485-9ff273aa1495
-- title:
--   Bandit history prefix before a round
-- statement:
--   For a completed length-$n$ history $h=((A_1,X_1),\ldots,(A_n,X_n))$ and an index $r<n$, banditHistoryPrefixAt returns the length-$r$ history $((A_1,X_1),\ldots,(A_r,X_r))$ available immediately before round $r+1$. It is the input to the policy kernel and UCB indices at that round.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), canonical model §4.6 and Theorem 8.1 Eq. (8.4), printed p. 119 / PDF p. 128.

import Definitions.Def_BanditPolicy

/-!
The history visible immediately before a round of a fixed finite bandit run.
This is the canonical prefix map used implicitly throughout Lattimore and
Szepesvári, *Bandit Algorithms* (CUP 2020), §4.6 and explicitly in the
time-indexed empirical means in Theorem 8.1, Eq. (8.4), printed p. 119.
-/

namespace BanditAlgorithm

/-- For a completed history `h` and round index `r`, retain precisely the
observations from rounds strictly before `r`. -/
def banditHistoryPrefixAt {k n : ℕ} (h : BanditHistory k n) (r : Fin n) :
    BanditHistory k r.val :=
  fun s ↦ h ⟨s.val, lt_trans s.isLt r.isLt⟩

end BanditAlgorithm


