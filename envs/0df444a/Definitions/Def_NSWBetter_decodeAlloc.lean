-- Prove2me | Definitions.Def_NSWBetter_decodeAlloc
-- name    : NSWBetter_decodeAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:50:40.254194+00:00
-- url     : https://prove2.me/theorems/926bce7a-dfd7-4789-b19c-bf4f022110fd
-- title:
--   Decoding an algorithm's output list into an allocation
-- statement:
--   An algorithm outputs a list $l$ of natural numbers; it is read as the allocation in which good $g$ (0-based) goes to agent $k$ when $l_g=k+1$ with $k<n$, and is unallocated when $l_g=0$, when $l_g>n$, or when the list is too short.
--
--   Every list is read as some allocation, so a malformed output can only lower the Nash welfare.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 1.1, p.3 (the algorithm outputs an allocation)

import Mathlib
import Definitions.Def_NSWBetter_Inst
import Definitions.Def_NSWBetter_Alloc

namespace NSWBetter

/-- **Reading an allocation from a list of naturals.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 1.1, p.3: the algorithm's output is an allocation.

`decodeAlloc I l` gives good `g` to agent `k` when `l[g] = k + 1` with `k < n`, and leaves it unallocated otherwise (entry `0`, an index `≥ n`, or a missing entry).

**Formalization Note.** Every list decodes to an allocation, so a malformed output can only lower the Nash welfare; nothing is gained from it. Outputs are encoded by the platform's `ReserveLB.encListNat`. -/
def decodeAlloc (I : Inst) (l : List ℕ) : Alloc I := fun g =>
  match l[g.val]? with
  | some (k + 1) => if h : k < I.n then some ⟨k, h⟩ else none
  | _ => none

end NSWBetter


