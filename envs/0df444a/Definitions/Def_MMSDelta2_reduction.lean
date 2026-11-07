-- Prove2me | Definitions.Def_MMSDelta2_reduction
-- name    : MMSDelta2_reduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:07.552676+00:00
-- url     : https://prove2.me/theorems/577e24ca-d93c-45ec-939e-2155a5eced75
-- title:
--   The §7 reduction as a map on binary strings
-- statement:
--   The reduction from LexMax4Partition-Promise to MMS existence maps the code of a 4-PARTITION instance to the code of the five-agent goods instance constructed from it in §7.1. Every string that is not the code of a 4-PARTITION instance is mapped to the one-bit string $1$, which has odd length and so is the code of no instance (instance codes have even length); it is a no-instance of the MMS problem.
--
--   This is the map whose polynomial running time is Lemma 7.14.
--
--   **Formalization Note** The instance is recovered from its code by choice; the code is injective, so the recovered instance is the encoded one.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §7.1 and Lemma 7.14, pp.27–37 (PDF pp.29–39)

import Mathlib
import Definitions.Def_MMSDelta2_buildInstance
import Definitions.Def_MMSDelta2_instCode

namespace MMSDelta2

/-!
# The reduction map of §7 on binary strings

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §7.1 and Lemma 7.14, pp.27–37 (PDF pp.29–39).

**Formalization Note.** On the code of a 4-PARTITION instance the map outputs the code of the
constructed five-agent instance `buildInstance`. Every other string is mapped to `[true]`, which
has odd length and so encodes no instance (instance codes have even length); it is in neither MMS
language. Whether a string is a code is decidable in polynomial time. The instance is recovered
from its code by choice; `fourPartCode` is injective, so the choice is the instance itself.
-/

open Classical in
/-- The reduction from LexMax4Partition-Promise to MMS existence for five agents. -/
noncomputable def reduction (x : List Bool) : List Bool :=
  if h : ∃ I : FourPartInstance, fourPartCode I = x then
    instCode 5 _ (Classical.choose h).buildInstance
  else [true]

end MMSDelta2


