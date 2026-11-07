-- Prove2me | Definitions.Def_NSWBetter_largeSet
-- name    : NSWBetter_largeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:16.567192+00:00
-- url     : https://prove2.me/theorems/070a56f7-5b73-44cb-89b2-0a6e809bd7a5
-- title:
--   The set $L_i$ of large goods of agent $i$
-- statement:
--   $L_i$, the unique set satisfying Definition 4.7 (Lemma 4.10). Goods outside $L_i$ are the **small** goods of agent $i$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.7, p.20; Lemma 4.10, p.21

import Mathlib
import Definitions.Def_NSWBetter_IsLargeSetFrac

namespace NSWBetter

open Classical in
/-- **The set L_i.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.7, p.20; Lemma 4.10, p.21: "For any fractional allocation x and agent i, there is a unique set of large goods Li satisfying the properties of Definition 4.7."

**Formalization Note.** By Lemma 4.10 the set exists and is unique, so the choice is canonical; the fallback `∅` is never reached for a fractional allocation. -/
noncomputable def largeSet {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n) :
    Finset (Fin m) :=
  if h : ∃ L, IsLargeSetFrac v x i L then Classical.choose h else ∅

end NSWBetter


