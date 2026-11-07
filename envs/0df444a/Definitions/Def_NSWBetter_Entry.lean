-- Prove2me | Definitions.Def_NSWBetter_Entry
-- name    : NSWBetter_Entry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:34.644979+00:00
-- url     : https://prove2.me/theorems/029abdf4-4c34-46d7-a56a-a2111074d3b9
-- title:
--   Entry $(i,S,y_{i,S})$ of a configuration LP solution
-- statement:
--   An entry $(i,S,q)$ of the sparse representation of a configuration LP solution: agent $i$, bundle $S$ given as a list of good indices, and value $y_{i,S}=q\in\mathbb Q$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Theorem 2.5, p.10 ("represented using a list of the non-zero entries")

import Mathlib

namespace NSWBetter

/-- **An entry of a configuration LP solution.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Theorem 2.5, p.10: "represented using a list of the non-zero entries".

An entry `(i, S, q)` is an agent index, a list of good indices (the bundle `S`) and the rational value `y_(i,S) = q`. -/
abbrev Entry : Type := ℕ × List ℕ × ℚ

end NSWBetter


