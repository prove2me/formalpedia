-- Prove2me | Definitions.Def_HybridXorLift_blockParity
-- name    : HybridXorLift_blockParity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:45.595598+00:00
-- url     : https://prove2.me/theorems/cf3932f2-387a-48d4-8c89-28ee74c61004
-- title:
--   Block parity $\bigoplus_{j=1}^r y_j$
-- statement:
--   For a block $y = (y_1,\dots,y_r) \in \{0,1\}^r$ of $r$ bits, its **parity** is
--   $$
--   \bigoplus_{j=1}^r y_j \in \{0,1\},
--   $$
--   the exclusive or of the bits; the parity of the empty block ($r = 0$) is $0$.
--
--   The parity is the gadget of the parity encoding: every bit of the original input is stored as the parity of a block of physical bits.
--
--   **Formalization Note** Bits are Booleans ($1$ = `true`); the sum is taken in the Boolean ring $\mathbb F_2$ structure on `Bool`, in which addition is exclusive or. Positions are indexed $0,\dots,r-1$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.3, Eq. (2.2), p.10 (PDF p.12)

import Mathlib

namespace HybridXorLift

/-- The parity `⊕_{j=1}^r y_j` of a block of `r` bits (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.3, Eq. (2.2), p.10 (PDF p.12)).

**Formalization Note** Bits are `Bool` (`true` = 1). The sum is taken in Mathlib's Boolean-ring
structure on `Bool`, in which `+` is exclusive or; the positions of the block are `Fin r`
(0-based). -/
def blockParity (r : ℕ) (y : Fin r → Bool) : Bool :=
  ∑ j, y j

end HybridXorLift


