-- Prove2me | Definitions.Def_OnlineCRS_Combine_encQuery
-- name    : OnlineCRS_Combine_encQuery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:24:00.700096+00:00
-- url     : https://prove2.me/theorems/0870ff53-9415-4147-88d8-26b40d04d557
-- title:
--   Input encoding of the independence oracle
-- statement:
--   The input $(i,x,r,S)$ of the oracle (instance, rational point, sampled random index $r\in\mathbb N$, queried set $S\subseteq\{0,\dots,n_i-1\}$) is encoded as $\mathrm{code}_i$, $3$, the encoding of $x$, the binary encoding of $r$, $3$, and the characteristic bit string of $S$.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_OnlineCRS_Combine_encSet

namespace OnlineCRS.Combine

/-- **Input encoding of the independence oracle.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4: "an oracle that answers in polynomial time queries of the form: is a
set `S ⊆ N` in `F_{π,x}`?".

The oracle's input `(i, x, r, S)` (instance, point, sampled random index, queried set) is encoded
as `code i`, `3`, `encVec x`, `encNat r`, `3`, `encSet S`.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. -/
def encQuery {ι : Type} (n : ι → ℕ) (code : ι → List Bool) :
    (Σ i, (Fin (n i) → ℚ) × ℕ × Finset (Fin (n i))) → List Sym :=
  fun p => (code p.1).map bit ++ [3] ++ encVec p.2.1 ++ encNat p.2.2.1 ++ [3] ++ encSet p.2.2.2

end OnlineCRS.Combine


