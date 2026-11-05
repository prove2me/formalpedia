-- Prove2me | Definitions.Def_BaconOQEC_repDecode
-- name    : BaconOQEC_repDecode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:53.7002+00:00
-- url     : https://prove2.me/theorems/bc7a4631-121b-4feb-ab40-40debf1cec9e
-- title:
--   Repetition-code decoder $f''$ from the syndrome
-- statement:
--   The row parities $f_1(b),\dots,f_n(b)$ of a $Z$-error are treated as a word of the $n$-bit repetition code. The $S^X$-syndrome gives the differences $s_i = f_i \oplus f_{i+1}$, $i = 1,\dots,n-1$. Two bit strings are consistent with it: $f'$ with $f'_1 = 0$ and $f'_{i+1} = f'_i\oplus s_i$, i.e. $f'_k = \bigoplus_{i<k} s_i$, and its negation $\neg f'$. The decoder returns
--
--   $$
--   f'' = \text{the one of } f',\ \neg f' \text{ with the smaller Hamming weight}.
--   $$
--
--   The same decoder applied to the $S^Z$-syndrome gives the column string $e''$ of the $X$-correction.
--
--   **Formalization Note** Positions are 0-based, $n = m+1$; Hamming weight is Mathlib's `hammingNorm` (number of nonzero entries). On a tie $H(f') = H(\neg f')$, which the page leaves open and which can occur only for even $n$, the decoder returns $f'$.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.C, pp.7–8

import Mathlib

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.C, pp.7–8: the decoder of the `n`-bit repetition ("redundancy") code
from its syndrome. "Give[n] the s^X_i we can construct two possible bit strings f′_i and ¬f′_i …
consistent with these measurements. Let H(f′) and H(¬f′) denote the Hamming weight of these bit
strings … and define f″ to be the bit string f′ or ¬f′ with the smallest Hamming weight." From the
syndrome bits `s_i = f_i ⊕ f_{i+1}` (`i : Fin m`) the candidate is `f′_k = Σ_{i < k} s_i` (so
`f′_0 = 0` and `f′_{i+1} = f′_i ⊕ s_i`), its negation is `1 + f′`, and `repDecode s` is the one of
smaller Hamming weight.

**Formalization Note.** Positions `k : Fin (m + 1)` (`n = m + 1` bits, 0-based). Hamming weight is
Mathlib's `hammingNorm` (number of nonzero entries). The page leaves a tie `H(f′) = H(¬f′)` (possible
for even `n`) open; this decoder then returns `f′`. -/
def repDecode {m : ℕ} (s : Fin m → ZMod 2) : Fin (m + 1) → ZMod 2 :=
  let f : Fin (m + 1) → ZMod 2 := fun k =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < (k : ℕ)), s i
  if hammingNorm f ≤ hammingNorm (1 + f) then f else 1 + f

end BaconOQEC


