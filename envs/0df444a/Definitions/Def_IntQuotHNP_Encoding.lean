-- Prove2me | Definitions.Def_IntQuotHNP_Encoding
-- name    : IntQuotHNP_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:11.063901+00:00
-- url     : https://prove2.me/theorems/fba2a3a9-7d8d-4e69-b707-a5b599cbcaef
-- title:
--   The binary codes of an MIHNP input and of a finite set of secrets
-- statement:
--   The **input code** concatenates the self-delimiting binary codes of $p$, $X$, $N$, $t_1,\dots,t_N$, $v_1,\dots,v_N$, in this order. The **output code** of a finite set of natural numbers lists its elements in increasing order, each in the same code. Both are injective, so the machine's output determines the returned set exactly.
--
--   **Formalization Note** The numeric code is the published `ExponomialAssortment.FPTAS.encodeNat`: the bit length in unary, a separator, then the bits. Injectivity of both codes is proved in the mission's sanity checks. The paper does not fix a code; it requires only that the public input has binary encoding length $\mathrm{poly}(\log p)$, and this one has length $O_N(\log p)$ on a promised input.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §3.1 (iv), p.16 (PDF p.17); Definition 4.1, p.21 (PDF p.22); Algorithm 1, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_IntQuotHNP_MIHNPInput
open ExponomialAssortment.FPTAS (encodeNat)

namespace IntQuotHNP

/-- **The binary encoding of a public MIHNP input.**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), §3.1 (iv), p.16 (PDF p.17): "The public input has binary encoding length poly(log p)";
Definition 4.1, p.21: the public input is `p`, `X`, `N`, `t₁, …, t_N` and `v`.

The concatenation of the binary codes of `p`, `X`, `N`, `t₁, …, t_N`, `v₁, …, v_N`, in this order.

**Formalization Note.** Every number is written with the published self-delimiting binary code
`encodeNat` (bit length in unary, a separator, then the bits). The code is injective, and for
fixed `N` its length is `O(log p)` on a promised input. -/
def encodeInput (I : MIHNPInput) : List Bool :=
  encodeNat I.p ++ encodeNat I.X ++ encodeNat I.N ++ (List.ofFn I.t).flatMap encodeNat ++
    (List.ofFn I.v).flatMap encodeNat

/-- **The binary encoding of a finite set of secrets** (the algorithm's output `Y`).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Algorithm 1, p.18 (PDF p.19):
"Output: Y: all secrets satisfying the original input constraints"; Definition 3.1 (iii), p.16:
secrets "have canonical binary encodings".

The elements of the set listed in increasing order, each written with `encodeNat`.

**Formalization Note.** Sorting makes the code canonical, so a set has exactly one code and two
different sets have different codes. -/
def encodeSecrets (s : Finset ℕ) : List Bool :=
  (s.sort (· ≤ ·)).flatMap encodeNat

end IntQuotHNP


