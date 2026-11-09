-- Prove2me | Definitions.Def_RSSubspaceDesign_encField
-- name    : RSSubspaceDesign_encField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:23:42.550394+00:00
-- url     : https://prove2.me/theorems/afcd154d-a684-49d1-adc3-35861f9ada04
-- title:
--   The input code of a finite field $K=\mathbb F_p[Y]/(f)$
-- statement:
--   The binary input code of the finite field $K=\mathbb F_p[Y]/(f)$: the prime $p$ in binary, followed by the list of the $\deg f+1$ coefficients of $f$, each a residue in $\{0,\dots,p-1\}$ written in binary.
--
--   The constructions of this mission receive $K$ in this form, followed by their numerical parameters.
--
--   **Formalization Note** Uses the public self-delimiting codes `encNat` and `encList` (`RSListDecodingCapacity.AllRates`).
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Theorem 1.1, p.4 (PDF p.6); Theorem 7.2, p.40 (PDF p.42); Lemma 7.3, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

open Polynomial

namespace RSSubspaceDesign

open RSListDecodingCapacity.AllRates in
/-- **The input code of a finite field `K = 𝔽_p[Y]/(f)`.** Alrabiah–Goyal–Guruswami,
arXiv:2610.36215 (held version, sha256 cf26424b…f36206), Theorem 1.1, p.4, Theorem 7.2, p.40 and
Lemma 7.3, p.41 ("given a finite field `K`").

The prime `p` in binary, followed by the list of the `deg f + 1` coefficients of `f` as residues
`0, …, p − 1` in binary.

**Formalization Note.** Uses the public self-delimiting codes `encNat`/`encList` of
`RSListDecodingCapacity.AllRates`. -/
def encField (p : ℕ) (f : (ZMod p)[X]) : List Bool :=
  encNat p ++ encList encNat ((List.range (f.natDegree + 1)).map fun i => (f.coeff i).val)

end RSSubspaceDesign


