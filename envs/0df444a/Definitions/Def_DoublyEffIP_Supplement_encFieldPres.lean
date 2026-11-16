-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_encFieldPres
-- name    : DoublyEffIP_Supplement_encFieldPres
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:32:18.001146+00:00
-- url     : https://prove2.me/theorems/358e0251-abac-4da5-81b6-703179faef2f
-- title:
--   A presented finite field as a bit string
-- statement:
--   A finite field given by a presentation $\mathbb F=\mathbb F_p[X]/(f)$ ($p$ prime, $f$ monic irreducible) is written for the machines as $p$ in binary followed by the list of the coefficients of $f$, each in binary.
--
--   Every finite field has such a presentation, and with it field operations take $\mathrm{polylog}|\mathbb F|$ time, which is the paper's notion of a constructible field (Definition 1).
--
--   **Formalization Note** The presentation is the published `AvgCaseTI.FieldPres`.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.1, p.8, Definition 1; Theorem 4, p.13 (field in the public parameters)

import Mathlib
import Definitions.Def_AvgCaseTI_FieldPres
import Definitions.Def_DoublyEffIP_encBin
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP.Supplement

/-- **A finite field given to the machines** — "a field F" among the public parameters
`[σ, F, ⟨Φ⟩, d]` of the IPP (Theorem 4, p.13) and the field "with respect to" which an LDP-IP is
defined (Definition 8, p.11) in Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…); Section 3.1, p.8 (Definition 1): "every element in F_n has
an O(log|F_n|)-bit representation, and addition, multiplication, and inverses can be computed in
polylog(|F_n|) time given the representations."

The presentation `F = F_p[X]/(f)` (published `AvgCaseTI.FieldPres`) as a word: `p` in binary, then
the list of the coefficients of `f`, each in binary.

**Formalization Note.** Every finite field has such a presentation, and with it the field
operations are computable in `polylog |F|` time, so this is a constructible field in the sense of
Definition 1. -/
def encFieldPres (P : AvgCaseTI.FieldPres) : List Bool :=
  encBin P.p ++ Encoding.encodeList encBin
    ((List.range (P.f.natDegree + 1)).map fun i => (P.f.coeff i).val)

end DoublyEffIP.Supplement


