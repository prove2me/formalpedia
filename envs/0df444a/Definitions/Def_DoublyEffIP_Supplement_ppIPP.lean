-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_ppIPP
-- name    : DoublyEffIP_Supplement_ppIPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:36:43.223727+00:00
-- url     : https://prove2.me/theorems/e61b4947-fb58-4444-b0fe-aae9e826c4dc
-- title:
--   Public parameters $[\sigma,\mathbb F,\langle\Phi\rangle,d]$ of the IPP
-- statement:
--   The public parameters of the IPP with row reduction for a $k\times L$ input matrix are the word
--
--   $$
--   \langle\sigma\rangle\,\langle\mathbb F\rangle\,\langle d\rangle\,\langle k\rangle\,\langle L\rangle\,\langle\Phi\rangle ,
--   $$
--
--   the numbers in self-delimited binary, the field by its presentation, and the description $\langle\Phi\rangle$ self-delimited.
--
--   **Formalization Note** The shape $(k,L)$ is a parameter, since the verifier must know what its output describes. $\langle\Phi\rangle$ comes last, so the numbers can be read without scanning it.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Theorem 4, p.13 (IPP(Φ) := (P(M), V)[σ,F,⟨Φ⟩,d]); Definition 9, p.12

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_encFieldPres
import Definitions.Def_DoublyEffIP_encBin
import Definitions.Def_AvgCaseTI_FieldPres
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT

namespace DoublyEffIP.Supplement

/-- **The public parameters of the IPP with row reduction** — `IPP(Φ) := (P(M), V)[σ,F,⟨Φ⟩,d]`
for an input matrix of shape `k × L`, Theorem 4 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.13; Definition 9, p.12 ("the verifier
receives no input (except the protocol's parameters)").

The word `⟨σ⟩ ⟨F⟩ ⟨d⟩ ⟨k⟩ ⟨L⟩ ⟨Φ⟩`: the numbers in self-delimited binary, the field by its
presentation (`encFieldPres`), the description `⟨Φ⟩` self-delimited.

**Formalization Note.** The shape `(k, L)` of the input matrix is a parameter: the prover's input
is a `k × L` matrix, and the verifier needs its shape to know what the output describes. `⟨Φ⟩`
comes last, so the numbers can be read without scanning it. -/
def ppIPP (σ : ℕ) (P : AvgCaseTI.FieldPres) (descΦ : List Bool) (d k L : ℕ) : List Bool :=
  encBin σ ++ encFieldPres P ++ encBin d ++ encBin k ++ encBin L ++ Encoding.frame descΦ

end DoublyEffIP.Supplement


