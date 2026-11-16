-- Prove2me | Definitions.Def_QiOPoQ_Supplement_encShape
-- name    : QiOPoQ_Supplement_encShape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:47:08.274998+00:00
-- url     : https://prove2.me/theorems/bd1feafd-afe4-433d-80c7-77f4bba2cdbc
-- title:
--   Descriptions of circuit shapes, and unary decoding
-- statement:
--   The classical description of a shape $(s,n_{\mathrm{in}},n_{\mathrm{anc}},n_{\mathrm{out}})$: the tuple code of the four numbers in unary. It is the input of the blindness simulator $\mathrm{Sim}(1^\lambda,\mathrm{shape}(C_\lambda))$ and of the canonical padding $X_b$ of Notation 5.1. `decNat` decodes a unary code (and fails on any other string).
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13; Definition 3.5, p.16; Notation 5.1, p.22

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- The classical description of a circuit shape `(s, n_in, n_anc, n_out)` (Gheorghiu, Gupte,
Havlíček, Liu, arXiv:2609.40289, sha256 fe2f9210…, §3.1, p.13: "shape(C) := (s, n_in, n_anc,
n_out)"; Definition 3.5, p.16: "chall′ ← Sim(1^λ, shape(C_λ))"; Notation 5.1, p.22: "from b and
this common shape alone"): the tuple code of the four numbers in unary. -/
def encShape (sh : ℕ × ℕ × ℕ × ℕ) : Str :=
  tup [encNat sh.1, encNat sh.2.1, encNat sh.2.2.1, encNat sh.2.2.2]

/-- Decoding of `encNat`: `decNat (encNat k) = some k`, and `none` on a string that is not a unary
code. -/
def decNat (s : Str) : Option ℕ :=
  if s = encNat (s.length - 1) then some (s.length - 1) else none

end QiOPoQ.Supplement


