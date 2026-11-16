-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsAFUnitaryWide
-- name    : QiOPoQ_Supplement_IsAFUnitaryWide
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:03:24.711995+00:00
-- url     : https://prove2.me/theorems/0cf8b572-9a00-4954-96dc-8a68e6400ec4
-- title:
--   Polynomial-size ancilla-free unitary families of width at least $\lambda$
-- statement:
--   The class of Theorem 6.6: families that are polynomial-size, have no ancillas ($n_{\mathrm{anc}}=0$), are unitary, and have width $n_{\mathrm{in}}+n_{\mathrm{anc}}\ge\lambda$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 6.6, p.32; §3.1, pp.13–14

import Mathlib
import Definitions.Def_QiOPoQ_Circ
import Definitions.Def_QiOPoQ_Supplement_IsUnitaryFam

set_option autoImplicit false

namespace QiOPoQ.Supplement

/-- **Polynomial-size ancilla-free unitary circuit families of width at least `λ`.** Gheorghiu,
Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit
Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 6.6, p.32: "there is a quantum iO
scheme for polynomial-size ancilla-free unitary circuit families of width at least λ"; §3.1,
pp.13–14 ("polynomial-sized", "Its width is n_in + n_anc", "A circuit is ancilla-free if
n_anc = 0", "C_unitary").

The family is polynomial-size, every member has `n_anc = 0`, the family is unitary
(`IsUnitaryFam`), and `C_λ` has width `n_in + n_anc ≥ λ`. -/
def IsAFUnitaryWide {G : GateSet} (Cf : ℕ → Circ G) : Prop :=
  PolySize Cf ∧ (∀ n, (Cf n).nanc = 0) ∧ IsUnitaryFam Cf ∧ ∀ n, n ≤ (Cf n).nin + (Cf n).nanc

end QiOPoQ.Supplement


