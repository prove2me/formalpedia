-- Prove2me | Definitions.Def_GoodQLTC_logicalQubits
-- name    : GoodQLTC_logicalQubits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:37:22.395644+00:00
-- url     : https://prove2.me/theorems/aebed77a-3c46-4cf7-8315-e0825706bf35
-- title:
--   Number of logical qubits $K(Q)=N-\operatorname{rank}H_X-\operatorname{rank}H_Z$
-- statement:
--   A CSS code encodes
--   $$
--   K(Q)=N-\operatorname{rank}H_X-\operatorname{rank}H_Z
--   $$
--   logical qubits (ranks over $\mathbb F_2$); its code space has dimension $2^{K(Q)}$.
--
--   The rate of a code family is $K(Q_\nu)/N_\nu$.
--
--   **Formalization Note** An integer.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.2, p.14 (PDF p.17)

import Mathlib

namespace GoodQLTC

/-- The number of **logical qubits** `K(Q) := N − rank H_X − rank H_Z` of the CSS code
`(H_X, H_Z)`, Gay–Jeronimo, arXiv:2609.20780 (held version), §3.2, p.14 (ranks over `F_2`).

**Formalization Note.** An integer; for a CSS code (`H_X H_Z^⊺ = 0`) it is `≥ 0`. -/
noncomputable def logicalQubits {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) : ℤ :=
  (Fintype.card ι : ℤ) - (HX.rank : ℤ) - (HZ.rank : ℤ)

end GoodQLTC


