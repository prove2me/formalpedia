-- Prove2me | Definitions.Def_BaconOQEC_InT
-- name    : BaconOQEC_InT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:36.240137+00:00
-- url     : https://prove2.me/theorems/308f32ad-bfcd-4767-b35c-629103b57993
-- title:
--   Membership in the gauge group $\mathcal T$
-- statement:
--   The group $\mathcal T$ consists of the Pauli operators with an even number of $X$'s in every column and an even number of $Z$'s in every row:
--
--   $$
--   \mathcal T = \Big\{ (-1)^\varphi P(a,b) \;\Big|\; \varphi\in\mathbb Z_2,\ \bigoplus_{i=1}^n a_{i,j} = 0 \ \forall j,\ \bigoplus_{j=1}^n b_{i,j} = 0\ \forall i \Big\}.
--   $$
--
--   The predicate says that $P(a,b)$ (with either sign) lies in $\mathcal T$, i.e. all column parities $e_j(a)$ and all row parities $f_i(b)$ vanish. $\mathcal T$ is the gauge group of the subsystem code: it acts only on the gauge subsystem and never on the encoded qubit.
--
--   **Formalization Note** Operators are taken modulo phase, as pairs $(a,b)$; the sign $(-1)^\varphi$ of (8) is dropped.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.A, eq. (8), p.4; §IV.C, eq. (20), p.7

import Mathlib
import Definitions.Def_BaconOQEC_colPar
import Definitions.Def_BaconOQEC_rowPar

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.A, eq. (8), p.4: the group `T`, "made up of Pauli operators which
have an even number of X_{i,j} operators in each column and an even number of Z_{i,j} operators in
each row", `T = {(−1)^φ P(a, b) | φ ∈ Z₂, ⊕_i a_{i,j} = 0, and ⊕_j b_{i,j} = 0}`. `InT a b` says
that `P(a, b)` (with either sign) is in `T`: every column parity `e_j(a)` and every row parity
`f_i(b)` vanishes (cf. (20), p.7: "if e_j = f_i = 0, ∀i, j, then this implies that P(a, b) is in
the set T").

**Formalization Note.** Pauli operators are taken modulo phase, as pairs of bit matrices; the sign
`(−1)^φ` of (8) is dropped. Indices are 0-based, `n = m + 1`. -/
def InT {m : ℕ} (a b : Bits m) : Prop :=
  (∀ j, colPar a j = 0) ∧ (∀ i, rowPar b i = 0)

end BaconOQEC


