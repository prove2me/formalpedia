-- Prove2me | Definitions.Def_BaconThesis_Collective_totalS2
-- name    : BaconThesis_Collective_totalS2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:58.057322+00:00
-- url     : https://prove2.me/theorems/6cbb58f2-580a-4e19-8159-60e44fdcb794
-- title:
--   Total angular momentum $(S^{[n]})^2$
-- statement:
--   The **total angular momentum** (Casimir) operator of $n$ qubits,
--   $$
--   \big(S^{[n]}\big)^2=\big(S_x^{[n]}\big)^2+\big(S_y^{[n]}\big)^2+\big(S_z^{[n]}\big)^2 .
--   $$
--   It commutes with every $S_\alpha^{[n]}$; on the spin-$J$ irreps it acts as $J(J+1)$ (8.40).
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.39), §8.6, p.117 (PDF p.134)

import Mathlib
import Definitions.Def_BaconThesis_Collective_collS

open scoped Matrix

namespace BaconThesis.Collective

/-- **The total angular momentum operator `(S^[n])²`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.39), §8.6, p.117 (PDF p.134):
`(S^[n])² = (S_x^[n])² + (S_y^[n])² + (S_z^[n])²`. -/
noncomputable def totalS2 (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  collS n .x ^ 2 + collS n .y ^ 2 + collS n .z ^ 2

end BaconThesis.Collective


