-- Prove2me | Definitions.Def_BaconThesis_ExchangeUniv_totalS2
-- name    : BaconThesis_ExchangeUniv_totalS2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:47.786015+00:00
-- url     : https://prove2.me/theorems/6ff1e053-0949-4198-9514-09084fa07284
-- title:
--   The total angular momentum $(S^{[n]})^2$
-- statement:
--   The **total angular momentum** of $n$ qubits is
--   $$
--   \big(S^{[n]}\big)^2=\big(S^{[n]}_x\big)^2+\big(S^{[n]}_y\big)^2+\big(S^{[n]}_z\big)^2 .
--   $$
--   Its eigenvalues are $J(J+1)$ for $J=n/2,\,n/2-1,\dots$ down to $0$ or $\tfrac12$, and its eigenspaces carry the strong collective decoherence DFSs.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, eq. (8.39), §8.6, p.117 (PDF p.134); used in (C.8), p.248 (PDF p.265)

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_collS

open scoped Matrix

namespace BaconThesis.ExchangeUniv

/-- **The total angular momentum `(S^[n])² = S_x² + S_y² + S_z²`.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, (8.39), §8.6, p.117 (PDF p.134); used in (C.8), p.248 (PDF p.265). Its eigenvalue on the
spin-`J` irreps is `J(J+1)`, and the strong collective decoherence DFS `DFS_n(J)` lives in that
eigenspace.

**Formalization Note.** Defined directly as the sum of the squares of the three collective
operators `collS n α`. -/
noncomputable def totalS2 (n : ℕ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  ∑ α : Fin 3, collS n α * collS n α

end BaconThesis.ExchangeUniv


