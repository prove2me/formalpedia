-- Prove2me | Definitions.Def_MayersBC_binaryPOVM
-- name    : MayersBC_binaryPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:56.721734+00:00
-- url     : https://prove2.me/theorems/87ffef63-2acd-40d4-aec9-1205096d3650
-- title:
--   Two-outcome measurement $\{Q, I - Q\}$
-- statement:
--   An effect $Q$ (an operator with $0 \le Q \le I$) defines the measurement with two outcomes: outcome $0$ has POVM element $Q$ and outcome $1$ has POVM element $I - Q$. On p.8 the measurement $\{M'_0, M'_1\}$ obtained by grouping the outcomes of an arbitrary measurement is of this form.
--
--   **Formalization Note** The outcomes are $\{0, 1\}$ (`Fin 2`).
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, pp.7–8

import Mathlib

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, pp.7–8: the measurement "that return[s] two
outcomes", given by an effect `Q`: outcome `0` has POVM element `Q`, outcome `1` has `I − Q`
(on p.8, `M'_0` and `M'_1`).

**Formalization Note.** Outcomes are `Fin 2`; `binaryPOVM Q 0 = Q`, `binaryPOVM Q 1 = 1 − Q`. -/
def binaryPOVM {ι : Type} [DecidableEq ι] (Q : Matrix ι ι ℂ) : Fin 2 → Matrix ι ι ℂ :=
  ![Q, 1 - Q]

end MayersBC


