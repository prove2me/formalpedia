-- Prove2me | Definitions.Def_SelectiveDPT_H2
-- name    : SelectiveDPT_H2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:53.712689+00:00
-- url     : https://prove2.me/theorems/d5bbf923-0786-451b-984b-565fa9ae1a94
-- title:
--   Binary entropy $H_2$ in bits
-- statement:
--   The **binary entropy** in bits is
--   $$H_2(p) = p\log_2\frac1p + (1-p)\log_2\frac1{1-p}, \qquad p \in [0,1],$$
--   with $0\log(1/0) = 0$.
--
--   **Formalization Note** Mathlib's `Real.binEntropy` uses the natural logarithm, so $H_2 = \mathrm{binEntropy}/\ln 2$.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §2.1, p.8

import Mathlib

namespace SelectiveDPT

/-- The binary entropy in bits, `H₂(p) = p log₂(1/p) + (1 − p) log₂(1/(1 − p))`
(arXiv:2609.26678, §2.1, p.8: "where log is assumed to be base 2 unless otherwise indicated").

**Formalization Note.** Mathlib's `Real.binEntropy` is in nats, so it is divided by `ln 2`. -/
noncomputable def H2 (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

end SelectiveDPT


