-- Prove2me | Definitions.Def_SATotalCoeffLB_QForm_eval
-- name    : SATotalCoeffLB_QForm_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:04.346892+00:00
-- url     : https://prove2.me/theorems/b608a3b4-9791-4d9f-8936-b12b7a0f219c
-- title:
--   Evaluation $a(\bar x)$ of a quadratic form
-- statement:
--   For $a = \sum_{i<j} a_{ij} \bar x_i \bar x_j \in Q_n$ and $\bar x \in \mathbb F_2^n$,
--
--   $$
--   a(\bar x) = \sum_{i<j} a_{ij}\, \bar x_i \bar x_j \in \mathbb F_2 .
--   $$
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.1, Quadratic Forms, pp.50–51

import Mathlib
import Definitions.Def_SATotalCoeffLB_QForm

namespace SATotalCoeffLB

/-- **Evaluation of a quadratic form** `a(x̄) = ∑_{i<j} a_ij x̄_i x̄_j ∈ F₂` at `x̄ ∈ F₂ⁿ`
(Section 9.1, pp.50–51, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)). -/
def QForm.eval {n : ℕ} (a : QForm n) (xb : Fin n → ZMod 2) : ZMod 2 :=
  ∑ e : Pair n, a e * xb e.1.1 * xb e.1.2

end SATotalCoeffLB


