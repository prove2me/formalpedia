-- Prove2me | Definitions.Def_WeightedCongestionBR_IsPd
-- name    : WeightedCongestionBR_IsPd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:36.908194+00:00
-- url     : https://prove2.me/theorems/b130a1bd-eac2-4848-90e4-e937a40da045
-- title:
--   The class $\mathfrak P_d$ of polynomials
-- statement:
--   For a natural number $d$, $\mathfrak P_d$ is the class of real polynomials of degree at most $d$ with nonnegative coefficients,
--
--   $$
--   f(x)=\sum_{i=0}^d a_i x^i,\qquad a_i\ge 0 .
--   $$
--
--   Every cost function of a polynomial weighted congestion game of degree $d$ lies in $\mathfrak P_d$; Lemmas 2 and 14 quantify over this class.
--
--   **Formalization Note** An element is a `Polynomial ℝ` with `natDegree ≤ d` and all coefficients nonnegative.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, §2, p.5 and footnote 9

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The class `𝔓_d` of polynomials of degree at most `d` with nonnegative coefficients
(Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, §2, p.5 and footnote 9): `f(x) = ∑_{i=0}^d a_i x^i` with `a_i ≥ 0`.

**Formalization Note** Elements are real polynomials `P`, evaluated with `P.eval`. -/
def IsPd (d : ℕ) (P : Polynomial ℝ) : Prop :=
  P.natDegree ≤ d ∧ ∀ j, 0 ≤ P.coeff j

end WeightedCongestionBR


