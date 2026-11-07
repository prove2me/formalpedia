-- Prove2me | Definitions.Def_QPSpinParisi_MixHyp
-- name    : QPSpinParisi_MixHyp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:17.985956+00:00
-- url     : https://prove2.me/theorems/f9184dec-c026-4eb1-8f39-6e84f005c4d9
-- title:
--   The mixture assumption $\sum_p 2^p c_p^2<\infty$, some $c_p\neq0$
-- statement:
--   A sequence of real coefficients $(c_p)_{p\ge2}$ is admissible when
--   $$\sum_{p\ge2}2^p c_p^2<\infty\quad\text{and}\quad c_p\ne0\text{ for at least one }p.$$
--   The coefficients may be negative. This is the standing assumption of every result in the mission; it makes the series for $\xi$, $\xi'$, $\xi''$ converge on a neighbourhood of $[-1,1]$.
--
--   **Formalization Note** The sequence is indexed by all natural numbers and $c_0,c_1$ are not read.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3 (PDF p.3)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The standing assumption on the mixture coefficients (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.3, PDF p.3): the real
coefficients `(c_p)_{p≥2}` satisfy `∑_{p≥2} 2^p c_p² < ∞`, and at least one `c_p` is nonzero.

**Formalization Note** `c : ℕ → ℝ` is indexed by all of `ℕ`, and the values `c 0`, `c 1` are never used. -/
def MixHyp (c : ℕ → ℝ) : Prop :=
  Summable (fun p : ℕ => (2 : ℝ) ^ (p + 2) * c (p + 2) ^ 2) ∧ ∃ p, 2 ≤ p ∧ c p ≠ 0

end QPSpinParisi


