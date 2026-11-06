-- Prove2me | Definitions.Def_MetricMinTest_certWorkloadInt
-- name    : MetricMinTest_certWorkloadInt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:40.401698+00:00
-- url     : https://prove2.me/theorems/0f79a020-b082-44a8-8fff-04a33ad73da4
-- title:
--   Integral ball-cover optimum
-- statement:
--   The **integral cover optimum** is the value of program (2.1) with the weights $y_{j\ell}$ restricted to nonnegative integers. Theorem A asserts that on $d_m$ it equals the fractional optimum $F$.
--
--   **Formalization Note** Same encoding of indexed balls as the certificate workload.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Eq. (2.1), p.6; Theorem A, p.2; Theorem 4.2, p.8

import Mathlib

namespace MetricMinTest

/-- **Integral ball-cover optimum.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*,
STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem A p.2 and Theorem 4.2 p.8
("the fractional and integral cover optima agree"): program (2.1), p.6, with `y` restricted to
nonnegative integers.

**Formalization Note.** Same encoding of indexed balls as `certWorkload` (pairs `(j, i)` with
`d j i < γ`), with `y : ι × ι → ℕ`. -/
noncomputable def certWorkloadInt {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (γ : ℝ) : ℝ :=
  sInf {C : ℝ | ∃ y : ι × ι → ℕ,
    (∑ p ∈ Finset.univ.filter (fun p : ι × ι => d p.1 p.2 < γ),
      (y p : ℝ) * ((γ - d p.1 p.2) ^ 2)⁻¹) = C ∧
    ∀ i, 1 ≤ ∑ p ∈ Finset.univ.filter (fun p : ι × ι => d p.1 p.2 < γ ∧ d i p.1 ≤ d p.1 p.2),
      (y p : ℝ)}

end MetricMinTest


