-- Prove2me | Definitions.Def_AvgValueAlloc_coinTape
-- name    : AvgValueAlloc_coinTape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:24.32463+00:00
-- url     : https://prove2.me/theorems/e0177181-3474-4af8-af7b-9d44696c038a
-- title:
--   Fair coin tape
-- statement:
--   The law of an infinite sequence $\omega=(\omega_0,\omega_1,\dots)$ of independent fair bits: the product of uniform measures on $\{0,1\}$.
--
--   It is the randomness of the polynomial-time learner.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3, p.7; Appendix A.2, p.14

import Mathlib

namespace AvgValueAlloc

/-- **The fair coin tape.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3, p.7: "two fair bits select one branch";
Appendix A.2, p.14: "This uses O(log(nT)) fair bits per proposal".

`coinTape` is the law of an infinite sequence of independent fair bits: the product of uniform
measures on `Bool`. -/
noncomputable def coinTape : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

end AvgValueAlloc


