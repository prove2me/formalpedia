-- Prove2me | Definitions.Def_AvgValueAlloc_LearnerInput
-- name    : AvgValueAlloc_LearnerInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:27.278008+00:00
-- url     : https://prove2.me/theorems/7f594537-e3b4-4141-8395-0c4236354afd
-- title:
--   Observation of the learner at one live position
-- statement:
--   Before each decision the learner observes the thresholds $\rho_1,\dots,\rho_n$, the horizon $T$, the history length $S$, the $S$ historical vectors, the past live vectors and the current live vector, each vector given by its $n$ rational coordinates.
--
--   This is the "observed binary input" in which the learner's running time is measured.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2

import Mathlib

namespace AvgValueAlloc

/-- **What the learner observes before one decision.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "thresholds ρ ∈ Q^n_{>0} and known live
horizon T ≥ 1 … S ≥ 0 historical and T live vectors … Observe each live vector in full, then
irrevocably assign it"; "Runtime is polynomial in n, S, T and observed binary input".

The observation at a live position: the thresholds `rho`, the horizon `T`, the history length
`S`, the `S` historical vectors `hist`, the past live vectors `past` and the current vector `cur`,
each vector a list of its `n` rational coordinates.

**Formalization Note.** `n` is the length of `rho`. Lists keep the input a single plain data type
for Mathlib's Turing-machine model. -/
structure LearnerInput where
  /-- thresholds `ρ_1, …, ρ_n` -/
  rho : List ℚ
  /-- the live horizon -/
  T : ℕ
  /-- the number of historical vectors -/
  S : ℕ
  /-- the historical vectors -/
  hist : List (List ℚ)
  /-- the live vectors already seen -/
  past : List (List ℚ)
  /-- the current live vector -/
  cur : List ℚ

end AvgValueAlloc


