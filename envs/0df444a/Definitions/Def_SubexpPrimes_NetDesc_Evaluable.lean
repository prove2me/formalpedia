-- Prove2me | Definitions.Def_SubexpPrimes_NetDesc_Evaluable
-- name    : SubexpPrimes_NetDesc_Evaluable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:48.193208+00:00
-- url     : https://prove2.me/theorems/0d6afe88-bf1e-4bc5-b5ba-1d228142eac2
-- title:
--   The hypotheses of Theorem 2.5 on a network
-- statement:
--   A description is **evaluable** with constant $c$ and entry machine $E$ if the network has $m\ge2$ edges and maximum degree at most $m^{3/4}$, with constant $1$; if $|W|\le cm$ and $p\le cm$; if its entries are in range; and if $E$ computes them within time and space $c(m+L+1)^c$.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 2.5, p.15

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_SubexpPrimes_NetDesc

set_option autoImplicit false

namespace SubexpPrimes

open OAI.Algorithms.SubexponentialSAT.Computation

/-- **The hypotheses of Theorem 2.5 on a network** — Gajulapalli, *Deterministic Construction of
Primes in Subexponential Time* (manuscript, sha256 6ad4d3de…), Theorem 2.5, p.15, with one
constant `c`: `m ≥ 2` edges; maximum degree at most `m^{3/4}`, with constant `1` as printed;
`w, p ≤ c m`; entries in range; and entry algorithm `E` running in time and space
`c (m + L + 1)^c`, where `L = |D.encode|`. -/
def NetDesc.Evaluable (D : NetDesc) (c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount)
    (T : D.Tables ℚ) : Prop :=
  2 ≤ D.m ∧ (D.maxDeg : ℝ) ≤ (D.m : ℝ) ^ ((3 : ℝ) / 4) ∧
  D.W.card ≤ c * D.m ∧ D.prec ≤ c * D.m ∧ D.EntriesInRange T ∧
  D.EntryComputes E outE T (polyBound c (D.m + D.encode.length))
    (polyBound c (D.m + D.encode.length))

end SubexpPrimes


