-- Prove2me | Definitions.Def_TIESharp_overlap
-- name    : TIESharp_overlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:07.917365+00:00
-- url     : https://prove2.me/theorems/3c5aeec4-4f70-4a82-8365-d6319acad0a7
-- title:
--   Job–slot entry of the slot matrix
-- statement:
--   Machine $i$'s list of intervals is divided into **slots** of capacity one, slot $k$ being $[k,k+1)$, $k=0,1,2,\dots$ The job–slot entry is the length of the overlap of job $j$'s interval with the slot,
--   $$\mathrm{ov}_{i}(j,k)=\big|[c_{ij},c_{ij}+q_{ij})\cap[k,k+1)\big|,$$
--   and $0$ for jobs with $q_{ij}=0$. Each job's entries over all slots of all machines sum to one; only the last slot of a machine can have a deficit.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10

import Mathlib
import Definitions.Def_TIESharp_bsProb
import Definitions.Def_TIESharp_slotStart

set_option autoImplicit false

namespace TIESharp

/-- The **job–slot entry** of the slot matrix (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, §3.2, p.10): machine `i`'s list is divided "into slots of capacity
one", slot `k` being `[k, k + 1)`, and "Its job–slot entry is the length of their overlap", i.e.
the length of `[c, c + q_ij) ∩ [k, k + 1)` with `c = slotStart t i j`. Jobs with `q_ij = 0` are not
in machine `i`'s list and have entry `0`.

**Formalization Note.** Slots of machine `i` are indexed by `k : ℕ`; entries vanish beyond the last
slot `⌈Σ_j q_ij⌉ − 1`. -/
noncomputable def overlap {n m : ℕ} (t : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) (k : ℕ) : ℝ :=
  if 0 < bsProb t i j then
    max 0 (min (slotStart t i j + bsProb t i j) ((k : ℝ) + 1) - max (slotStart t i j) (k : ℝ))
  else 0

end TIESharp


