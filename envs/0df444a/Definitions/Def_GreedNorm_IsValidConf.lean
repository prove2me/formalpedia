-- Prove2me | Definitions.Def_GreedNorm_IsValidConf
-- name    : GreedNorm_IsValidConf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:45.730039+00:00
-- url     : https://prove2.me/theorems/a5c1f407-8e1d-47f1-ac19-1482747ffbd0
-- title:
--   Valid configuration set
-- statement:
--   A configuration set $\mathcal A$ is **valid** if it contains at most one configuration of each type $i\in[m]$.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 Constraints on configuration sets, p.8 (PDF 10)

import Mathlib

namespace GreedNorm

/-- **Valid configuration set**: at most one configuration of each type.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 "Constraints on configuration sets", p.8 (PDF 10): "A configuration set A is said to be
valid if it contains at most one configuration of each type."

**Formalization Note** Configurations are pairs `(i, S) : Fin m × Finset U`, `i` the type. -/
def IsValidConf {m : ℕ} {U : Type} (A : Finset (Fin m × Finset U)) : Prop :=
  ∀ i : Fin m, (A.filter (fun c => c.1 = i)).card ≤ 1

end GreedNorm


