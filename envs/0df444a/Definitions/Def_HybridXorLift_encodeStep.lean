-- Prove2me | Definitions.Def_HybridXorLift_encodeStep
-- name    : HybridXorLift_encodeStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:55.387494+00:00
-- url     : https://prove2.me/theorems/07bb29bb-11cc-4f0b-839c-310abe187fde
-- title:
--   Recording an outcome in a history
-- statement:
--   The outcome $y = (a, v)$ of a subroutine with $k$ slots and workspace $[w]$ is recorded in a history as the pair $([a_1,\dots,a_k], v)$. For fixed $k$ and $w$ this record determines $y$. The child $hy$ of a history $h$ is $h$ followed by the record of $y$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.2 "Histories", p.10 (PDF p.12)

import Definitions.Def_HybridXorLift_Step

namespace HybridXorLift

/-- The record of a measurement outcome `y = (a, v)` in a history (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.2 "Histories", p.10
(PDF p.12)): the list `[a_1, …, a_k]` of slot labels and the workspace index `v`. For fixed `k`
and `w` it is injective. -/
def encodeStep {ι : Type} {k w : ℕ} (y : (Fin k → ι × Bool) × Fin w) : Step ι :=
  (List.ofFn y.1, (y.2 : ℕ))

end HybridXorLift


