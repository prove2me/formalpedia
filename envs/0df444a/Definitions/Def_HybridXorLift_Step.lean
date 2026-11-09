-- Prove2me | Definitions.Def_HybridXorLift_Step
-- name    : HybridXorLift_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:48.539518+00:00
-- url     : https://prove2.me/theorems/b3a1ae1c-ea07-4772-8401-487c97a10443
-- title:
--   Recorded outcome of a history
-- statement:
--   A **history** is the sequence of measurement outcomes along a path from the root of a hybrid algorithm. One entry of a history records an outcome $(a, v)$ of a parallel subroutine with $k$ slots, where $a = (a_1,\dots,a_k)$ are the slot labels and $v$ is the workspace index, as the pair consisting of the list $[a_1,\dots,a_k]$ and the number $v$.
--
--   **Formalization Note** This uniform record type lets histories of all depths be lists of the same type, whatever the slot and workspace sizes of the nodes they pass through.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.2 "Histories", p.10 (PDF p.12)

import Mathlib

namespace HybridXorLift

/-- The type in which one measurement outcome of a history is recorded (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.2 "Histories",
p.10 (PDF p.12)): an outcome `(a, v)` of a subroutine with `k` slots and workspace `Fin w` (slot
labels `a : Fin k → ι × Bool`, workspace index `v`) is stored as the list of its `k` slot labels
and the number `v`. A history is a list of steps. -/
abbrev Step (ι : Type) : Type := List (ι × Bool) × ℕ

end HybridXorLift


