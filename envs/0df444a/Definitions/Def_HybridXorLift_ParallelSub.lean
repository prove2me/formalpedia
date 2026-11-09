-- Prove2me | Definitions.Def_HybridXorLift_ParallelSub
-- name    : HybridXorLift_ParallelSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:02.780345+00:00
-- url     : https://prove2.me/theorems/caf55f55-67e2-4053-b4c2-465da6f559d0
-- title:
--   Parallel subroutine with $k$ slots (Definition 2.2)
-- statement:
--   A **parallel subroutine with $k$ slots** prepares an input-independent unit state $|\phi\rangle$ on $k$ separate query registers, each of the form $\iota \times \{0,1\}$ (an address and a control bit), and a workspace $[w]$; it then applies $k$ controlled phase queries on the $k$ registers at the same time, an input-independent unitary $V$, and a complete measurement in the computational basis. The prepared state may entangle the query registers with each other and with the workspace.
--
--   **Formalization Note** The $k$ registers are the coordinates of a tuple $a = (a_1,\dots,a_k) \in (\iota \times \{0,1\})^k$. The processing and measurement are in the refined form of §2.2 (an isometry followed by a complete measurement is a unitary on a larger workspace followed by a computational-basis measurement).
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.2, p.9 (PDF p.11); refinement of §2.2, p.10 (PDF p.12)

import Definitions.Def_QAlgorithms_Defs_Basic

namespace HybridXorLift

/-- A parallel subroutine with `k` slots (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.2, p.9 (PDF p.11), refined as in
§2.2, p.10 (PDF p.12)): an input-independent unit state `start` on `k` query registers
`ι × Bool` (slot `ℓ` holds an address and a control bit) and a workspace `Fin w`, which may
entangle the registers with each other and with the workspace, followed (after the `k` parallel
queries) by an input-independent unitary `V` and a complete measurement in the computational
basis.

**Formalization Note** The `k` registers are the coordinates of `Fin k → ι × Bool`. As in
`HybridAlg`, the processing and measurement are in the refined form of §2.2 (an isometry
followed by a complete measurement equals a unitary on a larger workspace followed by a
computational-basis measurement). -/
structure ParallelSub (ι : Type) [Fintype ι] [DecidableEq ι] (k w : ℕ) where
  /-- the prepared input-independent state `|ϕ⟩` -/
  start : EuclideanSpace ℂ ((Fin k → ι × Bool) × Fin w)
  /-- it is a unit vector -/
  start_unit : ‖start‖ = 1
  /-- the input-independent processing after the queries -/
  V : Matrix.unitaryGroup ((Fin k → ι × Bool) × Fin w) ℂ

end HybridXorLift


