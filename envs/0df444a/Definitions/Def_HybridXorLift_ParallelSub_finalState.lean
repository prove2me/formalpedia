-- Prove2me | Definitions.Def_HybridXorLift_ParallelSub_finalState
-- name    : HybridXorLift_ParallelSub_finalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:35.101134+00:00
-- url     : https://prove2.me/theorems/26b8b67a-af75-4863-8786-d215a4559fb4
-- title:
--   Final state $V_h O_{h,x} |\phi_h\rangle$ of a parallel subroutine
-- statement:
--   For a parallel subroutine with prepared state $|\phi\rangle$ and processing unitary $V$, and an input $x$, the **final state** is
--   $$
--   V\, O^{(k)}_x\, |\phi\rangle ,
--   $$
--   the state that is measured in the computational basis at the end of the subroutine.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.1, Eq. (3.1), p.11 (PDF p.13)

import Definitions.Def_HybridXorLift_ParallelSub
import Definitions.Def_HybridXorLift_parallelOracle

namespace HybridXorLift

/-- The state `V_h O_{h,x} |ϕ_h⟩` of a parallel subroutine just before its complete measurement
(Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.1, Eq. (3.1), p.11 (PDF p.13), and Definition 2.2, p.9 (PDF p.11)). -/
noncomputable def ParallelSub.finalState {ι : Type} [Fintype ι] [DecidableEq ι] {k w : ℕ}
    (S : ParallelSub ι k w) (x : ι → Bool) : EuclideanSpace ℂ ((Fin k → ι × Bool) × Fin w) :=
  QAlgorithms.act (S.V : Matrix _ _ ℂ) (QAlgorithms.act (parallelOracle k w x) S.start)

end HybridXorLift


