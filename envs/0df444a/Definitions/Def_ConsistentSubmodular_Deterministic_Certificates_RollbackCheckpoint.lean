-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RollbackCheckpoint
-- name    : ConsistentSubmodular_Deterministic_Certificates_RollbackCheckpoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:16:09.012852+00:00
-- url     : https://prove2.me/theorems/61ba0cfe-5ed7-4ff5-84f1-742364de36e2
-- title:
--   Checkpoint certificate by rollback to a parent: one added entry segment, sufficient two-piece exit
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$, let $h$ be a stage with a relay history $H$ (parent $a = $ `H.parent` $< h$, parameter $q = $ `H.parameter`), and assume $0 \le q \le 4$, that the sufficient eligibility of $a$ at $q$ is nonnegative at $h$, and that for every $t \ge h$ the sufficient row dominates, $\tfrac34\,\mathrm{benchmark}_t \le \mathrm{suffRow}(a,h,t,q)$. Here $\mathrm{suffRow}(a,h,t,q) = \mathrm{baseline}_t + (1 - \tfrac q4)\,\mathrm{residual}(a,t) + \tfrac q4\,\mathrm{residual}(h,t) - \tfrac14\min\{\mathrm{residual}(a,t),\mathrm{residual}(h,t)\}$.
--
--   - `checkpoint_of_rollback` produces a `CheckpointCertificate` for $P$ with point $p = (1-\tfrac q4)\,\delta_a + \tfrac q4\,\delta_h$ (a point of support at most two on the edge between the parent and the child vertex). Its entry path is the parent's access path followed by the single segment from $\delta_a$ to $p$, and its exit path is a path of at most two segments from $p$ to $\delta_m$ supplied by a terminal sufficient row. The piece budget is $(m+1)+2$.
--
--   This is the rollback branch of the selector: the child keeps the original parent's access history and adds one affine entry piece. It is used in the construction of $(3/4, m+3)$-certificates (Theorem 7).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RollbackCheckpoint.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffConstructor
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

/-- A rollback keeps the original parent's access history and adds one affine
entry piece. A terminal sufficient row supplies the two-piece exit. -/
def checkpoint_of_rollback (hP : P.Canonical) (h : Fin (m + 1)) (H : RelayHistory P h)
    (hk0 : 0 ≤ H.parameter) (hk4 : H.parameter ≤ 4)
    (helig : 0 ≤ P.suffEligibility H.parent H.parameter h)
    (hlater : ∀ t, h ≤ t → (3 : ℝ) / 4 * P.benchmark t ≤
      LowRollback.suffRow P H.parent h t H.parameter) : CheckpointCertificate P := by
  let p := mix (vertex H.parent) (vertex h) (H.parameter / 4)
  let finalEntry := PolygonalPath.segment (vertex H.parent) p
  have hfinalsafe := P.suff_pair_entry hP H.parent h H.advances H.parameter hk0 hk4 helig
  have hjoin : H.parent_access.entry.node (Fin.last H.parent_access.entry.pieces) =
      finalEntry.node 0 := by simpa [finalEntry] using H.parent_access.terminal
  have hexit := P.suff_terminal_exit hP H.parent h (H.parameter / 4)
    (by positivity) (by linarith) (hlater _ (Fin.le_last h))
  let exit := Classical.choose hexit
  have hexit0 := (Classical.choose_spec hexit).1
  have hexit1 := (Classical.choose_spec hexit).2.1
  have hexitsafe := (Classical.choose_spec hexit).2.2.1
  have hexitpieces := (Classical.choose_spec hexit).2.2.2
  change exit.pieces ≤ 2 at hexitpieces
  refine {
    point := p
    entry := PolygonalPath.append H.parent_access.entry finalEntry
    exit := exit
    simplex := (simplex_vertex _).mix (simplex_vertex _) (by positivity) (by linarith)
    support := supportCard_mix_vertices _ _ _
    stages := ?_
    entry_initial := by rw [PolygonalPath.append_initial, H.parent_access.initial]
    entry_terminal := by
      rw [PolygonalPath.append_terminal _ _ hjoin]
      exact PolygonalPath.segment_terminal _ _
    exit_initial := hexit0
    exit_terminal := hexit1
    entry_safe := H.parent_access.safe.append hfinalsafe hjoin
    exit_safe := hexitsafe
    piece_budget := ?_ }
  · intro t
    by_cases hht : h ≤ t
    · exact (hlater t hht).trans (P.value_mix_vertices_sufficient t H.parent h
        (ne_of_lt H.advances) (by positivity) (by linarith)
        (le_min (P.overlap_le_left _ _ _) (P.overlap_le_right _ _ _)))
    · by_cases ha : P.Active t
      · apply P.suff_pair_prefix H.parent h t (ne_of_lt H.advances) H.parameter hk0 hk4
          (le_of_not_ge hht) helig
        by_cases hta : t ≤ H.parent
        · exact P.envelopeSlack_early hP _ _ _ hta
        · exact H.envelope t (lt_of_not_ge hta) ha
      · exact P.inactive_stage_safe t
          ((simplex_vertex _).mix (simplex_vertex _) (by positivity) (by linarith))
          (le_of_not_gt ha)
  · change H.parent_access.entry.pieces + 1 + exit.pieces ≤ (m + 1) + 2
    have hp := H.parent_access.pieces
    have := H.parent.isLt
    omega

end AtomicProfile

end ConsistentSubmodular

end


