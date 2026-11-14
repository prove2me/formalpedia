-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_BaselineStop
-- name    : ConsistentSubmodular_Deterministic_Certificates_BaselineStop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:12:55.068664+00:00
-- url     : https://prove2.me/theorems/7447d2b7-99cd-4f7f-a561-0016c84969ef
-- title:
--   Persistence credit for atomic profiles (no new definitions)
-- statement:
--   This file introduces no new definitions. It works with an atomic profile $P$ with stages $0,\dots,m$, baseline $L_t$ (`baseline`), residual $r_{h,t}$ (`residual`), designated mass $A_t=r_{t,t}$ (`designated`), and benchmark $B_t=L_t+A_t$ (`benchmark`).
--
--   The single proved lemma, `persistence_credit`, states that for stages $h\le t$,
--   $$L_h+(A_t-r_{h,t})\le B_t-A_h,$$
--   which is a rewriting of the monotonicity of $L+r_{h,\cdot}$ (the baseline plus residual of stage $h$ at time $t$ dominates the benchmark at $h$) in terms of the benchmark.
--
--   This credit inequality is the form of persistence used when relays and exits of the deterministic $3/4$ certificate construction (Appendix B) are checked against the baseline budget.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/BaselineStop.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope

namespace ConsistentSubmodular

noncomputable section

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem persistence_credit (h t : Fin (m + 1)) (hht : h ≤ t) :
    P.baseline h + (P.designated t - P.residual h t) ≤
      P.benchmark t - P.designated h := by
  have hp := P.baseline_add_residual_monotone h hht
  change P.baseline h + P.designated h ≤ P.baseline t + P.residual h t at hp
  unfold benchmark
  linarith

end AtomicProfile

end

end ConsistentSubmodular


