-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Checkpoint
-- name    : ConsistentSubmodular_Deterministic_Certificates_Checkpoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:13.575056+00:00
-- url     : https://prove2.me/theorems/117573a7-676f-4bf1-9ed1-fa3e3bf091e6
-- title:
--   Checkpoint certificate for an atomic profile: common two-support point with entry and exit paths
-- statement:
--   Let $P$ be an atomic profile with stages $0,\dots,m$, benchmark $B_t$ (`benchmark`) and mixture value $V_t(p)$ (`value`) at a point $p$ of the simplex $\Delta$ on $\{0,\dots,m\}$. A path is a `PolygonalPath`, and `SafePath` $P\,t\,\ell\,\gamma$ means that every node and every point of every segment of $\gamma$ lies in $\Delta$ and has $V_t\ge\ell$.
--
--   - `CheckpointCertificate` $P$ is a structure whose fields witness the following:
--     - a checkpoint `point` $p\in\Delta$ (`simplex`) with support size at most $2$ (`support`, the number of nonzero coordinates);
--     - persistence at every stage: $\tfrac34B_t\le V_t(p)$ for all $t$ (`stages`);
--     - an `entry` path from the vertex $\delta_0$ to $p$ (`entry_initial`, `entry_terminal`) that is safe at stage $0$ at level $3/4$ (`entry_safe`);
--     - an `exit` path from $p$ to the vertex $\delta_m$ (`exit_initial`, `exit_terminal`) that is safe at the last stage at level $\tfrac34B_m$ (`exit_safe`);
--     - the combined piece budget $\#\text{entry pieces}+\#\text{exit pieces}\le (m+1)+2$ (`piece_budget`).
--
--   The structure packages proofs for the checkpoint, the prescribed endpoints, every node and segment, and the budget, so that a certificate exists exactly when the finite checkpoint statement holds.
--
--   It is the finite, atomic-profile form of the clairvoyant certificate of Definition 3.1 with $\alpha=3/4$ and $L=m+3$ (Theorem 7), used in the deterministic upper-bound argument of Section 3 and Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/Checkpoint.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SafePaths

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

/-- A witness contains proofs for the common checkpoint, prescribed endpoints,
every path node and segment, and the combined affine-piece budget. -/
structure CheckpointCertificate (P : AtomicProfile m atomCount) where
  point : Point m
  entry : PolygonalPath m
  exit : PolygonalPath m
  simplex : IsSimplex point
  support : supportCard point ≤ 2
  stages : ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤ P.value t point
  entry_initial : entry.node 0 = vertex 0
  entry_terminal : entry.node (Fin.last entry.pieces) = point
  exit_initial : exit.node 0 = point
  exit_terminal : exit.node (Fin.last exit.pieces) = vertex (Fin.last m)
  entry_safe : SafePath P 0 ((3 : ℝ) / 4) entry
  exit_safe : SafePath P (Fin.last m)
    ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) exit
  piece_budget : entry.pieces + exit.pieces ≤ (m + 1) + 2

end ConsistentSubmodular

end


