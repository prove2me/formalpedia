-- Prove2me | Definitions.Def_NondetConn_Supplement_isEulerian
-- name    : NondetConn_Supplement_isEulerian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:09:12.163136+00:00
-- url     : https://prove2.me/theorems/10b046ff-cf2c-4c01-8306-80654e7479c8
-- title:
--   Eulerian finite simple graph
-- statement:
--   A finite simple graph is **Eulerian** when it is connected and every vertex has even degree.
--
--   This is exactly the characterization used in the proof of Theorem 6.2, where every vertex of the reduction graph has degree two.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), proof of Theorem 6.2, p.26 (PDF p.28)

import Mathlib

set_option autoImplicit false

namespace NondetConn.Supplement

/-- A finite simple graph is Eulerian when it is connected and every vertex has even
degree, the convention used in the proof of Zhang's Theorem 6.2. -/
noncomputable def isEulerian {V : Type} [Fintype V] (G : SimpleGraph V) : Prop := by
  classical
  exact G.Connected ∧ ∀ v, Even (G.degree v)

end NondetConn.Supplement


