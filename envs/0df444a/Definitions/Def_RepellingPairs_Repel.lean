-- Prove2me | Definitions.Def_RepellingPairs_Repel
-- name    : RepellingPairs_Repel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:40.609381+00:00
-- url     : https://prove2.me/theorems/7e871a12-a1d7-46c7-9fd9-fc4caa7f57f1
-- title:
--   Repelling terminal pairs
-- statement:
--   Terminal pairs $(s,t)$ and $(u,v)$ **repel** if
--
--   $$
--   D(s,t)+D(u,v)<\max\{D(s,u)+D(t,v),\ D(s,v)+D(u,t)\}.
--   $$
--
--   The four endpoints need not be distinct, and the repeated pair $(t,t)$ is allowed. By Lemma 5, shortest paths of two repelling pairs cannot intersect in any graph realizing $D$.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §2, pp.5–6

import Mathlib

set_option autoImplicit false

namespace RepellingPairs

/-- Terminal pairs `(s, t)` and `(u, v)` repel: `D(s, t) + D(u, v) < max{D(s, u) + D(t, v),
D(s, v) + D(u, t)}`. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §2, p.5.

**Formalization Note.** The four indices are arbitrary: "not necessarily with four distinct endpoints",
and the repeated pair `(t, t)` is allowed (p.6). -/
def Repel {k : ℕ} (D : Fin k → Fin k → ℝ) (s t u v : Fin k) : Prop :=
  D s t + D u v < max (D s u + D t v) (D s v + D u t)

end RepellingPairs


