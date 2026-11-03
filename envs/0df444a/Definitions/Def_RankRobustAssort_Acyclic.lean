-- Prove2me | Definitions.Def_RankRobustAssort_Acyclic
-- name    : RankRobustAssort_Acyclic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:39.525281+00:00
-- url     : https://prove2.me/theorems/90d94072-1f6b-4478-8086-f7a5535ab481
-- title:
--   Acyclicity of $\mathcal G_{i_1\cdots i_M}$
-- statement:
--   The graph $\mathcal G_{i_1\cdots i_M}$ is **acyclic** when it has no directed cycle, i.e. no vertex $a$ has a directed path (of at least one edge) from $a$ back to $a$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, Lemma EC.1, p.ec14 and Definition EC.1, p.ec15

import Mathlib
import Definitions.Def_RankRobustAssort_edge

namespace RankRobustAssort

/-- The directed graph `𝒢_{i₁⋯i_M}` is acyclic: no vertex lies on a directed cycle, i.e. there is
no directed path (of at least one edge) from a vertex to itself.

Sturt, arXiv:2112.05010v4, Lemma EC.1, p.ec14, and the remark after Definition EC.1, p.ec15.

Formalization Note: a cycle through `a` is a `Relation.TransGen (edge P t) a a`; self-loops
cannot occur since edges have `a ≠ t m`. -/
def Acyclic {n M : ℕ} (P : Problem n M) (t : Fin M → Fin (n + 1)) : Prop :=
  ∀ a, ¬ Relation.TransGen (edge P t) a a

end RankRobustAssort


