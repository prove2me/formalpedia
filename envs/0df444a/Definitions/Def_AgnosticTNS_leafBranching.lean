-- Prove2me | Definitions.Def_AgnosticTNS_leafBranching
-- name    : AgnosticTNS_leafBranching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:21.875234+00:00
-- url     : https://prove2.me/theorems/227af83a-e125-4b76-9b05-359f059b3c71
-- title:
--   Branching $b$ of a tree rooted at a leaf
-- statement:
--   For a tree $T$ rooted at a leaf $\ell$, the children of a vertex $v$ are its neighbours $u$ with $\mathrm{dist}(\ell,u)=\mathrm{dist}(\ell,v)+1$. The branching $b$ is "the maximum number of children after rooting $T$ at a leaf"; `leafBranching T` is the least such maximum over the leaves of $T$.
--
--   **Formalization Note** The page does not name the leaf; with the minimum over leaves, a bound stated for trees with `leafBranching T ≤ b` covers every tree that has some leaf of branching at most $b$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 5.1, p.39

import Mathlib

namespace AgnosticTNS

/-- **The branching `b` of a tree rooted at a leaf**, Corollary 5.1, p.39 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): "the maximum
number of children after rooting `T` at a leaf". Rooted at `ℓ`, the children of `v` are its
neighbours `u` with `dist(ℓ, u) = dist(ℓ, v) + 1`; `leafBranching T` is the least, over leaves `ℓ`
(degree one), of the maximum number of children.

**Formalization Note** The page does not name the leaf; the minimum over leaves is the reading under
which the learner may pick the leaf, and every bound stated with `leafBranching T ≤ b` covers the
trees with some leaf of branching `≤ b`. -/
noncomputable def leafBranching {n : ℕ} (T : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact sInf {b | ∃ ℓ, T.degree ℓ = 1 ∧
    b = Finset.univ.sup fun v =>
      (Finset.univ.filter fun u => T.Adj v u ∧ T.dist ℓ u = T.dist ℓ v + 1).card}

end AgnosticTNS


