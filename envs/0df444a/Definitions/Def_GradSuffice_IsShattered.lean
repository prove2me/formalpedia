-- Prove2me | Definitions.Def_GradSuffice_IsShattered
-- name    : GradSuffice_IsShattered
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:08.352106+00:00
-- url     : https://prove2.me/theorems/cf4f591f-be19-4760-85fb-553d05b4f0ea
-- title:
--   Tree shattered by $W$ at margin $\theta$
-- statement:
--   Let $W\subseteq X$ and $\theta\in\mathbb R$. An adaptive sequence $\bar\xi=(\xi_1,\dots,\xi_m)$ (a binary tree of depth $m$ labelled by dual vectors) is **shattered by $W$ at margin $\theta$** if every branch is realized by a point of $W$ with margin $\theta$: for every $\sigma\in\{-1,1\}^m$ there is $w_\sigma\in W$ with
--   $$\sigma_i\,\langle\xi_i(\sigma_{<i}),w_\sigma\rangle\ge\theta\qquad(i=1,\dots,m).$$
--   Equivalently, the leaves can be labelled by points of $W$ so that every internal node's functional is $\le-\theta$ on the leaves of its left subtree and $\ge\theta$ on those of its right subtree.
--
--   Shattering is only meaningful together with a norm bound on the labels (for instance $B^\star$-valued trees), since rescaling the labels changes the margin.
--
--   **Formalization Note** The label bound is the separate condition `IsDualValued`.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §3.1, p.7, Eq. (6); §7, p.17

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_GradSuffice_signR

namespace GradSuffice

/-- **A tree shattered by `W` at margin `θ`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §3.1, p.7, Eq. (6): "the shattering
condition is that, for every `σ`, there exists `w_σ ∈ B` satisfying `σᵢ⟨ξᵢ(σ<ᵢ), w_σ⟩ ≥ θ` for every
`i = 1, …, m`", and its extension to a convex domain `W ⊆ X` (p.7: "the point realizing each
root-to-leaf branch belongs to `W`"; §7, p.17).

**Formalization Note.** Branches are sign strings `σ : Fin m → Bool` (`true ↦ +1`, the right
subtree), positions are 0-based, `σ<ᵢ` is `NondualOpt.histPrefix σ i`. The leaf-labelling form of
the definition (p.7) is the same condition, a leaf being a branch. Whether the labels lie in `B⋆` is
a separate condition (`IsDualValued`). -/
def IsShattered {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X) (θ : ℝ) {m : ℕ}
    (ξ : NondualOpt.Tree (StrongDual ℝ X) m) : Prop :=
  ∀ σ : Fin m → Bool, ∃ w ∈ W, ∀ i : Fin m, θ ≤ signR (σ i) * ξ i (NondualOpt.histPrefix σ i) w

end GradSuffice


