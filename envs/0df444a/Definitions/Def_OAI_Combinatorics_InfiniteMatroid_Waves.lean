-- Prove2me | Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves
-- name    : OAI_Combinatorics_InfiniteMatroid_Waves
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T05:20:12.767883+00:00
-- url     : https://prove2.me/theorems/50bc6bb3-f142-4b24-b03c-11ff7eadd3d0
-- title:
--   Waves of a family of matroids
-- statement:
--   Let $(M_i)_{i\in\iota}$ be a family of matroids on a common set $\alpha$, indexed by an arbitrary set $\iota$, and let $F\subseteq\alpha$. For a matroid $M$ write $\operatorname{cl}_M$ for its closure operator and $E(M)$ for its ground set.
--
--   1. **Wave.** A *wave* of $(M_i)_{i\in\iota}$ in $F$ is a pair $W=(X,(S_i)_{i\in\iota})$ of subsets of $\alpha$ such that
--   $$X\subseteq F,\qquad S_i\subseteq X\ \ (i\in\iota),\qquad S_i\cap S_j=\emptyset\ \ (i\neq j),\qquad X\subseteq\operatorname{cl}_{M_i}(S_i)\ \ (i\in\iota).$$
--   In words, $X$ carries a packing of pairwise disjoint sets $S_i$, the set $S_i$ spanning $X$ in the matroid $M_i$. Waves are compared componentwise: $(X,S)\le(X',S')$ means $X\subseteq X'$ and $S_i\subseteq S'_i$ for every $i$.
--   2. **Contraction onto a set.** For a matroid $M$ on $\alpha$ and $C\subseteq\alpha$, the base definitions introduce the contraction onto $C$,
--   $$M.C=\bigl(M^{*}|C\bigr)^{*},$$
--   the dual of the restriction of the dual matroid $M^*$ to $C$. This file records that its ground set is $E(M.C)=C$. When $C\subseteq E(M)$, the matroid $M.C$ is the contraction $M/(E(M)\setminus C)$.
--
--   Waves organize the packing side of the packing/covering problem for a family of matroids that all have ground set $F$. A maximal wave $(X,S)$ (a separate result shows that one always exists) leaves no room for further packings: for no nonempty $Y\subseteq F\setminus X$ do the restrictions of the contractions $M_i/X$ to $Y$ admit pairwise disjoint spanning sets, so the covering condition on $F\setminus X$ holds trivially. For a pair of matroids, if in addition $F\setminus X$ could be covered by sets independent in the contractions $M_i/X$, then the wave and that covering would form a packing/covering decomposition. This is how, for two matroids without such a decomposition, the residual pair $(M_i/X)$ on $F\setminus X$ becomes a counterexample to the covering conjecture.
--
--   **Formalization Note** `Wave M F W` takes `W : Set α × (ι → Set α)`; maximality of a wave refers to the product order on this type, i.e. componentwise inclusion. Mathlib's closure $\operatorname{cl}_M(S)$ is always contained in $E(M)$, so the last condition also forces $X\subseteq E(M_i)$. `contractOnto M C` is `(M.dual ↾ C).dual` in the base definitions and `contractOnto_ground` is the simp lemma for its ground set; since Mathlib's restriction allows $C\not\subseteq E(M)$, elements of $C\setminus E(M)$ become coloops of $M.C$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Waves.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Waves.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the InfiniteMatroidCorollaries mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

def Wave {α ι : Type*} (M : ι → Matroid α) (F : Set α)
    (W : Set α × (ι → Set α)) : Prop :=
  W.1 ⊆ F ∧ (∀ i, W.2 i ⊆ W.1) ∧
    (Pairwise fun i j ↦ Disjoint (W.2 i) (W.2 j)) ∧
    ∀ i, W.1 ⊆ (M i).closure (W.2 i)

@[simp] lemma contractOnto_ground {α : Type*} (M : Matroid α) (C : Set α) :
    (contractOnto M C).E = C := rfl

end InfiniteMatroidCounterexample

end OAI


