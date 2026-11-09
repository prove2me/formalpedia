-- Prove2me | Definitions.Def_PrivateUniformGen_Characterization_Branching
-- name    : PrivateUniformGen_Characterization_Branching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:07.457021+00:00
-- url     : https://prove2.me/theorems/797b537f-ba1d-4727-b070-f5c21dd3d4d2
-- title:
--   Infinite-intersection closure, nested branching trees and ranks
-- statement:
--   The infinite-intersection closure $C^\cap_\infty$ consists of the infinite sets obtained as intersections of nonempty subfamilies of $C$. A nested branching tree of depth $d$ has $d$ nodes on every root-to-leaf path, labels in this closure, each child label contained in its parent, and finite intersection of all child labels at each internal node. An arity bound $k$ restricts each internal node to at most $k$ children; infinity permits arbitrary cardinality.
--
--   $$\rho_k(C,K)=\sup\{d:\text{a $k$-ary tree of depth $d$ is rooted at $K$}\},\qquad \operatorname{NBDim}_k(C)=\sup_{K\in C^\cap_\infty}\rho_k(C,K).$$
--
--   Unrestricted arity gives $\rho$ and $\operatorname{NBDim}$. The existence predicate is inductive: a leaf has depth one; a branch attaches depth-$d$ trees indexed by a nonempty set of child labels. Repeated equal labels can be merged without changing existence or the intersection. This retains uncountable branching. Ranks are extended naturals, with zero for no tree and infinity for unbounded depths.
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Section 4 and Definitions 4.1–4.4, pp. 9–10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Languages

namespace PrivateUniformGen.Characterization

/-- Section 4, p. 9: nonempty, possibly infinite intersections that remain infinite. -/
def infiniteClosure {X : Type*} (C : LanguageClass X) : Set (Set X) :=
  {K | K.Infinite ∧ ∃ F : Set (Set X), F.Nonempty ∧ F ⊆ C.languages ∧ K = ⋂₀ F}

/-- Definition 4.1: existence of a tree, encoded by its set of child labels.
    arity = top permits even uncountably many children; depth counts nodes. -/
inductive HasTree {X : Type*} (C : LanguageClass X) (arity : ℕ∞) : ℕ → Set X → Prop
  | leaf (K : Set X) (hK : K ∈ infiniteClosure C) : HasTree C arity 1 K
  | branch {d : ℕ} {K : Set X} (hd : 1 ≤ d) (hK : K ∈ infiniteClosure C)
      (F : Set (Set X)) (hne : F.Nonempty) (hcard : F.encard ≤ arity)
      (hsub : ∀ T ∈ F, T ⊆ K) (htree : ∀ T ∈ F, HasTree C arity d T)
      (hfin : (⋂₀ F).Finite) : HasTree C arity (d + 1) K

/-- Definition 4.2, pp. 9-10; no finite/unbounded supremum defaults. -/
noncomputable def rank {X : Type*} (C : LanguageClass X) (arity : ℕ∞) (K : Set X) : ℕ∞ :=
  ⨆ (d : ℕ) (_ : HasTree C arity d K), (d : ℕ∞)

/-- Definition 4.4, p. 10; arity = top gives NBDim, arity = 2 gives NBDim_2. -/
noncomputable def nbDim {X : Type*} (C : LanguageClass X) (arity : ℕ∞) : ℕ∞ :=
  ⨆ (K : Set X) (_ : K ∈ infiniteClosure C), rank C arity K

end PrivateUniformGen.Characterization


