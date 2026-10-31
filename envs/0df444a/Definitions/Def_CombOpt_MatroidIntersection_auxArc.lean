-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_auxArc
-- name    : CombOpt_MatroidIntersection_auxArc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:08:29.225602+00:00
-- url     : https://prove2.me/theorems/7d5eee4d-37fc-4825-9842-12d640b31576
-- title:
--   Arcs of the auxiliary digraph $G(M_1,M_2,J)$
-- statement:
--   Let $M_1=(S,\mathcal I_1)$ and $M_2=(S,\mathcal I_2)$ be matroids on $S$ and $J\subseteq S$ (in §8.3, $J\in\mathcal I_1\cap\mathcal I_2$). The **auxiliary digraph** $G=G(M_1,M_2,J)$ has node set $S\cup\{r,s\}$ and arcs
--
--   1. $es$ for every $e\in S\setminus J$ such that $J\cup\{e\}\in\mathcal I_1$;
--   2. $re$ for every $e\in S\setminus J$ such that $J\cup\{e\}\in\mathcal I_2$;
--   3. $ef$ for every $e\in S\setminus J$, $f\in J$ such that $J\cup\{e\}\notin\mathcal I_1$ and $(J\cup\{e\})\setminus\{f\}\in\mathcal I_1$;
--   4. $fe$ for every $e\in S\setminus J$, $f\in J$ such that $J\cup\{e\}\notin\mathcal I_2$ and $(J\cup\{e\})\setminus\{f\}\in\mathcal I_2$.
--
--   There are no other arcs. An $(r,s)$-dipath in $G$ corresponds to an augmenting sequence for $J$.
--
--   **Formalization Note** The digraph is given by its arc relation: `auxArc M₁ M₂ J u v` holds iff $uv$ is an arc. No two arcs of $G$ share both tail and head, so the relation determines $G$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.3, p. 290 (PDF p. 297)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersection_Matroid
import Definitions.Def_CombOpt_MatroidIntersection_AuxNode

namespace CombOpt.MatroidIntersection

/-- **The arcs of the auxiliary digraph `G(M₁, M₂, J)`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.3,
p. 290 (PDF p. 297): "It has node-set S ∪ {r, s}, and arcs:
• es for every e ∈ S\J such that J ∪ {e} ∈ I₁;
• re for every e ∈ S\J such that J ∪ {e} ∈ I₂;
• ef for every e ∈ S\J, f ∈ J such that J ∪ {e} ∉ I₁, (J ∪ {e})\{f} ∈ I₁;
• fe for every e ∈ S\J, f ∈ J such that J ∪ {e} ∉ I₂, (J ∪ {e})\{f} ∈ I₂."

`auxArc M₁ M₂ J u v` holds exactly when `uv` is an arc (from `u` to `v`) of `G(M₁, M₂, J)`:
1. `elem e → s` when `e ∉ J` and `J ∪ {e}` is independent in `M₁`;
2. `r → elem e` when `e ∉ J` and `J ∪ {e}` is independent in `M₂`;
3. `elem e → elem f` when `e ∉ J`, `f ∈ J`, `J ∪ {e}` is dependent in `M₁` and
   `(J ∪ {e}) \ {f}` is independent in `M₁`;
4. `elem f → elem e` when `e ∉ J`, `f ∈ J`, `J ∪ {e}` is dependent in `M₂` and
   `(J ∪ {e}) \ {f}` is independent in `M₂`.
There are no other arcs.

**Formalization Note.** The digraph is given by its arc relation. Distinct arcs of the book's
`G` have distinct (tail, head) pairs (an `ef` arc has its tail outside `J`, an `fe` arc inside),
so a relation loses nothing. In the theorems `J` is a common independent set, as in §8.3. -/
def auxArc {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : Matroid S) (J : Finset S) :
    AuxNode S → AuxNode S → Prop
  | .elem e, .s => e ∉ J ∧ M₁.Indep (insert e J)
  | .r, .elem e => e ∉ J ∧ M₂.Indep (insert e J)
  | .elem x, .elem y =>
      (x ∉ J ∧ y ∈ J ∧ ¬ M₁.Indep (insert x J) ∧ M₁.Indep ((insert x J).erase y)) ∨
      (y ∉ J ∧ x ∈ J ∧ ¬ M₂.Indep (insert y J) ∧ M₂.Indep ((insert y J).erase x))
  | _, _ => False

end CombOpt.MatroidIntersection


