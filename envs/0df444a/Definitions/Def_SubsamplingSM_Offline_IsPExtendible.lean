-- Prove2me | Definitions.Def_SubsamplingSM_Offline_IsPExtendible
-- name    : SubsamplingSM_Offline_IsPExtendible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:51.862023+00:00
-- url     : https://prove2.me/theorems/56183963-2926-4cd3-bb0c-ba856ad4a1fe
-- title:
--   $p$-extendible system
-- statement:
--   An independence system $(N,\mathcal I)$ is **$p$-extendible** if for every $A\in\mathcal I$, every extension $B\in\mathcal I$ of $A$ (that is, $A\subseteq B$) and every element $e\notin A$ with $A\cup\{e\}\in\mathcal I$, there is a set $Y\subseteq B\setminus A$ with
--   $$|Y|\le p\qquad\text{and}\qquad (B\setminus Y)\cup\{e\}\in\mathcal I.$$
--
--   Informally, adding an element to an independent set requires removing at most $p$ other elements. Matroids are exactly the $1$-extendible systems, and $p$-extendible systems contain $p$-matchoids and intersections of $p$ matroids. Theorem 1 is stated for this class.
--
--   **Formalization Note** $p$ is a natural number; the statements that use the class assume $p\ge1$. The element $e$ may lie in $B$ (then $Y=\emptyset$ works), as on the page, which only asks $e\notin A$.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §3, p. 5

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsIndepSystem

namespace SubsamplingSM.Offline

/-- **p-extendible system.**
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §3, p. 5 (unnumbered): "An independence system is a p-extendible system if for all
`A ∈ I`, extension `B ∈ I` of `A` and element `e ∉ A` such that `A ∪ {e} ∈ I`, there
exists a set `Y ⊆ B \ A` with `|Y| ≤ p` such that `B \ Y ∪ {e} ∈ I`." An extension of
`A` is "an independent set `B ∈ I` that contains `A`" (p. 5).

`B \ Y ∪ {e}` is `insert e (B \ Y)`.

**Formalization Note.** `p : ℕ`; statements that use the predicate assume `1 ≤ p`
(paper.md Reading 3). The element `e` may lie in `B` (then `Y = ∅` works), exactly as on
the page, which only asks `e ∉ A`. -/
def IsPExtendible {α : Type*} [DecidableEq α] (I : Finset α → Prop) (p : ℕ) : Prop :=
  IsIndepSystem I ∧
    ∀ A B : Finset α, ∀ e : α, I A → I B → A ⊆ B → e ∉ A → I (insert e A) →
      ∃ Y ⊆ B \ A, Y.card ≤ p ∧ I (insert e (B \ Y))

end SubsamplingSM.Offline


