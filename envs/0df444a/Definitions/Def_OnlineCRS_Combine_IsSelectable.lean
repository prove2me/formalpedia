-- Prove2me | Definitions.Def_OnlineCRS_Combine_IsSelectable
-- name    : OnlineCRS_Combine_IsSelectable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:11.021649+00:00
-- url     : https://prove2.me/theorems/dc755fe3-33a2-4337-8b0a-1fd2a1ef8d6a
-- title:
--   $(b,c)$-selectability (Definition 1.5)
-- statement:
--   Let $b,c\in[0,1]$. A greedy OCRS $\pi$ for $P$ is **$(b,c)$-selectable** if for every $x\in b\cdot P=\{b\,y : y\in P\}$
--   $$\Pr\bigl[I\cup\{e\}\in\mathcal F_x\ \ \forall I\subseteq R(x),\ I\in\mathcal F_x\bigr]\ \ge\ c\qquad\text{for all } e\in N .$$
--
--   A $(b,c)$-selectable greedy OCRS selects every element with probability at least $c$ against an almighty adversary, provided the input is scaled down by $b$.
--
--   **Formalization Note** The ranges $b,c\in[0,1]$ are hypotheses of the theorems that use the predicate, not part of it.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.5, p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS
import Definitions.Def_OnlineCRS_Combine_selectProb
open Pointwise

namespace OnlineCRS.Combine

/-- **`(b, c)`-selectability (Definition 1.5).**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.5, p. 4: "Let `b, c ∈ [0,1]`. A greedy OCRS for `P` is `(b, c)`-selectable if
for any `x ∈ b · P` we have `Pr[I ∪ {e} ∈ F_x ∀ I ⊆ R(x), I ∈ F_x] ≥ c ∀ e ∈ N`."

`IsSelectable P π b c` says `selectProb π x e ≥ c` for every `x ∈ b • P` and every `e ∈ N`.

**Formalization Note.** `b • P = {b · y | y ∈ P}` (pointwise scaling). The ranges
`b, c ∈ [0,1]` of Definition 1.5 are hypotheses of the theorems that use this predicate. -/
def IsSelectable {N : Type*} [Fintype N] [DecidableEq N] {F : Finset (Finset N)}
    (P : Set (N → ℝ)) (π : GreedyOCRS F) (b c : ℝ) : Prop :=
  ∀ x ∈ b • P, ∀ e : N, c ≤ selectProb π x e

end OnlineCRS.Combine


