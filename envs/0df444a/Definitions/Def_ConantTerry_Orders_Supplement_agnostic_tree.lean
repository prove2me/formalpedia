-- Prove2me | Definitions.Def_ConantTerry_Orders_Supplement_agnostic_tree
-- name    : ConantTerry_Orders_Supplement_agnostic_tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:24:22.00561+00:00
-- url     : https://prove2.me/theorems/f5bb04da-51fa-4896-a016-eb33e83473e5
-- title:
--   Agnostic function trees
-- statement:
--   For arbitrary sets $X,Y$, let $f:X\times Y\to[0,1]$. Given an integer $t\ge1$ and a real $\gamma>0$, an agnostic $(t,\gamma)$-tree has labels $x_\sigma\in X$ for binary words $\sigma$ of length less than $t$ and $y_\eta\in Y$ for binary words $\eta$ of length $t$. For every internal word $\sigma$ and every pair of leaves $\eta,\eta'$ extending its respective $0$ and $1$ children, it satisfies
--   $$
--   \left|f(x_\sigma,y_\eta)-f(x_\sigma,y_{\eta'})\right|\ge\gamma.
--   $$
--   Admission is existence of the two labeling maps. There are no thresholds or fixed low/high orientations. This supplies the input predicate for Theorem 5.2 and reuses the published finite binary word types.
--
--   **Formalization Note** The inequality tests every pair of opposite-branch leaves, not only siblings or a selected pair. The predicate is defined for all heights and scales; Theorem 5.2 imposes the positive source domain.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 19, Definition 5.1

import Mathlib
import Definitions.Def_ConantTerry_Orders_binary_words

namespace ConantTerry.Orders.Supplement

/-- Definition 5.1, p.19. All pairs of opposite-branch leaves are tested.
There is no threshold, low/high orientation, or ordinary-tree assumption. -/
def IsAgnosticTree {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (t : ℕ) (γ : ℝ)
    (x : WordsBelow t → X) (y : WordsAt t → Y) : Prop :=
  ∀ (σ : WordsBelow t) (η η' : WordsAt t),
    List.IsPrefix (σ.val ++ [false]) η.val →
    List.IsPrefix (σ.val ++ [true]) η'.val →
      γ ≤ |(f (x σ, y η) : ℝ) - (f (x σ, y η') : ℝ)|

/-- Existence of the two labeling maps in Definition 5.1. -/
def AdmitsAgnosticTree {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (t : ℕ) (γ : ℝ) : Prop :=
  ∃ (x : WordsBelow t → X) (y : WordsAt t → Y), IsAgnosticTree f t γ x y

end ConantTerry.Orders.Supplement


