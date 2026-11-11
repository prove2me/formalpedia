-- Prove2me | Definitions.Def_ConantTerry_Orders_function_tree
-- name    : ConantTerry_Orders_function_tree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:46.131195+00:00
-- url     : https://prove2.me/theorems/c8bd98b1-0a9f-4b03-8c30-74af27507952
-- title:
--   Trees coded in a unit-interval-valued function
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, $t$ a height, and $\gamma$ a real scale. A tree witness consists of labels $x:B_{<t}\to X$, $y:B_t\to Y$ and thresholds $r:B_{<t}\to[0,1]$. It satisfies the tree condition if, for every $\sigma\in B_{<t}$ and every pair $\eta,\eta'\in B_t$,
--   $$
--   \sigma\mathbin{{}^\frown}0\unlhd\eta\ \wedge\
--   \sigma\mathbin{{}^\frown}1\unlhd\eta'
--   \quad\Longrightarrow\quad
--   f(x_\sigma,y_\eta)\le r_\sigma\ \wedge\
--   f(x_\sigma,y_{\eta'})\ge r_\sigma+\gamma.
--   $$
--   The predicate $\operatorname{AdmitsTree}(f,t,\gamma)$ asserts existence of these three sequences. All pairs of opposite-branch leaves are included. The thresholds may vary freely between nodes, and labels need not be distinct.
--
--   This is the tree configuration used by every function-theoretic statement in the mission. The source uses positive heights and scales; each theorem carries these restrictions explicitly, while the defining predicate itself is meaningful at every natural height and real scale.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.2, Definition 1.2; p.6, §1.6(6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib
import Definitions.Def_ConantTerry_Orders_binary_words

namespace ConantTerry.Orders

/-- Definition 1.2, p.2: all pairs of opposite-branch leaves are tested.
`false` denotes bit 0 and `true` denotes bit 1. Heights and scales are
restricted in the theorem statements, rather than built into this predicate. -/
def IsFunctionTree {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (t : ℕ) (γ : ℝ)
    (x : WordsBelow t → X) (y : WordsAt t → Y)
    (r : WordsBelow t → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ (σ : WordsBelow t) (η η' : WordsAt t),
    List.IsPrefix (σ.val ++ [false]) η.val →
    List.IsPrefix (σ.val ++ [true]) η'.val →
      (f (x σ, y η) : ℝ) ≤ (r σ : ℝ) ∧
      (r σ : ℝ) + γ ≤ (f (x σ, y η') : ℝ)

/-- Admission means existence of the source's three sequences (§1.6(6), p.6). -/
def AdmitsTree {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (t : ℕ) (γ : ℝ) : Prop :=
  ∃ (x : WordsBelow t → X) (y : WordsAt t → Y)
    (r : WordsBelow t → Set.Icc (0 : ℝ) 1), IsFunctionTree f t γ x y r

end ConantTerry.Orders


