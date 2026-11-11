-- Prove2me | Definitions.Def_ConantTerry_Orders_ladder
-- name    : ConantTerry_Orders_ladder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:08.977198+00:00
-- url     : https://prove2.me/theorems/d7fbd12a-a325-43ba-901d-49bf0bd2bb17
-- title:
--   Non-uniform ladders with row thresholds
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, $k$ a length and $\delta$ a real scale. A ladder witness consists of $x_1,\ldots,x_k\in X$, $y_1,\ldots,y_k\in Y$ and $r_1,\ldots,r_k\in[0,1]$ such that
--   $$
--   i\le j\Longrightarrow f(x_i,y_j)\ge r_i+\delta,
--   \qquad
--   i>j\Longrightarrow f(x_i,y_j)\le r_i.
--   $$
--   The diagonal is high. Each threshold belongs to its row and may differ from every other threshold. There is no injectivity requirement. The predicate $\operatorname{AdmitsLadder}(f,k,\delta)$ means existence of these three sequences.
--
--   This is precisely the non-uniform ladder in the goal. Uniform and tight ladders are different source notions and are not imposed here. The source's positive length and scale restrictions are hypotheses of the consuming theorems. **Formalization Note** `Fin k` indexes the sequences by decreasing every source index by one.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p.3, Definition 1.4(1); p.6, §1.6(6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1299.pdf

import Mathlib

namespace ConantTerry.Orders

/-- Definition 1.4(1), p.3. The diagonal is high and thresholds vary by row.
`Fin k` is `[k]` with every index decreased by one. -/
def IsLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (δ : ℝ)
    (x : Fin k → X) (y : Fin k → Y)
    (r : Fin k → Set.Icc (0 : ℝ) 1) : Prop :=
  ∀ i j : Fin k,
    (i ≤ j → (r i : ℝ) + δ ≤ (f (x i, y j) : ℝ)) ∧
    (j < i → (f (x i, y j) : ℝ) ≤ (r i : ℝ))

/-- Existence of a ladder, without injectivity or a common threshold. -/
def AdmitsLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (δ : ℝ) : Prop :=
  ∃ (x : Fin k → X) (y : Fin k → Y)
    (r : Fin k → Set.Icc (0 : ℝ) 1), IsLadder f k δ x y r

end ConantTerry.Orders


