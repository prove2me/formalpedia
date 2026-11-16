-- Prove2me | Definitions.Def_IndependentInfoPricing_Main_Supplement_TwoItem
-- name    : IndependentInfoPricing_Main_Supplement_TwoItem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:47:33.753885+00:00
-- url     : https://prove2.me/theorems/90f6737b-e095-477e-8232-712602ca76d3
-- title:
--   Two-item opposite-sign instance and single-direction slice relaxations
-- statement:
--   For independent nonnegative magnitudes $X,Y$ the type is $v=(X,-Y)$; its law is the product of the law of $X$ and the law of $-Y$ (base `oppositeLaw`). $Z=\min\{X,Y\}$, with law the image of $X\otimes Y$ under $\min$.
--
--   The **types** of Lemma 4.3 are $(x,-y)$ with $x,y\ge0$. A **slice-relaxed mechanism** assigns to every type an allocation $(a,b)\in[0,1]^2$ and a nonnegative price $p$ (measurably), gives type $(x,-y)$ the utility $xa-yb-p$, satisfies both participation constraints
--   $$u(x,y)\ge 0,\qquad u(x,y)\ge x-y$$
--   for every type, and satisfies the IC constraints only between types in the same slice: same $y$ (fixed-$y$ relaxation) or same $x$ (fixed-$x$ relaxation). The **slice value** is the supremum of expected revenue over these mechanisms. Finally
--   $$\operatorname{Rel}_X=\mathbb E[H_X(Y)],\qquad \operatorname{Rel}_Y=\mathbb E[H_Y(X)].$$
--
--   These objects are used by Lemma 4.3, Lemma 4.6 and Theorem 4.1.
--
--   **Formalization Note** Mechanisms are the base `DirectMechanism (Fin 2)`; coordinate 0 is $x$ and coordinate 1 is $-y$. Expected revenues are lintegrals in $[0,\infty]$.
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), §4.2 and Lemma 4.3, printed p.22–25 (PDF p.24–27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Diagonal
import Definitions.Def_IndependentInfoPricing_Main_Supplement_Regularity

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main.Supplement

open IndependentInfoPricing.Main

/-- The two-item opposite-sign instance `v = (X, −Y)` with independent `X, Y`
(base `oppositeLaw`: coordinate 0 has law `X`, coordinate 1 the law of `−Y`). -/
def twoItemLaw (X Y : Measure ℝ) : Measure (Values (Fin 2)) := productLaw (oppositeLaw X Y)

/-- The law of `Z = min{X, Y}` for independent `X` and `Y`. -/
def minLaw (X Y : Measure ℝ) : Measure ℝ :=
  Measure.map (fun q : ℝ × ℝ => min q.1 q.2) (X.prod Y)

/-- Types `(x, −y)` with `x, y ≥ 0`. -/
def quadrant : Set (Values (Fin 2)) := {v | 0 ≤ v 0 ∧ v 1 ≤ 0}

/-- Same slice: equal `y` (when `fixY`) or equal `x` (otherwise). -/
def sameSlice (fixY : Bool) (v w : Values (Fin 2)) : Prop :=
  if fixY then v 1 = w 1 else v 0 = w 0

/-- A direct mechanism on the types `(x, −y)`, `x, y ≥ 0`, with allocations in `[0,1]²`,
nonnegative prices, utility `x a − y b − p`, both participation constraints
`u ≥ 0` and `u ≥ x − y` for every type, and the IC constraints only between types in the same
slice. -/
def SliceRelaxedOn (fixY : Bool) (m : DirectMechanism (Fin 2)) : Prop :=
  BasicOn quadrant m ∧
  (∀ v ∈ quadrant, ∀ w ∈ quadrant, sameSlice fixY v w →
    dot v (m.allocation w) - m.price w ≤ dot v (m.allocation v) - m.price v) ∧
  ∀ v ∈ quadrant, outside v ≤ dot v (m.allocation v) - m.price v

/-- Value of the single-direction slice relaxation (fixed `y` when `fixY`, fixed `x` otherwise). -/
def sliceValue (fixY : Bool) (F : Measure (Values (Fin 2))) : ℝ≥0∞ :=
  ⨆ (m : DirectMechanism (Fin 2)) (_ : SliceRelaxedOn fixY m), revenue F m

/-- `Rel_D(E) = E[H_D(E)]`: `Rel_X = relValue X Y`, `Rel_Y = relValue Y X`. -/
def relValue (D E : Measure ℝ) : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (cappedRevenue D y) ∂E

end IndependentInfoPricing.Main.Supplement


