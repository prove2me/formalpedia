-- Prove2me | Definitions.Def_NashBargainingProblem_Axiomatic_BillJack
-- name    : NashBargainingProblem_Axiomatic_BillJack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:23.245472+00:00
-- url     : https://prove2.me/theorems/62d510a4-9326-4a67-859e-144c16ffa34d
-- title:
--   Nash's Bill–Jack barter: goods, utilities, exchange gains and the set of alternatives
-- statement:
--   Nash's example on pp. 160–161. Bill owns a book, a whip, a ball, a bat and a box; Jack owns a pen, a toy, a knife and a hat. The utilities of the goods are
--
--   | good | utility to Bill | utility to Jack |
--   |---|---|---|
--   | book (Bill's) | 2 | 4 |
--   | whip (Bill's) | 2 | 2 |
--   | ball (Bill's) | 2 | 1 |
--   | bat (Bill's) | 2 | 2 |
--   | box (Bill's) | 4 | 1 |
--   | pen (Jack's) | 10 | 1 |
--   | toy (Jack's) | 4 | 1 |
--   | knife (Jack's) | 6 | 2 |
--   | hat (Jack's) | 2 | 2 |
--
--   and, by the paper's simplifying assumption (p. 160), the utility of a collection of goods is the sum of the utilities of its members. An **exchange** is a pair $(X,Y)$ with $X$ a set of Bill's goods given to Jack and $Y$ a set of Jack's goods given to Bill. Its **gain** is
--
--   $$
--   \mathrm{gain}(X,Y)=\Bigl(\sum_{y\in Y}u_{\mathrm{Bill}}(y)-\sum_{x\in X}u_{\mathrm{Bill}}(x),\ \ \sum_{x\in X}u_{\mathrm{Jack}}(x)-\sum_{y\in Y}u_{\mathrm{Jack}}(y)\Bigr),
--   $$
--
--   the utility gains of Bill and Jack relative to no trade, which has gain $(0,0)$. The **set of alternatives** $S_{BJ}$ is the convex hull of the gains of all $2^9$ exchanges, since any probability combination of available anticipations is available (p. 158). This is the convex polygon of Figure 2.
-- source:
--   Nash, The Bargaining Problem, Econometrica 18 (1950), pp. 160–161, Examples (additivity assumption p. 160, table of goods p. 161, Figure 2)

import Mathlib

namespace NashBargainingProblem.Axiomatic

/-- Bill's goods in Nash's example (p. 161). -/
inductive BillGood
  | book | whip | ball | bat | box
  deriving DecidableEq

instance : Fintype BillGood :=
  ⟨{.book, .whip, .ball, .bat, .box}, by intro x; cases x <;> decide⟩

/-- Jack's goods in Nash's example (p. 161). -/
inductive JackGood
  | pen | toy | knife | hat
  deriving DecidableEq

instance : Fintype JackGood :=
  ⟨{.pen, .toy, .knife, .hat}, by intro x; cases x <;> decide⟩

/-- Utility to Bill of each of Bill's goods (table, p. 161). -/
def billGoodUtilBill : BillGood → ℝ
  | .book => 2 | .whip => 2 | .ball => 2 | .bat => 2 | .box => 4

/-- Utility to Jack of each of Bill's goods (table, p. 161). -/
def billGoodUtilJack : BillGood → ℝ
  | .book => 4 | .whip => 2 | .ball => 1 | .bat => 2 | .box => 1

/-- Utility to Bill of each of Jack's goods (table, p. 161). -/
def jackGoodUtilBill : JackGood → ℝ
  | .pen => 10 | .toy => 4 | .knife => 6 | .hat => 2

/-- Utility to Jack of each of Jack's goods (table, p. 161). -/
def jackGoodUtilJack : JackGood → ℝ
  | .pen => 1 | .toy => 1 | .knife => 2 | .hat => 2

/-- The utility gains `(Bill's gain, Jack's gain)` of the exchange in which Bill gives Jack the
goods `X` and Jack gives Bill the goods `Y`, using additivity of utility over goods (p. 160). -/
def billJackGain (e : Finset BillGood × Finset JackGood) : ℝ × ℝ :=
  ((∑ y ∈ e.2, jackGoodUtilBill y) - (∑ x ∈ e.1, billGoodUtilBill x),
   (∑ x ∈ e.1, billGoodUtilJack x) - (∑ y ∈ e.2, jackGoodUtilJack y))

/-- The set of alternatives of the Bill–Jack barter: all probability combinations of exchanges,
i.e. the convex hull of the gains of the `2^9` pure exchanges. -/
def billJackSet : Set (ℝ × ℝ) := convexHull ℝ (Set.range billJackGain)

end NashBargainingProblem.Axiomatic


