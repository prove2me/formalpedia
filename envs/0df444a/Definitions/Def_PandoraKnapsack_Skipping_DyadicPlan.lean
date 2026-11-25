-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_DyadicPlan
-- name    : PandoraKnapsack_Skipping_DyadicPlan
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:30:17.890994+00:00
-- url     : https://prove2.me/theorems/61db6c55-1fe2-43d2-af5e-01b3c2cc16d8
-- title:
--   Dyadic feasible plan computed by normalized packing
-- statement:
--   Use start times zero and the powers of two at most $T$. The packing matrix has one unit row per item and a prefix row at each positive checkpoint $t$, with coefficient $\mu_{ij,t}/(2t)$ for starts through $t$. Normalize positive profits by the best time-zero profit, run the bounded packing solver, and omit negative-profit columns from its output. The result is a sparse array in the original time-indexed LP.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#A2.SS1, Appendix B.1 and Theorem 5.1, original dyadic-support variant with coefficients evaluated at the retained start.

import Definitions.Def_PandoraKnapsack_NormalizedPacking
import Definitions.Def_PandoraKnapsack_Skipping_CompactLP

namespace PandoraKnapsack.Skipping

open PandoraPacking

/-- A zero label followed by the powers of two at most the capacity. -/
def labelCount (T : ℕ) := if T = 0 then 1 else Nat.log 2 T + 2

def timeLabel {T : ℕ} (k : Fin (labelCount T)) : ℕ :=
  if k.val = 0 then 0 else 2 ^ (k.val - 1)

def columnCount (n m T : ℕ) := n * (m * labelCount T)

def columns (n m T : ℕ) : (Fin n × Fin m × Fin (labelCount T)) ≃ Fin (columnCount n m T) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def timeRows (n T : ℕ) := n + labelCount T

def clockRow {n T : ℕ} (v : Fin n ⊕ Fin (labelCount T)) : Fin (timeRows n T) := finSumFinEquiv v

noncomputable def packingRows {n m T : ℕ} (I : Instance n m T) :
    Matrix (timeRows n T) (columnCount n m T) := fun row col =>
  let z := (columns n m T).symm col
  match finSumFinEquiv.symm row with
  | Sum.inl i => if i = z.1 then 1 else 0
  | Sum.inr k =>
    let r := timeLabel k
    if r = 0 then 0 else if timeLabel z.2.2 ≤ r then mu I z.1 z.2.1 r / (2*r) else 0

/-- Normalize by the largest initial profit, starting the maximum scan at zero. -/
noncomputable def maxWeight {n m T : ℕ} (I : Instance n m T) : ℝ :=
  (insert 0 (Finset.univ.image fun p : Fin n × Fin m => effWeight I p.1 p.2 0)).max'
    (Finset.insert_nonempty _ _)

noncomputable def columnWeight {n m T : ℕ} (I : Instance n m T) (col : Fin (columnCount n m T)) : ℝ :=
  let z := (columns n m T).symm col
  effWeight I z.1 z.2.1 (timeLabel z.2.2)

noncomputable def packingProfits {n m T : ℕ} (I : Instance n m T) : Vec (columnCount n m T) :=
  fun col => if maxWeight I = 0 then 0 else max 0 (columnWeight I col) / maxWeight I

noncomputable def planVector {n m T : ℕ} (I : Instance n m T) : Vec (columnCount n m T) :=
  let v := solve (packingRows I) (packingProfits I)
  fun col => if 0 ≤ columnWeight I col then v col else 0

noncomputable def spreadVector {n m T : ℕ} (x : Vec (columnCount n m T)) : LPArray n m :=
  fun i j t => ∑ k : Fin (labelCount T), if timeLabel k = t then x (columns n m T (i,j,k)) else 0

noncomputable def dyadicPlan {n m T : ℕ} (I : Instance n m T) : LPArray n m :=
  spreadVector (planVector I)

end PandoraKnapsack.Skipping


