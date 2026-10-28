-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
-- name    : HlawkaSchatten_DiagonalCutoff4_Localization
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-28T10:48:18.268992+00:00
-- url     : https://prove2.me/theorems/ce15eb6d-ac61-45e4-9cd5-974039245e32
-- title:
--   Ordered pair-coordinate charts before excluding collisions
-- statement:
--   For a real $3\times3$ matrix $X$, write $V=\sum_jX_j$ and $V_i=V-X_i$. RawFrame records normalization, the norm bounds and the necessary linear deficit inequality. OrderedChart additionally assigns each pair its own signed coordinate ordering and a lower bound for its dominant coordinate. Different pairs are allowed to have the same dominant coordinate. RawLinearData collects the resulting common linear inequalities. These are localization predicates; normalization is not retained during convex averaging.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Extension of the cutoff-six localization records allowing repeated dominant coordinates.

import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff4

/-- Normalized necessary conditions before choosing dominant coordinates. -/
structure RawFrame (p k A : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop where
  sum : (∑ j, lpNorm p (X j)) = 3
  row_total : ∀ j, lpNorm p (X j) ≤ lpNorm p (total X)
  total_one : 1 ≤ lpNorm p (total X)
  total_cap : lpNorm p (total X) ≤ A
  linear_failure : lpNorm p (total X)-k*(∑ i, lpNorm p (pair X i)) ≤ 3-6*k

def signValue (b : Bool) : ℝ := if b then 1 else -1

def signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool)
    (i h : Fin 3) : ℝ := signValue (signs i h)*pair X i h

/-- Each pair has its own ordered coordinates; dominant coordinates may coincide. -/
structure OrderedChart (p k A d : ℝ) (X : Fin 3 → Fin 3 → ℝ)
    (orders : Fin 3 → Fin 3 → Fin 3) (signs : Fin 3 → Fin 3 → Bool) : Prop where
  raw : RawFrame p k A X
  permutation : ∀ i, Function.Bijective (orders i)
  main : ∀ i, d*lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)
  ordered : ∀ i, 0 ≤ signedPair X signs i (orders i 2) ∧
    signedPair X signs i (orders i 2) ≤ signedPair X signs i (orders i 1) ∧
    signedPair X signs i (orders i 1) ≤ signedPair X signs i (orders i 0)

structure RawLinearData (k A : ℝ) (X : Fin 3 → Fin 3 → ℝ)
    (N P : Fin 3 → ℝ) (T : ℝ) : Prop where
  sum : N 0+N 1+N 2 = 3
  Nnonneg : ∀ j, 0 ≤ N j
  Ntotal : ∀ j, N j ≤ T
  Tone : 1 ≤ T
  Tcap : T ≤ A
  coord : ∀ j i, -N j ≤ X j i ∧ X j i ≤ N j
  column : ∀ i, -T ≤ X 0 i+X 1 i+X 2 i ∧ X 0 i+X 1 i+X 2 i ≤ T
  Pnonneg : ∀ i, 0 ≤ P i
  Ptriangle : ∀ i, P i ≤ 3-N i
  Ptotal : ∀ i, P i ≤ T+N i
  Tpair : ∀ i, T ≤ P i+N i
  reverse : ∀ i j l, i ≠ j → i ≠ l → j ≠ l → N j-N l ≤ P i
  failure : T-k*(P 0+P 1+P 2) ≤ 3-6*k

end HlawkaSchatten.DiagonalCutoff4


