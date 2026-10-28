-- Prove2me | Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
-- name    : HlawkaSchatten_DiagonalCutoff6_Localization
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-27T18:51:42.585467+00:00
-- url     : https://prove2.me/theorems/45335feb-e11d-4dc9-a80a-200f42ce38e7
-- title:
--   Normalized signed-coordinate data for the diagonal Hlawka problem
-- statement:
--   For a real $3\times3$ matrix $X$, write $V=\sum_jX_j$ and $V_i=V-X_i$. The records collect normalization, norm bounds, distinct dominant pair coordinates and the necessary linear inequality for a strict Hlawka counterexample. These predicates describe the localization stage; equality normalization is not retained as a convex-domain hypothesis during averaging.
-- source:
--   Sharp diagonal Hlawka campaign, cutoff-6 signed localization: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . The definitions encode the constraints used in the signed-tail proof, https://prove2.me/theorems/bcc29d84-0329-4119-8e6b-e33624b0ec4a .

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Algebra.BigOperators.Fin
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6
structure RelativeOrientedData (p q k d : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop where
  sum : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2) = 3
  norm_le_total : ∀ i, lpNorm p (X i) ≤ lpNorm p (X 0+X 1+X 2)
  total_one : 1 ≤ lpNorm p (X 0+X 1+X 2)
  total_cap : lpNorm p (X 0+X 1+X 2) < 3*q
  main0 : d*lpNorm p (X 1+X 2) ≤ X 1 0+X 2 0
  main1 : d*lpNorm p (X 0+X 2) ≤ X 0 1+X 2 1
  main2 : d*lpNorm p (X 0+X 1) ≤ X 0 2+X 1 2
  max0 : ∀ h, |(X 1+X 2) h| ≤ X 1 0+X 2 0
  max1 : ∀ h, |(X 0+X 2) h| ≤ X 0 1+X 2 1
  max2 : ∀ h, |(X 0+X 1) h| ≤ X 0 2+X 1 2
  linear_failure : lpNorm p (X 0+X 1+X 2) - k*
    (lpNorm p (X 1+X 2)+lpNorm p (X 0+X 2)+lpNorm p (X 0+X 1)) ≤ 3-6*k
  failure : tripleDeficit p (cyclicConstant p) X < 0


def total (X : Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ := ∑ j, X j

def pair (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : Fin 3 → ℝ := total X-X i

def relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun j i => X (e j) (e i)


structure Frame (p k A d : ℝ) (X : Fin 3 → Fin 3 → ℝ) : Prop where
  sum : (∑ j, lpNorm p (X j)) = 3
  row_total : ∀ j, lpNorm p (X j) ≤ lpNorm p (total X)
  total_one : 1 ≤ lpNorm p (total X)
  total_cap : lpNorm p (total X) ≤ A
  main : ∀ i, d*lpNorm p (pair X i) ≤ pair X i i
  maximal : ∀ i h, |pair X i h| ≤ pair X i i
  linear_failure : lpNorm p (total X)-k*(∑ i, lpNorm p (pair X i)) ≤ 3-6*k


structure LinearData (k A d : ℝ) (X : Fin 3 → Fin 3 → ℝ) (N P : Fin 3 → ℝ) (T : ℝ) : Prop where
  sum : N 0+N 1+N 2 = 3
  Nnonneg : ∀ j, 0 ≤ N j
  Ntotal : ∀ j, N j ≤ T
  Tone : 1 ≤ T
  Tcap : T ≤ A
  coord : ∀ j i, -N j ≤ X j i ∧ X j i ≤ N j
  column : ∀ i, -T ≤ X 0 i+X 1 i+X 2 i ∧ X 0 i+X 1 i+X 2 i ≤ T
  Pnonneg : ∀ i, 0 ≤ P i
  Ptriangle : ∀ i, P i ≤ 3-N i
  main : ∀ i, d*P i ≤ pair X i i
  maximal : ∀ i h, |pair X i h| ≤ pair X i i
  Ptotal : ∀ i, P i ≤ T+N i
  Tpair : ∀ i, T ≤ P i+N i
  reverse : ∀ i j l, i ≠ j → i ≠ l → j ≠ l → N j-N l ≤ P i
  failure : T-k*(P 0+P 1+P 2) ≤ 3-6*k


end HlawkaSchatten.DiagonalCutoff6


