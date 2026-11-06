-- Prove2me | Definitions.Def_BianchiIX_Statistics_GaussCylinders
-- name    : BianchiIX_Statistics_GaussCylinders
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T15:55:18.81836+00:00
-- url     : https://prove2.me/theorems/289d5075-5a96-4e67-911c-a7b0f7ab1989
-- title:
--   Gauss cylinders and minimal contained cylinders
-- statement:
--   Let $A=\{1,2,3,\ldots\}$, and let $a=(a_0,a_1,\ldots)\in A^{\mathbb N}$.
--   For $b\in A$, write $g_b(x)=1/(b+x)$. For a finite word $w=(b_0,\ldots,b_{n-1})$,
--   set $G_w=g_{b_0}\circ\cdots\circ g_{b_{n-1}}$, with $G_{\varnothing}$ the identity.
--   Define
--   $$q_n(a)=G_{(a_0,\ldots,a_{n-1})}(0),\qquad
--   \pi(a)=\lim_{n\to\infty}q_n(a),\qquad (\sigma^m a)_j=a_{m+j}.$$
--   The limit exists by the uniform contraction of inverse words. Write
--   $T(x)=1/x-\lfloor1/x\rfloor$ for $x\ne0$ and $T(0)=0$.
--
--   For a finite word $w$ of nonnegative integers, let
--   $$C(w)=G_w((0,1)).$$
--   For these maps on all of $\mathbb R$, the reciprocal uses $0^{-1}=0$.
--   Write $a|_n=(a_0,\ldots,a_{n-1})$. For a set $O\subset\mathbb R$, let
--   $\mathcal F(O)$ consist of the nonempty positive-digit words $w$ such that
--   $C(w)\subset O$ and no proper nonempty prefix $v$ has $C(v)\subset O$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussCylinders.lean

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

/-! Gauss cylinders and the passage from cylinder bounds to measure domination. -/

namespace BianchiIX

noncomputable section

open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

def gaussCylinder (w : List ℕ) : Set ℝ := gaussWord w '' Ioo 0 1





















def firstGaussCylinders (O : Set ℝ) : Set (List ℕ) :=
  {w | (∀ k ∈ w, 1 ≤ k) ∧ gaussCylinder w ⊆ O ∧ w ≠ [] ∧
    ∀ v, v ≠ [] → v <+: w → v.length < w.length → ¬ gaussCylinder v ⊆ O}













end

end BianchiIX


