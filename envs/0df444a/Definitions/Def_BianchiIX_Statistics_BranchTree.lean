-- Prove2me | Definitions.Def_BianchiIX_Statistics_BranchTree
-- name    : BianchiIX_Statistics_BranchTree
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T16:57:51.481721+00:00
-- url     : https://prove2.me/theorems/80f43578-af97-4e8c-853f-d58c6e7874bd
-- title:
--   Stopped inverse-branch trees and their actual domains
-- statement:
--   Let $T$ be an inverse-branch tree with open root
--   $R\subset\mathbb R$. For every finite positive-digit word $v$ and digit $a$,
--   let $U_{v,a}\subset\mathbb R$ be open and let $h_{v,a}:\mathbb R\to\mathbb R$
--   be continuous and injective on $U_{v,a}$. For fixed $v$, assume the images
--   $h_{v,a}(U_{v,a})$ are pairwise disjoint. Define
--   $$K_\varnothing=R,\qquad K_{va}=U_{v,a}\cap h_{v,a}^{-1}(K_v),$$
--   $$H_\varnothing=\mathrm{id},\qquad H_{va}=H_v\circ h_{v,a},\qquad C_v=H_v(K_v),$$
--   $$D_v=K_v\setminus\bigcup_a h_{v,a}(U_{v,a}),\qquad S_n=\bigcup_{|v|=n}C_v.$$
--   Here $va$ denotes appending the digit $a$ to $v$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/BranchTree.lean

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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Actual domains of a stopped inverse-branch tree. Only local branch data are assumed. -/

open Set MeasureTheory

namespace BianchiIX

structure InverseBranchTree where
  root : Set ℝ
  branch : List ℕ+ → ℕ+ → ℝ → ℝ
  domain : List ℕ+ → ℕ+ → Set ℝ
  root_open : IsOpen root
  domain_open : ∀ w a, IsOpen (domain w a)
  branch_continuous : ∀ w a, ContinuousOn (branch w a) (domain w a)
  branch_injective : ∀ w a, InjOn (branch w a) (domain w a)
  branch_disjoint : ∀ w, Pairwise (fun a b =>
    Disjoint (branch w a '' domain w a) (branch w b '' domain w b))

namespace InverseBranchTree

variable (T : InverseBranchTree)

def terminal (w : List ℕ+) : Set ℝ :=
  w.reverseRecOn T.root (fun v a K => T.domain v a ∩ T.branch v a ⁻¹' K)

def toRoot (w : List ℕ+) : ℝ → ℝ :=
  w.reverseRecOn id (fun v a H => H ∘ T.branch v a)

def cell (w : List ℕ+) : Set ℝ := T.toRoot w '' T.terminal w

def stoppedDomain (w : List ℕ+) : Set ℝ :=
  T.terminal w \ ⋃ a, T.branch w a '' T.domain w a

def level (n : ℕ) : Set ℝ := ⋃ w : {w : List ℕ+ // w.length = n}, T.cell w.val















































end InverseBranchTree

end BianchiIX


