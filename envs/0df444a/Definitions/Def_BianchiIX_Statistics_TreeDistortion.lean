-- Prove2me | Definitions.Def_BianchiIX_Statistics_TreeDistortion
-- name    : BianchiIX_Statistics_TreeDistortion
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T17:35:59.486446+00:00
-- url     : https://prove2.me/theorems/716fe9ec-268a-4779-810a-7696e59f20ca
-- title:
--   Local analytic estimates on an inverse-branch tree
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
--
--   Let $S=\bigcap_nS_n$ be the surviving set. For $x\in S$, denote its unique
--   length-$n$ cell word by $v_n(x)$ and define $a_n(x)$ by
--   $v_{n+1}(x)=v_n(x)a_n(x)$. Let $g_b(t)=1/(b+t)$ and
--   $G_v=g_{v_0}\circ\cdots\circ g_{v_{|v|-1}}$, with the empty composition the
--   identity. The code is
--   $$\kappa(x)=\lim_{n\to\infty}G_{v_n(x)}(0).$$
--   For a Borel measure $\mu$ on $\mathbb R$, write $\mu_S$ for its pullback
--   to the measurable subtype $S$ by the inclusion into $\mathbb R$.
--
--   Assume $R,U_{v,a}\subset(0,1)$ and that every branch is differentiable
--   with nonzero derivative on its domain. Let real sequences $d,e$ satisfy,
--   for every $t\in U_{v,a}$,
--   $$|h_{v,a}(t)-g_a(t)|\leq d_{|v|},\qquad
--   \left|\log\frac{|h_{v,a}'(t)|}{|g_a'(t)|}\right|\leq e_{|v|}.$$
--   Put $B_n=\sum_{j=0}^{n-1}e_j+2\sum_{j=1}^{n-1}d_j$, with empty sums zero,
--   and write $\lambda$ for Lebesgue measure.
--
--   The branch-estimate structure consists of the root and domain inclusions,
--   branch differentiability, nonvanishing derivatives, and the two local
--   error bounds displayed above.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeDistortion.lean

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_BranchTree
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

/-! Local inverse-branch errors imply distortion and measure bounds for the whole tree. -/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX







namespace InverseBranchTree

/-- These are local analytic inputs on the branch domains, not conclusions about prefixes. -/
structure BranchEstimates (T : InverseBranchTree) (d e : ℕ → ℝ) : Prop where
  root_subset : T.root ⊆ Ioo (0 : ℝ) 1
  domain_subset : ∀ w a, T.domain w a ⊆ Ioo (0 : ℝ) 1
  differentiable : ∀ w a, ∀ x ∈ T.domain w a, DifferentiableAt ℝ (T.branch w a) x
  nonzero : ∀ w a, ∀ x ∈ T.domain w a, deriv (T.branch w a) x ≠ 0
  value_error : ∀ w a, ∀ x ∈ T.domain w a,
    |T.branch w a x - gaussInv a x| ≤ d w.length
  log_error : ∀ w a, ∀ x ∈ T.domain w a,
    |Real.log (|deriv (T.branch w a) x| / |deriv (gaussInv a) x|)| ≤ e w.length

namespace BranchEstimates

























end BranchEstimates
end InverseBranchTree
end BianchiIX


