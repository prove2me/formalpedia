-- Prove2me | Definitions.Def_BianchiIX_Statistics_TreeOrbits
-- name    : BianchiIX_Statistics_TreeOrbits
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T17:37:14.589077+00:00
-- url     : https://prove2.me/theorems/520cae38-2867-4ed2-a479-56456f7ee8d0
-- title:
--   Intermediate phases of surviving points
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
--   For $x\in S$, let $\phi_n(x)$ be the unique point of $K_{v_n(x)}$
--   with $H_{v_n(x)}(\phi_n(x))=x$.
--
--   The phase is chosen using cell membership. The existence proof is included
--   with the definition, and injectivity of the root map makes the chosen point unique.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/TreeOrbits.lean

import Definitions.Def_BianchiIX_Statistics_BranchTree
import Definitions.Def_BianchiIX_Statistics_TreeCoding
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

/-! Actual intermediate phases of surviving initial points and their Gauss comparison. -/

open Set MeasureTheory Filter
open scoped Topology

namespace BianchiIX
namespace InverseBranchTree

variable (T : InverseBranchTree)

private theorem exists_phase (x : T.survivors) (n : ℕ) :
    ∃ t ∈ T.terminal (T.word x n), T.toRoot (T.word x n) t = x.val :=
  T.mem_word_cell x n

noncomputable def phase (x : T.survivors) (n : ℕ) : ℝ := (T.exists_phase x n).choose











namespace BranchEstimates













end BranchEstimates
end InverseBranchTree
end BianchiIX


