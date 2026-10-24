-- Prove2me | Definitions.Def_PricingWithTips3DM_05b2c87e27db444f8d2b3614
-- name    : PricingWithTips3DM_05b2c87e27db444f8d2b3614
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:23:12.433047+00:00
-- url     : https://prove2.me/theorems/574419ac-1210-453f-9d8e-fd5a4ddc21d1
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalCapacity
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_29fe1ade4792db459eadc3a6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Capacity inherited by normalized terminal branch arms

The recursive padding predicate already tracks every context reached by a
branch-free statement.  This file exposes its final consequence directly on
`TransitionStmtLinearResult`, eliminating the local route-capacity hypotheses
from later branch-mux assembly.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A normalized branch-free result retains the terminal capacity guaranteed
by the recursive padding predicate. -/
theorem transitionStmtLinearResult_capacity_of_padding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      transitionStmtLinearContextPadding tm seed context q hsupport →
      ∀ (result : TransitionStmtLinearResult tm),
        transitionStmtLinearResult tm context q hsupport = some result →
        ∀ k,
          2 * (transitionStmtStackActionsFor tm k
            result.context.stackActions).length + 1 ≤ seed.height := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hpadding result hresult
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      exact hpadding
  | goto jump =>
      intro hsupport hpadding result hresult
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      exact hpadding
  | load update continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih (context.afterLoad tm update) _ htail result hresult
  | push selected emit continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih _ _ htail result hresult
  | peek selected update continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih (context.afterPeek tm selected update) _ htail result hresult
  | pop selected update continuation ih =>
      intro hsupport hpadding result hresult
      rcases hpadding with ⟨_, htail⟩
      exact ih (context.afterPop tm selected update) _ htail result hresult
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hpadding
      exact False.elim hpadding

/-- Both routed rows in a successful terminal branch plan automatically fit
the widened workspace whenever their recursive arm paddings hold. -/
theorem transitionStmtTerminalBranchPlan_capacities_of_padding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (htruePadding : transitionStmtLinearContextPadding tm seed
      (transitionStmtBranchTrueContext tm context test) whenTrue
      (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport))
    (hfalsePadding : transitionStmtLinearContextPadding tm seed
      (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
      (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
        hsupport)) :
    (∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) ∧
      (∀ k,
        2 * (transitionStmtStackActionsFor tm k
          plan.falseResult.context.stackActions).length + 1 ≤
          workHeight tm seed.height) := by
  have hresults := transitionStmtTerminalBranchPlan_results tm labelOffset
    context test whenTrue whenFalse hsupport plan hplan
  have htrue := transitionStmtLinearResult_capacity_of_padding tm seed
    (transitionStmtBranchTrueContext tm context test) whenTrue
    (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport)
    htruePadding plan.trueResult hresults.1
  have hfalse := transitionStmtLinearResult_capacity_of_padding tm seed
    (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
    (transitionStmtBranchFalseSupport tm test whenTrue whenFalse hsupport)
    hfalsePadding plan.falseResult hresults.2
  constructor
  · intro k
    exact (htrue k).trans (by simp [workHeight])
  · intro k
    exact (hfalse k).trans (by simp [workHeight])

end CLRS.Chapter34.Turing.CookLevin


