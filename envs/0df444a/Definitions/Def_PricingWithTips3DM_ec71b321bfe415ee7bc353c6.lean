-- Prove2me | Definitions.Def_PricingWithTips3DM_ec71b321bfe415ee7bc353c6
-- name    : PricingWithTips3DM_ec71b321bfe415ee7bc353c6
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:27:30.639265+00:00
-- url     : https://prove2.me/theorems/c7ab46ed-2759-431f-96ce-e10d33093dbb
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearResultBounds
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_41dc4e06cda4d957031903ff
import Definitions.Def_PricingWithTips3DM_38bfba7347d7bb4c93d962b4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Automatic route bounds for recursive linear statement leaves

The compact affine-span source requires its left deletions to remain in the
public tableau row and its right deletions to remain in the fixed push
overflow.  Recursive padding already supplies the first fact.  This module
tracks pushes through the same linear normalizer and derives the second fact
from a single root-to-leaf push budget.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Appending one heterogeneous stack action adds exactly its selected-stack
push contribution. -/
theorem transitionStmtStackActionPushCountFor_append_singleton
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (actions : List (TransitionStmtStackAction tm))
    (action : TransitionStmtStackAction tm) :
    transitionStmtStackActionPushCountFor tm target (actions ++ [action]) =
      transitionStmtStackActionPushCountFor tm target actions +
        action.pushCountFor tm target := by
  induction actions with
  | nil => simp [transitionStmtStackActionPushCountFor]
  | cons head tail ih =>
      simp only [List.cons_append, transitionStmtStackActionPushCountFor]
      rw [ih]
      omega

/-- A successful linear normalization spends no more pushes than the pushes
already recorded in its context plus the syntactic budget of its suffix. -/
theorem transitionStmtLinearResult_pushCount_le_of_budget
    (tm : _root_.Turing.FinTM2) (budget : Nat) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
      (result : TransitionStmtLinearResult tm),
      transitionStmtLinearResult tm context q hsupport = some result →
      (∀ k,
        transitionStmtStackActionPushCountFor tm k context.stackActions +
          stmtMaxPushes tm k q ≤ budget) →
      ∀ k,
        transitionStmtStackActionPushCountFor tm k
          result.context.stackActions ≤ budget := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport result hresult hbudget k
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      simpa [stmtMaxPushes] using hbudget k
  | goto jump =>
      intro hsupport result hresult hbudget k
      simp only [transitionStmtLinearResult, Option.some.injEq] at hresult
      subst result
      simpa [stmtMaxPushes] using hbudget k
  | load update continuation ih =>
      intro hsupport result hresult hbudget
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      apply ih (context.afterLoad tm update) hcontinuation result hresult
      intro k
      simpa [TransitionStmtAffineContext.afterLoad,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.replaceStateByMap,
        stmtMaxPushes] using hbudget k
  | push selected emit continuation ih =>
      intro hsupport result hresult hbudget
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm selected :=
        fun code =>
          ⟨emit ((stateEquivFin tm).symm code), by
            apply hsupport selected
            simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      simp only [transitionStmtLinearResult] at hresult
      change transitionStmtLinearResult tm
          (context.afterPush tm selected table) continuation hcontinuation =
        some result at hresult
      apply ih (context.afterPush tm selected table) hcontinuation result
        hresult
      intro target
      have htarget := hbudget target
      simp only [stmtMaxPushes] at htarget
      simp only [TransitionStmtAffineContext.afterPush,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.recordPush,
        transitionStmtStackActionPushCountFor_append_singleton,
        TransitionStmtStackAction.pushCountFor]
      omega
  | peek selected update continuation ih =>
      intro hsupport result hresult hbudget
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      apply ih (context.afterPeek tm selected update) hcontinuation result
        hresult
      intro k
      simpa [TransitionStmtAffineContext.afterPeek,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.replaceStateByPairMap,
        stmtMaxPushes] using hbudget k
  | pop selected update continuation ih =>
      intro hsupport result hresult hbudget
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearResult] at hresult
      apply ih (context.afterPop tm selected update) hcontinuation result
        hresult
      intro target
      have htarget := hbudget target
      simpa [TransitionStmtAffineContext.afterPop,
        TransitionStmtAffineContext.advance,
        TransitionStmtAffineContext.replaceStateByPairMap,
        TransitionStmtAffineContext.recordPop,
        transitionStmtStackActionPushCountFor_append_singleton,
        TransitionStmtStackAction.pushCountFor,
        stmtMaxPushes] using htarget
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport result hresult hbudget
      simp [transitionStmtLinearResult] at hresult

/-- Public-row capacity plus the machine push bound discharge every endpoint
condition of the compact affine-span source. -/
theorem TransitionStmtLinearResult.routeBounds_of_capacity_pushCount
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm)
    (hcapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        result.context.stackActions).length + 1 ≤ seed.height)
    (hpush : ∀ k,
      transitionStmtStackActionPushCountFor tm k
        result.context.stackActions ≤ maxPushesPerStep tm) :
    result.RouteBounds tm seed labelOffset := by
  intro k
  have hleft := transitionStmtSelectedStackAffineActionSpans_sourceDrop_le
    tm k labelOffset
      (transitionStmtStackActionsFor tm k result.context.stackActions)
  have hright := transitionStmtSelectedStackAffineActionSpans_sourceRdrop_le
    tm k labelOffset
      (transitionStmtStackActionsFor tm k result.context.stackActions)
  have hselectedPush := transitionStmtStackActionsFor_pushCount_eq tm k
    result.context.stackActions
  have hcapacityK := hcapacity k
  have hpushK := hpush k
  dsimp [TransitionStmtAffineContext.stackRoute]
  rw [hselectedPush] at hright
  omega

/-- Recursive padding and one suffix-aware push budget automatically supply
the exact bounds needed by a successful linear leaf. -/
theorem transitionStmtRecursiveContextPadding_linearResult_routeBounds
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hpadding : transitionStmtRecursiveContextPadding tm seed context q
      hsupport)
    (hpushBudget : ∀ k,
      transitionStmtStackActionPushCountFor tm k context.stackActions +
        stmtMaxPushes tm k q ≤ maxPushesPerStep tm)
    (result : TransitionStmtLinearResult tm)
    (hresult : transitionStmtLinearResult tm context q hsupport =
      some result) :
    result.RouteBounds tm seed labelOffset := by
  have hresultIff := transitionStmtLinearResult_isSome_iff_terminal tm
    context q hsupport
  rw [hresult] at hresultIff
  have hterminal : (transitionStmtTerminalLayout tm q).isSome := by
    simpa using hresultIff
  have hlinear := transitionStmtRecursiveContextPadding_to_linear tm seed
    context q hsupport hterminal hpadding
  have hcapacity := transitionStmtLinearResult_capacity_of_padding tm seed
    context q hsupport hlinear result hresult
  have hpush := transitionStmtLinearResult_pushCount_le_of_budget tm
    (maxPushesPerStep tm) context q hsupport result hresult hpushBudget
  exact result.routeBounds_of_capacity_pushCount tm seed labelOffset
    hcapacity hpush

end CLRS.Chapter34.Turing.CookLevin


