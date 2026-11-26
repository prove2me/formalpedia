-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
-- name    : BKAR_OrderedAssembly_AllBranchesRegrouping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:58:34.729983+00:00
-- url     : https://prove2.me/theorems/20d46a42-687e-40da-914e-5e44e12d924f
-- title:
--   All Branches Regrouping
-- statement:
--   Definitions and structural lemmas for All Branches Regrouping, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def localBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      (F.activeEdges.attach.filter
        (fun e => (choices F e).forest.support = I))
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ ts)))))
noncomputable def localBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      (F.activeEdges.attach.filter
        (fun e =>
          (choices F e).forest.support = I ∧
            pref ++ [e.val] = order))
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order (prefixTs ++ ts)))))
noncomputable def firstBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e => (choices (Forest.empty V) e).forest.support = I))
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ)
noncomputable def firstBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e =>
          (choices (Forest.empty V) e).forest.support = I ∧
            [e.val] = order))
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution order ρ)
noncomputable def firstRecursiveBoundaryRemainder
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Forest.empty V).activeEdges.attach
    (fun e => ∫ t in 0..(1 : ℝ),
      Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
        (fun e' => ∫ s in 0..t,
          allBranchesBoundaryExpansion choices
            (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
            (choices ((choices (Forest.empty V) e).forest) e').forest
            ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
end Forest
end BKAR


