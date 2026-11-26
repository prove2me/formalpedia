-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranches
-- name    : BKAR_OrderedAssembly_AllBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:56:25.910231+00:00
-- url     : https://prove2.me/theorems/303e50cf-e3de-51d6-9e4b-5ce456b29905
-- title:
--   All Branches
-- statement:
--   Definitions and structural lemmas for All Branches, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev ActiveExtensionChoice (V : Type*) [Fintype V] [DecidableEq V] :=
  ∀ F : Forest V, ∀ e : {e // e ∈ F.activeEdges}, ActiveExtension F e.val
noncomputable def allBranchesExpansion
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → ℝ
  | 0, F, pref, prefixTs, top, ρ =>
      mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top)
  | n + 1, F, pref, prefixTs, top, ρ =>
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesExpansion choices n (choices F e).forest
              (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)
noncomputable def allBranchesBoundaryExpansion
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → ℝ
  | 0, F, pref, prefixTs, _, ρ =>
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs))
  | n + 1, F, pref, prefixTs, top, ρ =>
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices n (choices F e).forest
              (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)
def allBranchesAnalytic
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, F, pref, prefixTs, top, ρ =>
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) ∧
      (∀ t ∈ Set.uIcc 0 top,
        DifferentiableAt ℝ (mixedPartialList pref.reverse ρ)
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) ∧
      (∀ e ∈ F.activeEdges,
        IntervalIntegrable
          (fun t : ℝ => mixedPartialList (e :: pref.reverse) ρ
            (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
          MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges},
        IntervalIntegrable
          (fun t : ℝ => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
          MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            Finset.sum (choices F e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices (choices F e).forest e').forest.activeEdges.card
                  (choices (choices F e).forest e').forest
                  ((pref ++ [e.val]) ++ [e'.val])
                  ((prefixTs ++ [t]) ++ [s]) s ρ))
          MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges}, ∀ t ∈ Set.uIcc 0 top,
        allBranchesAnalytic choices n (choices F e).forest
          (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)
end Forest
end BKAR


