-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
-- name    : BKAR_OrderedAssembly_AllBranchesFibers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:02:37.308329+00:00
-- url     : https://prove2.me/theorems/70daefc2-a951-5ded-a157-e9ec180ca4e3
-- title:
--   All Branches Fibers
-- statement:
--   Definitions and structural lemmas for All Branches Fibers, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def supportOrderPairs (V : Type*) [Fintype V]
    [DecidableEq V] : Finset (Σ _ : ForestIndex V, List (Edge V)) :=
  (Finset.univ : Finset (ForestIndex V)).sigma
    (fun I => edgeSetOrders I.edges)
noncomputable def boundarySupportOrderTreeFiber
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  localBoundarySupportOrderContribution choices F pref prefixTs top I order ρ +
    Finset.sum F.activeEdges.attach
      (fun e => ∫ t in 0..top,
        boundarySupportOrderTreeFiber choices
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t I order ρ)
termination_by F.activeEdges.card
decreasing_by
  exact (choices F e).activeEdges_card_lt
def boundarySupportOrderTreeFiberIntegrable
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, F, pref, prefixTs, top, ρ =>
      (∀ e : {e // e ∈ F.activeEdges},
        ∀ x ∈ supportOrderPairs V,
          IntervalIntegrable
            (fun t : ℝ =>
              boundarySupportOrderTreeFiber choices
                (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t x.1 x.2 ρ)
            MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges}, ∀ t ∈ Set.uIcc 0 top,
        boundarySupportOrderTreeFiberIntegrable choices n
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t ρ)
def boundarySupportOrderTreeFiberNontrivialIntegrable
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, F, pref, prefixTs, top, ρ =>
      (∀ e : {e // e ∈ F.activeEdges},
        ∀ x ∈ supportOrderPairs V,
          (pref ++ [e.val]).length < x.2.length →
          x.1.edges ≠ ∅ →
          IntervalIntegrable
            (fun t : ℝ =>
              boundarySupportOrderTreeFiber choices
                (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t x.1 x.2 ρ)
            MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges}, ∀ t ∈ Set.uIcc 0 top,
        boundarySupportOrderTreeFiberNontrivialIntegrable choices n
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t ρ)
noncomputable def rootBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V)) : ℝ :=
  (if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0) +
    boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
      I order ρ
end Forest
end BKAR


