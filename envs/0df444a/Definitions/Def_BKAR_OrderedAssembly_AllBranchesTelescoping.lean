-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
-- name    : BKAR_OrderedAssembly_AllBranchesTelescoping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:00:00.533146+00:00
-- url     : https://prove2.me/theorems/194dfde5-ef99-4e32-bcb7-ffeee0592efe
-- title:
--   All Branches Telescoping
-- statement:
--   Definitions and structural lemmas for All Branches Telescoping, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_ActiveExtension_activeEdges_card_lt
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def localRecursiveBoundaryRemainder
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum F.activeEdges.attach
    (fun e => ∫ t in 0..top,
      Finset.sum (choices F e).forest.activeEdges.attach
        (fun e' => ∫ s in 0..t,
          allBranchesBoundaryExpansion choices
            (choices (choices F e).forest e').forest.activeEdges.card
            (choices (choices F e).forest e').forest
            ((pref ++ [e.val]) ++ [e'.val])
            ((prefixTs ++ [t]) ++ [s]) s ρ))
noncomputable def localBoundarySupportOrderSum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (ForestIndex V))
    (fun I => Finset.sum (edgeSetOrders I.edges)
      (fun order =>
        localBoundarySupportOrderContribution choices F pref prefixTs top
          I order ρ))
noncomputable def boundarySupportOrderTreeContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  localBoundarySupportOrderSum choices F pref prefixTs top ρ +
    Finset.sum F.activeEdges.attach
      (fun e => ∫ t in 0..top,
        boundarySupportOrderTreeContribution choices
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)
termination_by F.activeEdges.card
decreasing_by
  exact (choices F e).activeEdges_card_lt
end Forest
end BKAR


