-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_ProductAnnulusLocalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:16:07.16302+00:00
-- url     : https://prove2.me/theorems/d61b8e8d-d58b-4c54-9cfc-4a0a21755bf4
-- title:
--   Product Annulus Localization
-- statement:
--   Definitions and structural lemmas for Product Annulus Localization, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ProductAnnulusLocalization.lean

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_BlockLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Tactic.NormNum.Parity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
def coeffBlockFinset_wip {d : Nat} (ℓ : Idx d) : Finset (Idx d) :=
  Fintype.piFinset fun q : Fin d => HermiteLEAN.squareBlock (ℓ q)
def nearBlocks_wip {d : Nat} (j : Idx d) (M : Nat) : Finset (Idx d) :=
  (Fintype.piFinset fun q : Fin d => Finset.range (j q + M + 1)).filter fun ℓ =>
    Hermite1DimdLEAN.blockDistance j ℓ ≤ M
def nearLowBlocks_wip {d : Nat} (J M : Nat) : Finset (Idx d) :=
  (lowAnnuli d J).biUnion fun j => nearBlocks_wip j M
def nearLowCoeffSet_wip {d : Nat} (J M : Nat) : Finset (Idx d) :=
  (nearLowBlocks_wip (d := d) J M).biUnion fun ℓ => coeffBlockFinset_wip ℓ
end DimdPolyLEAN


