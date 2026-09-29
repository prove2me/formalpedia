-- Prove2me | Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data
-- name    : mme_dwz_step1_mixed_selected_full_map_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-28T10:18:24.071972+00:00
-- url     : https://prove2.me/theorems/8257ff27-6865-4c2f-ad2b-e634d616a0aa
-- title:
--   DWZ selected mixed-owner full-source maps
-- statement:
--   This module packages the canonical bases for arbitrary coarse blocks and per-mode coarse addresses, the selected mixed X/Y/Z word, and the corresponding address-block and full-source linear-map families used in Additional Zeroing-Out Step 1. It also records the ordinary owner-basis normal form of those maps. The definitions provide a common public boundary for coordinatewise fine-support vanishing and the later normalization to the existing filtered maps.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_mixed_common_state_source_data

open MME Module

universe u


set_option autoImplicit false
set_option warningAsError true

open MME.DWZSourceAligned

namespace MME.DWZSourceAligned

/-- The canonical square-pair basis of an arbitrary coarse block. -/
noncomputable def arbitraryCoarseComponentModeBasis
    (K : Type u) [Field K] (coarse : Fin 3 → Fin 5) (i : Fin 3) :
    Basis (DWZComponentRestriction.LiftedCoarsePair.{u} 6 (coarse i)) K
      (((cwSquareCanonicalGrading K 6).blockSubtensor coarse).V i) :=
  (DWZComponentRestriction.coarseClassBasis (K := K) 6 i
    (coarse i)).reindex Equiv.ulift.symm

/-- The canonical lifted coarse-pair word basis of an arbitrary per-mode
coarse address. -/
noncomputable def arbitraryCoarseAddressModeBasis
    (K : Type u) [Field K] {N : ℕ}
    (address : Fin 3 → Fin N → Fin 5) (i : Fin 3) :
    Basis (∀ r, DWZComponentRestriction.LiftedCoarsePair.{u} 6
      (address i r)) K
      ((gradedAddressBlock (cwSquareCanonicalGrading K 6) address).V i) := by
  unfold gradedAddressBlock
  exact TensorObj.kronFinModePiBasis N
    (fun r ↦ (cwSquareCanonicalGrading K 6).blockSubtensor
      (fun j ↦ address j r)) i
    (fun r ↦ arbitraryCoarseComponentModeBasis K
      (fun j ↦ address j r) i)

end MME.DWZSourceAligned

namespace MME.DWZGlobalCorrelated

/-- The mixed selected word, expressed in the ordinary coarse-address basis
of the owner of each tensor mode. -/
def step1MixedSelectedWord
    {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    ∀ i, AddressModeWord
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i)) i :=
  Fin.cases x
    (Fin.cases y (Fin.cases W (fun j : Fin 0 ↦ Fin.elim0 j)))

/-- The modewise normal form targeted by the mixed selected-map
calculation. -/
noncomputable def step1MixedSelectedNormalMap
    (K : Type u) [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    ∀ i,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i :=
  fun i ↦
    ((step1FilteredBrokenAddressMaps K m
        (sourceWord reindex edge
          (step1MixedOwnerIndex competitor owner i))
        (commonStateBrokenCopy m reindex q edge
          (step1MixedOwnerIndex competitor owner i)) i).comp
      (DWZComponentRestriction.basisLabelProjection
        (coarseAddressModeBasis K
          (sourceWord reindex edge
            (step1MixedOwnerIndex competitor owner i)) i)
        id {step1MixedSelectedWord reindex edge competitor owner W x y i})).comp
      (step1MixedCoarseProj K reindex edge competitor owner i)

/-- The Step-1 filtered broken-owner postmap on the mixed coarse address,
before selecting one canonical word in that mode. -/
noncomputable def step1MixedFilteredAddressPost
    (K : Type u) [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) :
    ∀ i,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (step1MixedAddress reindex edge competitor owner)).V i →ₗ[K]
      (commonStateBrokenAddressObj K m reindex q edge
        (step1MixedOwnerIndex competitor owner i)).V i :=
  fun i ↦
    (step1FilteredBrokenAddressMaps K m
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i))
      (commonStateBrokenCopy m reindex q edge
        (step1MixedOwnerIndex competitor owner i)) i).comp
      (step1MixedModeEquiv K reindex edge competitor owner i).toLinearMap

/-- Select the mixed canonical X/Y/Z word after the filtered mixed-address
postmap. -/
noncomputable def step1MixedSelectedAddressMaps
    (K : Type u) [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    ∀ i,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (step1MixedAddress reindex edge competitor owner)).V i →ₗ[K]
      (commonStateBrokenAddressObj K m reindex q edge
        (step1MixedOwnerIndex competitor owner i)).V i :=
  fun i ↦
    (step1MixedFilteredAddressPost K m reindex q edge
      competitor owner i).comp
      (DWZComponentRestriction.basisLabelProjection
        (arbitraryCoarseAddressModeBasis K
          (step1MixedAddress reindex edge competitor owner) i)
        id {step1MixedSelectedWord reindex edge competitor owner W x y i})

/-- Full-source selected mixed-owner maps: coarse-address projection followed
by the selected filtered address postmap. -/
noncomputable def step1MixedSelectedFullMaps
    (K : Type u) [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    ∀ i,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
      (commonStateBrokenAddressObj K m reindex q edge
        (step1MixedOwnerIndex competitor owner i)).V i :=
  fun i ↦
    (step1MixedSelectedAddressMaps K m reindex q edge
      competitor owner W x y i).comp
      (gradedAddressProj (cwSquareCanonicalGrading K 6) L
        (step1MixedAddress reindex edge competitor owner) i)

end MME.DWZGlobalCorrelated


