-- Prove2me | Definitions.Def_mme_dwz_step1_mixed_common_state_source_data
-- name    : mme_dwz_step1_mixed_common_state_source_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-28T10:12:31.853826+00:00
-- url     : https://prove2.me/theorems/a7ea9d96-dc78-4d0b-9d84-95bdcd489738
-- title:
--   DWZ Step-1 mixed-owner common-state source maps
-- statement:
--   This module packages the exact source-side data used to analyze a mixed tensor term with one common X/Y competitor and one Z owner in a shared affine state. It defines the mixed owner tuple and mixed coarse address, the canonical transport from that address to each owner's ordinary coarse-address block, the Step-1-filtered maps with one selected surviving Z word, the corresponding selected X/Y maps and coordinatewise fine-support predicate, the pointwise ordinary source-family singleton maps, and the equivalent raw post-projection map and tensor presentation. These definitions isolate the paper's Additional Zeroing-Out Step 1 geometry from the later support, collision, and direct-sum theorems.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Steps 1 and 2 and Claim 6.2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps
import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZGlobalCorrelated

open MME.DWZSourceAligned
open MME.DWZStep1Support

/-- The mixed owner tuple with one common X/Y competitor and one Z owner. -/
def step1MixedOwnerIndex {n : ℕ} (competitor owner : Fin n) :
    Fin 3 → Fin n :=
  ![competitor, competitor, owner]

/-- The broken source object attached to one owner in a common affine state. -/
noncomputable def commonStateBrokenAddressObj
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (j : Fin n) : TensorObj K 3 :=
  brokenAddressObj K m (sourceWord reindex edge j)
    (commonStateBrokenCopy m reindex q edge j)

/-- The mixed coarse address whose three modes are owned by the mixed owner
tuple. -/
def step1MixedAddress {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) : Fin 3 → Fin L → Fin 5 :=
  fun i r ↦ coarseAddress
    (sourceWord reindex edge (step1MixedOwnerIndex competitor owner i)) i r

/-- In one fixed mode, the mixed coarse block is canonically equivalent to
the ordinary coarse-address block of that mode's owner. -/
noncomputable def step1MixedModeEquiv
    (K : Type u) [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) (i : Fin 3) :
    (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (step1MixedAddress reindex edge competitor owner)).V i ≃ₗ[K]
      (coarseAddressObj K
        (sourceWord reindex edge
          (step1MixedOwnerIndex competitor owner i))).V i := by
  exact CoupledCTensorPackaging.gradedAddressBlockModeEquiv
    (cwSquareCanonicalGrading K 6) L
    (step1MixedAddress reindex edge competitor owner)
    (coarseAddress
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i))) i (by rfl)

/-- Coarse-address projections from the full squared-CW power for the mixed
X/Y/Z owner tuple. -/
noncomputable def step1MixedCoarseProj
    (K : Type u) [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) :
    ∀ i : Fin 3,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
        (coarseAddressObj K
          (sourceWord reindex edge
            (step1MixedOwnerIndex competitor owner i))).V i :=
  fun i ↦
    (step1MixedModeEquiv K reindex edge competitor owner i).toLinearMap.comp
      (gradedAddressProj (cwSquareCanonicalGrading K 6) L
        (step1MixedAddress reindex edge competitor owner) i)

/-- Address-block postmaps with Step-1 X/Y filters and one selected canonical
Z word of the Z owner. -/
noncomputable def step1FilteredMixedSingletonAddressPost
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    ∀ i : Fin 3,
      (coarseAddressObj K
        (sourceWord reindex edge
          (step1MixedOwnerIndex competitor owner i))).V i →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i := by
  let base := fun i ↦
    step1FilteredBrokenAddressMaps K m
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i))
      (commonStateBrokenCopy m reindex q edge
        (step1MixedOwnerIndex competitor owner i)) i
  let singleton := DWZComponentRestriction.basisLabelProjection
    (coarseAddressZBasis K (sourceWord reindex edge owner)) id {W}
  exact Function.update base 2
    (((brokenAddressGrading K m (sourceWord reindex edge owner)
      (commonStateBrokenCopy m reindex q edge owner)).blockProj 2 0).comp
        singleton)

/-- The same postmaps, with their domains transported from the mixed coarse
address block to each mode owner's ordinary coarse-address block. -/
noncomputable def step1FilteredMixedSingletonPost
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    ∀ i : Fin 3,
      (gradedAddressBlock (cwSquareCanonicalGrading K 6)
        (step1MixedAddress reindex edge competitor owner)).V i →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i :=
  fun i ↦
    (step1FilteredMixedSingletonAddressPost K m reindex q edge
      competitor owner W i).comp
        (step1MixedModeEquiv K reindex edge competitor owner i).toLinearMap

/-- Full-source maps obtained from the preceding address postmaps. -/
noncomputable def step1FilteredMixedSingletonMaps
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    ∀ i : Fin 3,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i :=
  fun i ↦
    (step1FilteredMixedSingletonAddressPost K m reindex q edge
      competitor owner W i).comp
      (step1MixedCoarseProj K reindex edge competitor owner i)

/-- Replace the filtered X mode by one selected word singleton. -/
noncomputable def step1FilteredMixedSelectedXMaps
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0) :
    ∀ i : Fin 3,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i := by
  let G := brokenAddressGrading K m (sourceWord reindex edge competitor)
    (commonStateBrokenCopy m reindex q edge competitor)
  let sx := DWZComponentRestriction.basisLabelProjection
    (coarseAddressModeBasis K (sourceWord reindex edge competitor) 0) id {x}
  let selectX := (G.blockProj 0 0).comp
    (addressXStep1Projector K m (sourceWord reindex edge competitor))
  let pre := step1MixedCoarseProj K reindex edge competitor owner
  exact Function.update
    (step1FilteredMixedSingletonMaps K m reindex q edge competitor owner W)
    0 (((selectX.comp sx).comp (pre 0)))

/-- Replace both filtered X/Y modes by selected accepted word singletons. -/
noncomputable def step1FilteredMixedSelectedXYMaps
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) :
    ∀ i : Fin 3,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i := by
  let G := brokenAddressGrading K m (sourceWord reindex edge competitor)
    (commonStateBrokenCopy m reindex q edge competitor)
  let sy := DWZComponentRestriction.basisLabelProjection
    (coarseAddressModeBasis K (sourceWord reindex edge competitor) 1) id {y}
  let selectY := (G.blockProj 1 0).comp
    (addressYStep1Projector K m (sourceWord reindex edge competitor))
  let pre := step1MixedCoarseProj K reindex edge competitor owner
  exact Function.update
    (step1FilteredMixedSelectedXMaps K m reindex q edge
      competitor owner W x)
    1 (((selectY.comp sy).comp (pre 1)))

/-- Coordinatewise fine support of one accepted selected X/Y pair and the
chosen Z word. -/
def step1MixedSelectedFineSupported
    (K : Type u) [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner))
    (x : AddressModeWord (sourceWord reindex edge competitor) 0)
    (y : AddressModeWord (sourceWord reindex edge competitor) 1) : Prop :=
  ∀ r : Fin L,
    (cwSquareFineSplitGrading K 6).blockTensor
      (fun i ↦ MME.DWZStep1Support.fineSplitGrade
        (![addressModeLeftGrade x r,
          addressModeLeftGrade y r,
          (W r).leftGrade] i)
        (![addressModeRightGrade x r,
          addressModeRightGrade y r,
          (W r).rightGrade] i)) ≠ 0

/-- Exact remaining coordinate adapter needed by the filtered mixed-owner
argument: nonzero selected accepted X/Y words have full fine support. -/
def Step1MixedSelectedSupportProperty
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) : Prop :=
  ∀ (x : AddressModeWord (sourceWord reindex edge competitor) 0),
    addressXWordPassesStep1 m (sourceWord reindex edge competitor) x →
  ∀ (y : AddressModeWord (sourceWord reindex edge competitor) 1),
    addressYWordPassesStep1 m (sourceWord reindex edge competitor) y →
  PiTensorProduct.map
      (step1FilteredMixedSelectedXYMaps K m reindex q edge
        competitor owner W x y)
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t ≠ 0 →
    step1MixedSelectedFineSupported K reindex edge
      competitor owner W x y

/-- The ordinary source-family maps for a common X/Y competitor and Z owner,
with the owner's surviving Z word selected at mode two. -/
noncomputable def step1MixedSourceFamilySingletonMaps
    (K : Type u) [Field K]
    (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    ∀ i,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i :=
  Function.update
    (fun i ↦ step1FilteredBrokenSourceMaps K m
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i))
      (commonStateBrokenCopy m reindex q edge
        (step1MixedOwnerIndex competitor owner i)) i)
    2
    ((((step1FilteredBrokenAddressMaps K m
        (sourceWord reindex edge owner)
        (commonStateBrokenCopy m reindex q edge owner) 2).comp
      (DWZComponentRestriction.basisLabelProjection
        (coarseAddressZBasis K (sourceWord reindex edge owner))
        id {W})).comp
      (gradedAddressProj (cwSquareCanonicalGrading K 6) L
        (coarseAddress (sourceWord reindex edge owner)) 2)))

/-- The map family in the generic post-projection presentation used by the
common-state mixed-singleton theorem. -/
noncomputable def step1FilteredMixedRawMaps
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    ∀ i : Fin 3,
      (((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).V i) →ₗ[K]
        (commonStateBrokenAddressObj K m reindex q edge
          (step1MixedOwnerIndex competitor owner i)).V i :=
  fun i ↦
    (step1FilteredMixedSingletonPost K m reindex q edge
      competitor owner W i).comp
      (gradedAddressProj (cwSquareCanonicalGrading K 6) L
        (step1MixedAddress reindex edge competitor owner) i)

/-- The tensor value of the generic post-projection presentation. -/
noncomputable def step1FilteredMixedRawTensor
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) :
    PiTensorProduct K (fun i ↦
      (commonStateBrokenAddressObj K m reindex q edge
        (step1MixedOwnerIndex competitor owner i)).V i) :=
  PiTensorProduct.map
    (step1FilteredMixedRawMaps K m reindex q edge competitor owner W)
    ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow L).t

/-- Nonvanishing in the generic common-state map presentation. -/
def Step1FilteredMixedRawNonzero
    (K : Type u) [Field K] (m : ℕ) {p N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n)
    (W : AddressZWord (sourceWord reindex edge owner)) : Prop :=
  step1FilteredMixedRawTensor K m reindex q edge competitor owner W ≠ 0

end MME.DWZGlobalCorrelated


