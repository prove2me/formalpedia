-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimFlags
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimFlags
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:58:06.307207+00:00
-- url     : https://prove2.me/theorems/969eaff3-c653-4f1e-87f1-11358bf1841e
-- title:
--   Topological Krull Dim Flags
-- statement:
--   Definitions and structural lemmas for Topological Krull Dim Flags, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TopologicalKrullDimFlags.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousCellMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InjectiveCellMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenMapCellMapStatement
import Theorems.Thm_GlobalTheory_FlagPts_cellMap_zero
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
import Theorems.Thm_GlobalTheory_T_injective_cellMap
import Theorems.Thm_GlobalTheory_T_topologicalKrullDim_affine_points
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_forall_exists_isOpen
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding
import Theorems.Thm_P2M_GlobalTheory_T_continuous_cellMap__068c99a1676a
import Theorems.Thm_P2M_GlobalTheory_T_isOpenMap_cellMap__6da3daee2469
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
namespace GlobalTheory.FlagPts
theorem card_lowerPairs (d : ℕ) : Fintype.card {p : Fin d × Fin d // p.2 < p.1} = d * (d - 1) / 2 := by
  rw [Fintype.card_subtype, ← Finset.sum_range_id, Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
theorem card_cellIdx {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] {n : ℕ} (hn : ∀ i, finrank k (V i) = n) :
    Fintype.card (CellIdx k V) = Fintype.card ι * (n * (n - 1) / 2) := by
  have h1 : Fintype.card (CellIdx k V) =
      ∑ i, Fintype.card {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1} := by
    unfold CellIdx
    convert Fintype.card_sigma (α := fun i => {p : Fin (finrank k (V i)) × Fin (finrank k (V i)) // p.2 < p.1})
  rw [h1]
  simp only [card_lowerPairs, hn, Finset.sum_const, Finset.card_univ, smul_eq_mul]
theorem isOpenEmbedding_cellMap {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Topology.IsOpenEmbedding (cellMap b) :=
  .of_continuous_injective_isOpenMap (GlobalTheory.T.continuous_cellMap' k ι V b) (GlobalTheory.T.injective_cellMap k ι V b) (GlobalTheory.T.isOpenMap_cellMap' k ι V b)
theorem topologicalKrullDim_flags (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ)
    (hn : ∀ i, finrank k (V i) = n) :
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) := by
  have hU : topologicalKrullDim (Set.univ : Set (Flags k V)) = topologicalKrullDim (Flags k V) :=
    (Homeomorph.Set.univ (Flags k V)).isHomeomorph.topologicalKrullDim_eq
  rw [← hU, ← card_cellIdx (k := k) (V := V) hn, ← GlobalTheory.T.topologicalKrullDim_affine_points k (CellIdx k V)]
  refine GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun F _ => ?_
  obtain ⟨b, rfl⟩ := flags_surjective F
  have he := isOpenEmbedding_cellMap b
  refine ⟨Set.range (cellMap b), he.isOpen_range, ⟨0, cellMap_zero b⟩, ?_⟩
  rw [Set.inter_univ]
  exact GlobalTheory.topologicalKrullDim_eq_of_isEmbedding he.isEmbedding rfl
example : ∀ (k : Type) [Field k] [IsAlgClosed k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (n : ℕ), (∀ i, finrank k (V i) = n) →
    topologicalKrullDim (Flags k V) = (Fintype.card ι * (n * (n - 1) / 2) : ℕ) :=
  topologicalKrullDim_flags
end GlobalTheory.FlagPts


