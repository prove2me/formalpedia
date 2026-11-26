-- Prove2me | Definitions.Def_FD1D_Spatial
-- name    : FD1D_Spatial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:13:29.389257+00:00
-- url     : https://prove2.me/theorems/51170d21-fede-5bfa-bb03-eb3e3974da5f
-- title:
--   Spatial
-- statement:
--   Definitions and structural lemmas for Spatial, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Spatial.lean

import Definitions.Def_FD1D_Transport
import Definitions.Def_FD1D_Markov
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_HaarSupportNested_trans
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


set_option autoImplicit true
namespace FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory
def dyadicLeafSumEquiv (L : ℕ) :
    DyadicNode L ⊕ DyadicNode L ≃ DyadicNode (L + 1) :=
  finSumFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_two]))
@[simp]
theorem dyadicLeafSumEquiv_inl_val {L : ℕ} (i : DyadicNode L) :
    (dyadicLeafSumEquiv L (Sum.inl i)).val = i.val := by
  simp [dyadicLeafSumEquiv]
@[simp]
theorem dyadicLeafSumEquiv_inr_val {L : ℕ} (i : DyadicNode L) :
    (dyadicLeafSumEquiv L (Sum.inr i)).val = 2 ^ L + i.val := by
  simp [dyadicLeafSumEquiv, Nat.add_comm]
namespace DyadicMass
def leafMass : {L : ℕ} → DyadicMass L → DyadicNode L → ℝ
  | 0, leaf mass, _ => mass
  | L + 1, branch left right, i =>
      match (dyadicLeafSumEquiv L).symm i with
      | Sum.inl j => leafMass left j
      | Sum.inr j => leafMass right j
def lowerMass : {L : ℕ} → DyadicMass L → DyadicNode L → ℝ
  | 0, leaf _, _ => 0
  | L + 1, branch left right, i =>
      match (dyadicLeafSumEquiv L).symm i with
      | Sum.inl j => lowerMass left j
      | Sum.inr j => left.total + lowerMass right j
def selectedIndex : {L : ℕ} → DyadicMass L → ℝ → DyadicNode L
  | 0, leaf _, _ => 0
  | L + 1, branch left right, u =>
      if u ≤ left.total then
        dyadicLeafSumEquiv L (Sum.inl (selectedIndex left u))
      else
        dyadicLeafSumEquiv L
          (Sum.inr (selectedIndex right (u - left.total)))
@[simp]
theorem leafMass_left {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).leafMass
        (dyadicLeafSumEquiv L (Sum.inl i)) = left.leafMass i := by
  simp [leafMass]
@[simp]
theorem leafMass_right {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).leafMass
        (dyadicLeafSumEquiv L (Sum.inr i)) = right.leafMass i := by
  simp [leafMass]
@[simp]
theorem lowerMass_left {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).lowerMass
        (dyadicLeafSumEquiv L (Sum.inl i)) = left.lowerMass i := by
  simp [lowerMass]
@[simp]
theorem lowerMass_right {L : ℕ} (left right : DyadicMass L)
    (i : DyadicNode L) :
    (branch left right).lowerMass
        (dyadicLeafSumEquiv L (Sum.inr i)) =
      left.total + right.lowerMass i := by
  simp [lowerMass]
theorem sum_leafMass {L : ℕ} (q : DyadicMass L) :
    ∑ i, q.leafMass i = q.total := by
  induction q with
  | leaf mass =>
      simp [leafMass, total]
  | @branch L left right ihLeft ihRight =>
      calc
        ∑ i, (branch left right).leafMass i =
            ∑ s : DyadicNode L ⊕ DyadicNode L,
              (branch left right).leafMass (dyadicLeafSumEquiv L s) := by
                symm
                exact (dyadicLeafSumEquiv L).sum_comp
                  (fun i => (branch left right).leafMass i)
        _ = ∑ i, left.leafMass i + ∑ i, right.leafMass i := by
              rw [Fintype.sum_sum_type]
              simp
        _ = (branch left right).total := by
              simp [ihLeft, ihRight, total]
theorem leafMass_nonneg {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) (i : DyadicNode L) :
    0 ≤ q.leafMass i := by
  induction q with
  | leaf mass =>
      change 0 ≤ mass at hq
      simpa [leafMass] using hq
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simpa using ihLeft hq.1 i
      · simpa using ihRight hq.2 i
theorem lowerMass_nonneg {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) (i : DyadicNode L) :
    0 ≤ q.lowerMass i := by
  induction q with
  | leaf =>
      simp [lowerMass]
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simpa using ihLeft hq.1 i
      · simp only [lowerMass_right]
        exact add_nonneg (total_nonneg left hq.1) (ihRight hq.2 i)
theorem lowerMass_add_leafMass_le_total {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) (i : DyadicNode L) :
    q.lowerMass i + q.leafMass i ≤ q.total := by
  induction q with
  | leaf mass =>
      simp [lowerMass, leafMass, total]
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · simp only [lowerMass_left, leafMass_left, total]
        exact (ihLeft hq.1 i).trans
          (le_add_of_nonneg_right (total_nonneg right hq.2))
      · simp only [lowerMass_right, leafMass_right, total]
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_left (ihRight hq.2 i) left.total
theorem selectedIndex_measurable {L : ℕ} (q : DyadicMass L) :
    Measurable q.selectedIndex := by
  induction q with
  | leaf =>
      exact measurable_const
  | @branch L left right ihLeft ihRight =>
      apply Measurable.ite (measurableSet_le measurable_id measurable_const)
      · exact (measurable_of_finite
          (fun i : DyadicNode L =>
            dyadicLeafSumEquiv L (Sum.inl i))).comp ihLeft
      · exact (measurable_of_finite
          (fun i : DyadicNode L =>
            dyadicLeafSumEquiv L (Sum.inr i))).comp
              (ihRight.comp (measurable_id.sub measurable_const))
theorem selectedIndex_eq_iff_mem_massInterval {L : ℕ} (q : DyadicMass L)
    (hq : q.allNonneg) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ q.total)
    (i : DyadicNode L) :
    q.selectedIndex u = i ↔
      u ∈ Ioc (q.lowerMass i) (q.lowerMass i + q.leafMass i) := by
  induction q generalizing u with
  | leaf mass =>
      rw [Fin.eq_zero i]
      have huMass : u ≤ mass := by simpa [total] using hu1
      simp [selectedIndex, lowerMass, leafMass, hu0, huMass]
  | @branch L left right ihLeft ihRight =>
      obtain ⟨i | i, rfl⟩ := (dyadicLeafSumEquiv L).surjective i
      · constructor
        · intro hsel
          have huLeft : u ≤ left.total := by
            by_contra hnot
            rw [selectedIndex, if_neg hnot] at hsel
            have hs := (dyadicLeafSumEquiv L).injective hsel
            simp at hs
          have hlocal : left.selectedIndex u = i := by
            rw [selectedIndex, if_pos huLeft] at hsel
            exact Sum.inl.inj ((dyadicLeafSumEquiv L).injective hsel)
          simpa using (ihLeft hq.1 hu0 huLeft i).mp hlocal
        · intro hmem
          have hmem' :
              u ∈ Ioc (left.lowerMass i)
                (left.lowerMass i + left.leafMass i) := by
            simpa using hmem
          have huLeft : u ≤ left.total := by
            exact hmem'.2.trans
              (left.lowerMass_add_leafMass_le_total hq.1 i)
          have hlocal :=
            (ihLeft hq.1 hu0 huLeft i).mpr hmem'
          simp [selectedIndex, huLeft, hlocal]
      · constructor
        · intro hsel
          have huRight : ¬u ≤ left.total := by
            intro huLeft
            rw [selectedIndex, if_pos huLeft] at hsel
            have hs := (dyadicLeafSumEquiv L).injective hsel
            simp at hs
          have huLocal0 : 0 < u - left.total := by linarith
          have huLocal1 : u - left.total ≤ right.total := by
            rw [total] at hu1
            linarith
          have hlocal : right.selectedIndex (u - left.total) = i := by
            rw [selectedIndex, if_neg huRight] at hsel
            exact Sum.inr.inj ((dyadicLeafSumEquiv L).injective hsel)
          have hinter :=
            (ihRight hq.2 huLocal0 huLocal1 i).mp hlocal
          simp only [lowerMass_right, leafMass_right, mem_Ioc]
          constructor <;> linarith [hinter.1, hinter.2]
        · intro hmem
          simp only [lowerMass_right, leafMass_right, mem_Ioc] at hmem
          have hLower := right.lowerMass_nonneg hq.2 i
          have huRight : ¬u ≤ left.total := by
            intro hu
            linarith [hmem.1, hLower]
          have huLocal0 : 0 < u - left.total := by linarith
          have huLocal1 : u - left.total ≤ right.total := by
            rw [total] at hu1
            linarith
          have hinter :
              u - left.total ∈
                Ioc (right.lowerMass i)
                  (right.lowerMass i + right.leafMass i) := by
            constructor <;> linarith [hmem.1, hmem.2]
          have hlocal :=
            (ihRight hq.2 huLocal0 huLocal1 i).mpr hinter
          simp [selectedIndex, huRight, hlocal]
def uniformDemand : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)
def selectedIndexPushforwardMass {L : ℕ} (q : DyadicMass L)
    (i : DyadicNode L) : ℝ :=
  ((Measure.map q.selectedIndex uniformDemand) {i}).toReal
theorem ae_ne_zero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
  rw [ae_iff]
  simp only [not_ne_iff]
  rw [show {u : ℝ | u = 0} = ({0} : Set ℝ) by ext u; simp]
  exact measure_singleton 0
theorem selectedIndexPushforwardMass_eq_leafMass {L : ℕ}
    (q : DyadicMass L) (hq : q.IsProbability) (i : DyadicNode L) :
    q.selectedIndexPushforwardMass i = q.leafMass i := by
  unfold selectedIndexPushforwardMass uniformDemand
  rw [Measure.map_apply q.selectedIndex_measurable
    (measurableSet_singleton i)]
  rw [Measure.restrict_apply
    (q.selectedIndex_measurable (measurableSet_singleton i))]
  have hsets :
      (((q.selectedIndex ⁻¹' ({i} : Set (DyadicNode L))) ∩
          Icc (0 : ℝ) 1) : Set ℝ) =ᵐ[volume]
      Ioc (q.lowerMass i) (q.lowerMass i + q.leafMass i) := by
    filter_upwards [ae_ne_zero] with u hu
    apply propext
    change
      (q.selectedIndex u = i ∧ u ∈ Icc (0 : ℝ) 1) ↔
        u ∈ Ioc (q.lowerMass i) (q.lowerMass i + q.leafMass i)
    constructor
    · rintro ⟨hsel, huUnit⟩
      have huPos : 0 < u := lt_of_le_of_ne huUnit.1 (Ne.symm hu)
      exact (q.selectedIndex_eq_iff_mem_massInterval hq.nonneg
        huPos (by simpa [hq.total_eq_one] using huUnit.2) i).mp hsel
    · intro hmem
      have hLower := q.lowerMass_nonneg hq.nonneg i
      have hUpper := q.lowerMass_add_leafMass_le_total hq.nonneg i
      have huPos : 0 < u := by linarith [hmem.1]
      have huTotal : u ≤ q.total := hmem.2.trans hUpper
      constructor
      · exact (q.selectedIndex_eq_iff_mem_massInterval hq.nonneg
          huPos huTotal i).mpr hmem
      · exact ⟨huPos.le, by simpa [hq.total_eq_one] using huTotal⟩
  rw [measure_congr hsets, Real.volume_Ioc]
  have hmass := q.leafMass_nonneg hq.nonneg i
  rw [show q.lowerMass i + q.leafMass i - q.lowerMass i =
    q.leafMass i by ring]
  exact ENNReal.toReal_ofReal hmass
def selectedIndexLaw {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) : FiniteLaw (DyadicNode L) where
  mass := q.selectedIndexPushforwardMass
  mass_nonneg i := ENNReal.toReal_nonneg
  sum_mass := by
    simp_rw [q.selectedIndexPushforwardMass_eq_leafMass hq]
    rw [q.sum_leafMass, hq.total_eq_one]
@[simp]
theorem selectedIndexLaw_mass {L : ℕ} (q : DyadicMass L)
    (hq : q.IsProbability) (i : DyadicNode L) :
    (q.selectedIndexLaw hq).mass i = q.leafMass i :=
  q.selectedIndexPushforwardMass_eq_leafMass hq i
end DyadicMass
def dyadicCellWidth (L : ℕ) : ℝ :=
  1 / ((2 ^ L : ℕ) : ℝ)
def dyadicCellLeft {L : ℕ} (i : DyadicNode L) : ℝ :=
  i.val / ((2 ^ L : ℕ) : ℝ)
def dyadicCell {L : ℕ} (i : DyadicNode L) : Set ℝ :=
  Icc (dyadicCellLeft i) (dyadicCellLeft i + dyadicCellWidth L)
structure SupplyConfiguration (L m : ℕ) where
  location : Fin m → ℝ
  leaf : Fin m → DyadicNode L
  location_mem_unit : ∀ j, location j ∈ Icc (0 : ℝ) 1
  location_mem_cell : ∀ j, location j ∈ dyadicCell (leaf j)
namespace SupplyConfiguration
variable {L m : ℕ}
def leafCount (C : SupplyConfiguration L m) (i : DyadicNode L) : ℕ :=
  (Finset.univ.filter fun j => C.leaf j = i).card
theorem sum_leafCount (C : SupplyConfiguration L m) :
    ∑ i, C.leafCount i = m := by
  classical
  simp only [leafCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp
def countState (C : SupplyConfiguration L m) :
    InventoryState (DyadicNode L) m :=
  ⟨C.leafCount, C.sum_leafCount⟩
def representative (C : SupplyConfiguration L m) (fallback : Fin m)
    (i : DyadicNode L) : Fin m :=
  if h : ∃ j, C.leaf j = i then Classical.choose h else fallback
def Supports (C : SupplyConfiguration L m) (q : DyadicMass L) : Prop :=
  ∀ i, 0 < q.leafMass i → ∃ j, C.leaf j = i
def selectedSupplyIndex (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) (u : ℝ) : Fin m :=
  C.representative fallback (q.selectedIndex u)
def selectedSupplyPoint (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) (u : ℝ) : ℝ :=
  C.location (C.selectedSupplyIndex q fallback u)
def expectedActualDistance (C : SupplyConfiguration L m)
    (q : DyadicMass L) (fallback : Fin m) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, |C.selectedSupplyPoint q fallback u - u|
end SupplyConfiguration
end
end FD1D


