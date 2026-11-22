-- Prove2me | solution 1 for Autoconvolutions.blocks_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:48.047584+00:00
-- url     : https://prove2.me/submissions/6d453a2a-d41d-4104-8352-2d94c69af359

module
public import Definitions.Def_Autoconvolutions_Step
public import Definitions.Def_Autoconvolutions_Interpolation
public import Mathlib.MeasureTheory.Function.L2Space
public import Definitions.Def_Autoconvolutions_Bounds
public import Theorems.Thm_Autoconvolutions_plateau_energy_le

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators
open Autoconvolutions
namespace Autoconvolutions
theorem _root_.solution {ι : Type*} (d : ℕ) (p : Fin (d+1) → ℝ)
    (D : ℕ) (T : Finset ι) (code width : ι → ℕ) (height : ι → ℝ)
    (hinj : Set.InjOn code (↑T)) (hw : ∀ i ∈ T, width i ≤ D)
    (heq : ∀ i ∈ T, ∀ h ≤ width i, convCoeff d p ((D*code i+h : ℕ) : ℤ) = height i) :
    ∑ i ∈ T, (width i : ℝ)*(height i)^2 ≤ (eLpNorm (auto (step d p)) 2 volume).toReal^2 := by
  classical
  let encode (i : ι) (h : ℕ) : ℤ := (D*code i+h : ℕ)
  let cells (i : ι) : Finset ℤ := (Finset.range (width i)).image (encode i)
  let S := T.biUnion cells
  have sep {i j : ι} {u v : ℕ} (hij : code i < code j) (hu : u < width i) (hi : i ∈ T) :
      D*code i+u < D*code j+v := by
    have ha := Nat.mul_le_mul_left D (show code i + 1 ≤ code j by omega)
    rw [Nat.mul_add, Nat.mul_one] at ha
    have := hw i hi
    omega
  have disj : Set.Pairwise (↑T) (fun i j => Disjoint (cells i) (cells j)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v,hv,h⟩ := Finset.mem_image.mp hz'
    have h' : D*code j+v = D*code i+u := by
      dsimp [encode] at h
      exact_mod_cast h
    have hne' : code i ≠ code j := fun hh => hij (hinj hi hj hh)
    rcases lt_or_gt_of_ne hne' with hc | hc
    · exact (sep (v := v) hc (Finset.mem_range.mp hu) hi).ne h'.symm
    · exact (sep (v := u) hc (Finset.mem_range.mp hv) hj).ne h'
  have mass : ∑ k ∈ S, (convCoeff d p k)^2 = ∑ i ∈ T, (width i : ℝ)*(height i)^2 := by
    rw [show S = T.biUnion cells from rfl, Finset.sum_biUnion disj]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show cells i = (Finset.range (width i)).image (encode i) from rfl,
      Finset.sum_image (fun u _ v _ huv => by
        have : D*code i+u = D*code i+v := by
          dsimp [encode] at huv
          exact_mod_cast huv
        omega)]
    calc
      _ = ∑ _h ∈ Finset.range (width i), (height i)^2 := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [show convCoeff d p (encode i h) = height i from
          heq i hi h (Finset.mem_range.mp hh).le]
      _ = _ := by simp
  rw [← mass]
  apply plateau_energy_le _ _ S (convCoeff d p) (fun _ _ => rfl)
  intro z hz
  obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hzi
  have hm : h < width i := Finset.mem_range.mp hh
  have hcast : encode i h + 1 = ((D*code i+(h+1) : ℕ):ℤ) := by
    simp [encode, add_assoc]
  rw [hcast, heq i hi (h+1) (by omega)]
  exact (heq i hi h hm.le).symm
end Autoconvolutions
