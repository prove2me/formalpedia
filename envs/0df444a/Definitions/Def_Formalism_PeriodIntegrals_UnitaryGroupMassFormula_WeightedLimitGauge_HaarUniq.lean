-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:09.781069+00:00
-- url     : https://prove2.me/theorems/b424a7c8-228e-4fdf-ae78-2fafaff22ea4
-- title:
--   Haar Uniq
-- statement:
--   Definitions and structural lemmas for Haar Uniq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeightedLimitGauge/HaarUniq.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
namespace PI.RhsWLim.W.HU
open PI.RhsWLim
variable {k r : ℕ}
def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩
def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)
theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega
theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)
theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num
theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
theorem isUnit_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]
theorem uh_one : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
theorem uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) : g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']
theorem uh_inv {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g⁻¹ ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
theorem uwb_one : (1 : Mat k r) ∈ UWb k r :=
  ⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩⟩
theorem uwb_mul {g h : Mat k r} (hg : g ∈ UWb k r) (hh : h ∈ UWb k r) : g * h ∈ UWb k r := by
  refine ⟨uh_mul hg.1 hh.1, fun c => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, (hh.2 c).1, (hg.2 c).1]
  · rw [← Matrix.mulVec_mulVec, (hh.2 c).2, (hg.2 c).2]
theorem uwb_unit {g : Mat k r} (hg : g ∈ UWb k r) : IsUnit g.det := isUnit_of_uh hg.1
theorem uwb_inv {g : Mat k r} (hg : g ∈ UWb k r) : g⁻¹ ∈ UWb k r := by
  have hu := uwb_unit hg
  have fix : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := by
    intro v hv
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hg.1, fun c => ⟨fix _ (hg.2 c).1, fix _ (hg.2 c).2⟩⟩
def amb (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ UWb k r}
def invM (x : Mt k r) : Mt k r := ((Matrix.of x : Mat k r)⁻¹ : Mat k r)
def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det
theorem detF_cont : Continuous (detF (k := k) (r := r)) := Continuous.matrix_det (continuous_id (X := Mat k r))
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := Continuous.matrix_adjugate (continuous_id (X := Mat k r))
theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  unfold invM detF adjF
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl
theorem invM_contOn : ContinuousOn (invM : Mt k r → Mt k r) {x | detF x ≠ 0} := by
  rw [invM_smul]
  exact (detF_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjF_cont.continuousOn
def Gp (k r : ℕ) : Type := {x : Mt k r // x ∈ amb k r}
instance : TopologicalSpace (Gp k r) := inferInstanceAs (TopologicalSpace {x : Mt k r // x ∈ amb k r})
instance : MeasurableSpace (Gp k r) := inferInstanceAs (MeasurableSpace {x : Mt k r // x ∈ amb k r})
instance : BorelSpace (Gp k r) := inferInstanceAs (BorelSpace {x : Mt k r // x ∈ amb k r})
instance : SecondCountableTopology (Gp k r) :=
  inferInstanceAs (SecondCountableTopology {x : Mt k r // x ∈ amb k r})
def inc (x : Gp k r) : Mt k r := x.1
theorem inc_cont : Continuous (inc : Gp k r → Mt k r) := continuous_subtype_val
theorem inc_mem (x : Gp k r) : Matrix.of (inc x) ∈ UWb k r := x.2
theorem lmulM_mem {x y : Mt k r} (hx : x ∈ amb k r) (hy : y ∈ amb k r) :
    lmulM (Matrix.of x) y ∈ amb k r := by
  show (Matrix.of x : Mat k r) * Matrix.of y ∈ UWb k r
  exact uwb_mul hx hy
theorem invM_mem {x : Mt k r} (hx : x ∈ amb k r) : invM x ∈ amb k r := by
  show (Matrix.of x : Mat k r)⁻¹ ∈ UWb k r
  exact uwb_inv hx
theorem one_mem_amb : (fun i j => (1 : Mat k r) i j : Mt k r) ∈ amb k r := by
  show (1 : Mat k r) ∈ UWb k r
  exact uwb_one
instance : Group (Gp k r) where
  mul a b := ⟨lmulM (Matrix.of a.1) b.1, lmulM_mem a.2 b.2⟩
  one := ⟨fun i j => (1 : Mat k r) i j, one_mem_amb⟩
  inv a := ⟨invM a.1, invM_mem a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1 : Mat k r) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1 : Mat k r))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1 : Mat k r))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1 : Mat k r) (uwb_unit a.2))
instance : IsTopologicalGroup (Gp k r) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact Continuous.matrix_mul (A := fun p : Gp k r × Gp k r => (Matrix.of (inc p.1) : Mat k r))
      (B := fun p : Gp k r × Gp k r => (Matrix.of (inc p.2) : Mat k r))
      (inc_cont.comp continuous_fst) (inc_cont.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact invM_contOn.comp_continuous inc_cont (fun x => (uwb_unit (inc_mem x)).ne_zero)
def pull (μ : Measure (Mt k r)) : Measure (Gp k r) := μ.comap inc
end PI.RhsWLim.W.HU
namespace PI.RhsWLim.W
open PI.RhsWLim HU
end PI.RhsWLim.W


