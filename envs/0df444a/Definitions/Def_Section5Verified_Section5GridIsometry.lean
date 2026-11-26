-- Prove2me | Definitions.Def_Section5Verified_Section5GridIsometry
-- name    : Section5Verified_Section5GridIsometry
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:43.087633+00:00
-- url     : https://prove2.me/theorems/f566a610-1dbd-4ca6-9255-cb77cc3fc061
-- title:
--   Section5GridIsometry — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5GridIsometry; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CellQuadrature
import Definitions.Def_Section5Verified_Section5FiniteGridMeasure
import Definitions.Def_Section5Verified_Section5GaussianSampling
import Definitions.Def_Section5Verified_Section5GaussianTail
import Definitions.Def_Section5Verified_Section5MultivariateSampling
import Definitions.Def_Section5Verified_Section5PhaseStateError
import Mathlib
section
set_option autoImplicit false

open MeasureTheory QuantumLTF.Example

/-! Exact correspondence between grid vectors and cell-constant L2 functions. -/

noncomputable def section5_grid_node (n M : ℕ) (j : Fin n → Fin M) : Fin n → ℝ :=
  fun i => -gridRadius M+(j i:ℝ)*gridSpacing M

noncomputable def section5_grid_lift (n M : ℕ) (F : (Fin n → ℝ) → ℂ) :
    (Fin n → ℝ) → ℂ :=
  (section5_grid_box n M).indicator (fun x => F (fun i => roundCoord M (x i)))

noncomputable def section5_grid_vector (n M : ℕ) (F : (Fin n → ℝ) → ℂ) :
    EuclideanSpace ℂ (Fin n → Fin M) :=
  WithLp.toLp 2 (fun j => (Real.sqrt ((gridSpacing M)^n) : ℂ)*F (section5_grid_node n M j))

theorem section5_gridSpacing_positive (M : ℕ) (hM : 0 < M) : 0 < gridSpacing M := by
  unfold gridSpacing
  positivity

theorem section5_roundCoord_grid_sample (M : ℕ) :
    roundCoord M = section5_grid_sample (-gridRadius M) (gridSpacing M) := by
  funext x
  simp only [roundCoord,section5_grid_sample,sub_neg_eq_add]

theorem section5_grid_window_eq (M : ℕ) :
    (volume.restrict (Set.Ico (-gridRadius M) (-gridRadius M+M*gridSpacing M))) =
      section5_window_measure M := by
  have hright : -gridRadius M+M*gridSpacing M = gridRadius M := by
    unfold gridRadius
    ring
  rw [hright,restrict_Ico_eq_restrict_Ioc]
  rfl







theorem section5_grid_lift_memLp (n M : ℕ) (hM : 0 < M)
    (F : (Fin n → ℝ) → ℂ) (hF : Measurable F) :
    MemLp (section5_grid_lift n M F) 2
      (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))) := by
  apply (memLp_indicator_iff_restrict (section5_grid_box_measurable n M)).mpr
  rw [← section5_window_pi]
  apply (memLp_two_iff_integrable_sq_norm
    (hF.comp (section5_round_coordinates_measurable n M)).aestronglyMeasurable).mpr
  have hh := section5_finite_grid_integrable n M (-gridRadius M) (gridSpacing M)
    (section5_gridSpacing_positive M hM) (fun x => ‖F x‖^2) (hF.norm.pow_const 2)
  simp only [← section5_roundCoord_grid_sample,section5_grid_window_eq] at hh
  exact hh





end


