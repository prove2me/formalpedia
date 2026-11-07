-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:52:54.983276+00:00
-- url     : https://prove2.me/theorems/b7c6ff55-4346-4484-adda-d91e3a2b8305
-- title:
--   Grid Cover
-- statement:
--   Definitions and structural lemmas for Grid Cover, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/GridCover.lean

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply


set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
abbrev GridCoordinate (K : ℕ) := ↥(Finset.Icc (-(K : ℤ)) (K : ℤ))
abbrev Grid (K : ℕ) := Fin 3 → GridCoordinate K
noncomputable def gridPoint (K : ℕ) (g : Grid K) : Space :=
  WithLp.toLp 2 (fun i => ((g i).val : ℝ))
theorem round_mem_grid (K : ℕ) (x : ℝ) (hx : |x| ≤ K) :
    round x ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
  have he := abs_sub_round x
  obtain ⟨hxlo,hxhi⟩ := abs_le.mp hx
  obtain ⟨helo,hehi⟩ := abs_le.mp he
  have hu : (round x : ℝ) < (K : ℝ)+1 := by linarith
  have hl : -(K : ℝ)-1 < (round x : ℝ) := by linarith
  have hu' : round x < (K : ℤ)+1 := by exact_mod_cast hu
  have hl' : -(K : ℤ)-1 < round x := by exact_mod_cast hl
  simp only [Finset.mem_Icc]
  omega
noncomputable def nearestGrid (K : ℕ) (p : Space) (hp : ‖p‖ ≤ K) : Grid K :=
  fun i => ⟨round (p i), round_mem_grid K (p i)
    (by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le p i).trans hp)⟩
end QEC.Coding.BDL26RandomPerturbation


