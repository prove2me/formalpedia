-- Prove2me | solution 1 for Autoconvolutions.Parameters.tendsto_factorialRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:32.010689+00:00
-- url     : https://prove2.me/submissions/2de18179-0fb2-4df5-b872-9a0838552809

module
public import Definitions.Def_Autoconvolutions_Witness
public import Definitions.Def_Autoconvolutions_Coefficients
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Definitions.Def_Autoconvolutions_Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Definitions.Def_Autoconvolutions_Main
public import Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
public import Theorems.Thm_Autoconvolutions_Blocks_peak_rowKey
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
public import Theorems.Thm_Autoconvolutions_Estimate_height_mono
public import Theorems.Thm_Autoconvolutions_Estimate_height_pos
public import Theorems.Thm_Autoconvolutions_Parameters_factorialRatio_lower
attribute [local simp] Autoconvolutions.Blocks.eval_gen_one
attribute [local simp] Autoconvolutions.Blocks.peak_rowKey
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Filter Finset Polynomial
open scoped BigOperators Topology
open Autoconvolutions Autoconvolutions.Parameters
namespace Autoconvolutions.Parameters
theorem _root_.solution (K : ℕ) :
    Tendsto (fun n : ℕ => factorialRatio (2*n) (2*K)) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n : ℕ => 1 - ((2*(K:ℝ))^2/2) / n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((2*(K:ℝ))^2/2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (K+1)] with n hn
    have h := factorialRatio_lower (N := 2*n) (j := 2*K) (by omega) (by omega)
    simpa [Nat.cast_mul, div_div] using h
  · filter_upwards [eventually_ge_atTop K] with n hn
    have h := Estimate.height_mono (n := n) (i := 0) (j := 2*K) (Nat.zero_le _) (by omega)
    have hrat : factorialRatio (2*n) (2*K) = Estimate.height n 0 / Estimate.height n (2*K) := by
      simp [factorialRatio, Estimate.height, pow_two]
    rw [hrat]
    exact (div_le_one (Estimate.height_pos n (2*K))).2 h
end Autoconvolutions.Parameters
