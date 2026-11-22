-- Prove2me | solution 1 for Autoconvolutions.Construction.witness_ratio_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:15.394568+00:00
-- url     : https://prove2.me/submissions/b15b6c08-c93f-4ebb-acca-b02da4090816

module
public import Definitions.Def_Autoconvolutions_Witness
public import Definitions.Def_Autoconvolutions_Coefficients
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Definitions.Def_Autoconvolutions_Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Definitions.Def_Autoconvolutions_Main
public import Theorems.Thm_Autoconvolutions_Blocks_coeff_cap
public import Theorems.Thm_Autoconvolutions_Blocks_coeff_eq_good
public import Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
public import Theorems.Thm_Autoconvolutions_Blocks_peakCode_injOn
public import Theorems.Thm_Autoconvolutions_Blocks_peak_mem
public import Theorems.Thm_Autoconvolutions_Blocks_peak_rowKey
public import Theorems.Thm_Autoconvolutions_Blocks_peak_sum
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_eval_witness
public import Theorems.Thm_Autoconvolutions_Construction_eval_witness_pos
public import Theorems.Thm_Autoconvolutions_Construction_witness_nonneg
public import Theorems.Thm_Autoconvolutions_Estimate_height_pos
public import Theorems.Thm_Autoconvolutions_Estimate_lower_le_block_fraction
public import Theorems.Thm_Autoconvolutions_convCoeff_eq_poly_sq
public import Theorems.Thm_Autoconvolutions_convCoeff_of_neg
public import Theorems.Thm_Autoconvolutions_exists_pos_coeff_of_eval_pos
public import Theorems.Thm_Autoconvolutions_poly_sum_eq_eval_one
public import Theorems.Thm_Autoconvolutions_ratio_ge_blocks
attribute [local simp] Autoconvolutions.Blocks.eval_gen_one
attribute [local simp] Autoconvolutions.Blocks.peak_rowKey
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Filter Finset Polynomial
open scoped BigOperators Topology
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution {m n K D : ℕ} (I J : Finset (Fin m))
    (hd : Disjoint I J) (hK : K < n) (hD : 4*n < D)
    (hJ : 8*n^3 ≤ J.card) (hIJ : J.card ≤ I.card) :
    let F := witness D n K I J
    (1 - 1/(n:ℝ)) * Parameters.factorialRatio (2*n) (2*K) *
      Parameters.geomRatio ((J.card:ℝ) / I.card) K ≤
      ratio (step F.natDegree (Polynomial.toFn (F.natDegree+1) F)) := by
  classical
  let F := witness D n K I J
  let p := Polynomial.toFn (F.natDegree+1) F
  have hn : 0 < n := by omega
  have hj : 0 < J.card := lt_of_lt_of_le (by positivity) hJ
  have hi := hj.trans_le hIJ
  have hp (i : Fin (F.natDegree+1)) : 0 ≤ p i := witness_nonneg I J i.val
  have hne : ∃ i, 0 < p i := exists_pos_coeff_of_eval_pos F (eval_witness_pos I J hK.le hi hj)
  have cap (k : ℤ) : convCoeff F.natDegree p k ≤ Estimate.height n (2*K) := by
    by_cases hk : k < 0
    · rw [convCoeff_of_neg _ _ hk]
      exact (Estimate.height_pos _ _).le
    · lift k to ℕ using (by omega : 0 ≤ k)
      rw [show convCoeff F.natDegree p (k : ℤ) = (F^2).coeff k from convCoeff_eq_poly_sq F k]
      exact Blocks.coeff_cap I J hd hK hD k
  have hplateau (x : Blocks.Peak m) (hx : x ∈ Blocks.peakSet I J n K) (h : ℕ) (hh : h ≤ x.1) :
      convCoeff F.natDegree p ((D * Blocks.peakCode D x + h : ℕ) : ℤ) = Estimate.height n x.1 := by
    obtain ⟨hs,ha,hb⟩ := Blocks.peak_mem hx
    rw [show convCoeff F.natDegree p _ = (F^2).coeff _ from convCoeff_eq_poly_sq F _]
    simpa only [F, witness, Blocks.key, Blocks.peakCode, Nat.add_comm h] using
      Blocks.coeff_eq_good I J hd hK hD hs ha hb h hh
  have bound := ratio_ge_blocks F.natDegree p hp hne (Estimate.height n (2*K))
    (Estimate.height_pos _ _) cap D (Blocks.peakSet I J n K) (Blocks.peakCode D)
    Sigma.fst (fun x => Estimate.height n x.1)
    (Blocks.peakCode_injOn (by omega) hd hK.le hD)
    (fun x hx => by have hs := (Blocks.peak_mem hx).1; omega) hplateau
  rw [Blocks.peak_sum, show (∑ j, p j) = F.eval 1 from poly_sum_eq_eval_one F] at bound
  exact (Estimate.lower_le_block_fraction hn hK.le hJ hIJ (eval_witness I J hK.le hi)).trans bound
end Autoconvolutions.Construction
