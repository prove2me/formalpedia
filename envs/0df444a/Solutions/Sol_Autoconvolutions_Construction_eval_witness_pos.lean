-- Prove2me | solution 1 for Autoconvolutions.Construction.eval_witness_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:31.301581+00:00
-- url     : https://prove2.me/submissions/12e47453-c304-41b7-a5e4-8397a3f05ba4

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
public import Definitions.Def_Autoconvolutions_PolyStep
public import Definitions.Def_Autoconvolutions_Witness
public import Theorems.Thm_Autoconvolutions_Construction_eval_witness
public import Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
attribute [local simp] Autoconvolutions.Blocks.eval_gen_one
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Finset Polynomial
open scoped BigOperators
open Autoconvolutions Autoconvolutions.Construction
namespace Autoconvolutions.Construction
theorem _root_.solution {m n K D : ℕ} (I J : Finset (Fin m))
    (hK : K ≤ n) (hI : 0 < I.card) (hJ : 0 < J.card) : 0 < (witness D n K I J).eval 1 := by
  rw [eval_witness I J hK hI]
  apply mul_pos (by positivity)
  have hq : 0 ≤ (J.card : ℝ) / I.card := by positivity
  exact lt_of_lt_of_le (by positivity) (single_le_sum (f := fun i : ℕ => ((J.card : ℝ)/I.card)^i)
    (fun i _ => pow_nonneg hq i) (a := 0) (by simp))
end Autoconvolutions.Construction
