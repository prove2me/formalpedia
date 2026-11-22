-- Prove2me | solution 1 for Autoconvolutions.Construction.eval_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:42.110046+00:00
-- url     : https://prove2.me/submissions/4d43e34c-3bbc-45a8-988c-a9fc97711638

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
public import Definitions.Def_Autoconvolutions_PolyStep
public import Definitions.Def_Autoconvolutions_Witness
public import Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_eval_family_one
public import Theorems.Thm_Autoconvolutions_Flat_P_eval_one
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
theorem _root_.solution {m n K D : ℕ} (I J : Finset (Fin m)) (hK : K ≤ n) (hI : 0 < I.card) :
    (witness D n K I J).eval 1 =
    ((I.card : ℝ) * J.card)^n * ∑ i ∈ range (K+1), ((J.card : ℝ)/I.card)^i := by
  unfold witness
  rw [eval_family_one _ _ _ hK Flat.P_eval_one (by simpa using hI.ne')]
  simp
end Autoconvolutions.Construction
