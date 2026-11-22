-- Prove2me | solution 1 for Autoconvolutions.Construction.witness_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:30.343925+00:00
-- url     : https://prove2.me/submissions/25ed7b51-eba8-47b8-b565-8ae696e2ef67

module
public import Definitions.Def_Autoconvolutions_BlockExpansion
public import Definitions.Def_Autoconvolutions_Estimate
public import Definitions.Def_Autoconvolutions_Flat
public import Definitions.Def_Autoconvolutions_PolyStep
public import Definitions.Def_Autoconvolutions_Witness
public import Theorems.Thm_Autoconvolutions_Blocks_eval_gen_one
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_family_nonneg_coeff
public import Theorems.Thm_Autoconvolutions_Flat_P_coeff_nonneg
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
theorem _root_.solution {m n K D : ℕ} (I J : Finset (Fin m)) (k : ℕ) :
    0 ≤ (witness D n K I J).coeff k := by
  have gen_pos (S : Finset (Fin m)) (j : ℕ) : 0 ≤ (Blocks.gen D S).coeff j := by
    simp only [Blocks.gen, finsetSum_coeff, coeff_X_pow]
    apply sum_nonneg
    intro i _
    split <;> simp
  exact family_nonneg_coeff Flat.P Flat.P_coeff_nonneg (gen_pos I) (gen_pos J) n K k
end Autoconvolutions.Construction
