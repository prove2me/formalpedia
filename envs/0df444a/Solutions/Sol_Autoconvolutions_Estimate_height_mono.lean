-- Prove2me | solution 1 for Autoconvolutions.Estimate.height_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:20.492795+00:00
-- url     : https://prove2.me/submissions/e6f13c28-cc88-4d88-889d-bdcb56fdb9a2

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
public import Definitions.Def_Autoconvolutions_Estimate
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Estimate
namespace Autoconvolutions.Estimate
theorem _root_.solution {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ 2*n) :
    height n i ≤ height n j := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    refine (ih (by omega)).trans ?_
    have hsub : 2*n-j = (2*n-(j+1))+1 := by omega
    have hadd : 2*n+(j+1) = (2*n+j)+1 := by omega
    have hcmp : ((2*n-(j+1)+1 : ℕ) : ℝ) ≤ ((2*n+j+1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2*n-(j+1)+1 ≤ 2*n+j+1)
    unfold height
    rw [hsub, hadd, Nat.factorial_succ, Nat.factorial_succ]
    push_cast at hcmp ⊢
    calc
      _ = ((2*n-(j+1) : ℕ) + 1 : ℝ) * (((2*n-(j+1)).factorial : ℝ) *
          ((2*n+j).factorial : ℝ)) := by ring
      _ ≤ ((2*n+j : ℕ) + 1 : ℝ) * (((2*n-(j+1)).factorial : ℝ) *
          ((2*n+j).factorial : ℝ)) := mul_le_mul_of_nonneg_right (by simpa using hcmp) (by positivity)
      _ = _ := by push_cast; ring
end Autoconvolutions.Estimate
