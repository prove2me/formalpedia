-- Prove2me | solution 1 for Autoconvolutions.Estimate.mass_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:54:58.697636+00:00
-- url     : https://prove2.me/submissions/62843662-b396-4a37-8b28-901ac1c480e4

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
public import Definitions.Def_Autoconvolutions_Estimate
public import Theorems.Thm_Autoconvolutions_Construction_card_evenAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_card_oddAlphabet
public import Theorems.Thm_Autoconvolutions_Construction_weight_eq
public import Theorems.Thm_Autoconvolutions_Digits_good_mass
attribute [local simp] Autoconvolutions.Construction.card_evenAlphabet
attribute [local simp] Autoconvolutions.Construction.card_oddAlphabet



set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Estimate
namespace Autoconvolutions.Estimate
theorem _root_.solution {r b n s : ℕ} (hn : 0 < n) (hb : 8*n^3 ≤ b) (hbr : b ≤ r)
    (hs : s ≤ 2*n) :
    (1-1/(n:ℝ)) * ((r:ℝ)*b)^(2*n) * ((b:ℝ)/r)^s ≤ count n r b s * height n s := by
  have hr : 0 < r := lt_of_lt_of_le (by positivity : 0 < 8*n^3) (hb.trans hbr)
  have h := Digits.good_mass (u := 2*n-s) (v := 2*n+s) hn hb hbr (by omega)
  rw [Construction.weight_eq (r:ℝ) (b:ℝ) (by positivity) hs] at h
  simpa only [count, height, mul_assoc] using h
end Autoconvolutions.Estimate
