-- Prove2me | solution 1 for Autoconvolutions.Estimate.lower_le_block_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:30.816789+00:00
-- url     : https://prove2.me/submissions/1f3f0004-028d-4a11-8833-864e7fe1e07e

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
public import Definitions.Def_Autoconvolutions_Estimate
public import Theorems.Thm_Autoconvolutions_Estimate_height_pos
public import Theorems.Thm_Autoconvolutions_Estimate_norm_ratio_lower

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Estimate
namespace Autoconvolutions.Estimate
theorem _root_.solution {r b n K : ℕ} (hn : 0 < n) (hK : K ≤ n)
    (hb : 8*n^3 ≤ b) (hbr : b ≤ r) {eval : ℝ}
    (heval : eval = ((r:ℝ)*b)^n * ∑ s ∈ range (K+1), ((b:ℝ)/r)^s) :
    (1-1/(n:ℝ)) * Parameters.factorialRatio (2*n) (2*K) *
      Parameters.geomRatio ((b:ℝ)/r) K ≤
      (∑ s ∈ range (K+1), (s:ℝ)*count n r b s*(height n s)^2) /
        (eval^2 * height n (2*K)) := by
  exact norm_ratio_lower hn hK hb hbr (congrArg (· ^ 2) heval) (height_pos n (2*K))
    le_rfl le_rfl
end Autoconvolutions.Estimate
