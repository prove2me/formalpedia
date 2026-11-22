-- Prove2me | solution 1 for Autoconvolutions.Estimate.height_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:03.145607+00:00
-- url     : https://prove2.me/submissions/40a2426e-76ab-40a4-a9cd-8fbcbd8fa67b

module
public import Definitions.Def_Autoconvolutions_Definitions
public import Definitions.Def_Autoconvolutions_Parameters
public import Definitions.Def_Autoconvolutions_Digits
public import Definitions.Def_Autoconvolutions_Levels
public import Definitions.Def_Autoconvolutions_Estimate

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Autoconvolutions Autoconvolutions.Estimate
namespace Autoconvolutions.Estimate
theorem _root_.solution (n s : ℕ) : 0 < height n s := by
  unfold height
  positivity
end Autoconvolutions.Estimate
