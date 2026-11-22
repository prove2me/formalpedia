-- Prove2me | solution 1 for Autoconvolutions.Estimate.count_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:53:02.42179+00:00
-- url     : https://prove2.me/submissions/17140669-ccd7-44f9-9cd5-7bf60152d2a2

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
theorem _root_.solution (n r b s : ℕ) : 0 ≤ count n r b s := by
  unfold count
  positivity
end Autoconvolutions.Estimate
