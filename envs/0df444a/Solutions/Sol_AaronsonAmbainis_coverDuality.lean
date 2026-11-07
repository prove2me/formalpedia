-- Prove2me | solution 1 for AaronsonAmbainis.coverDuality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:53:51.014756+00:00
-- url     : https://prove2.me/submissions/792be9c9-6c42-4972-8203-74ecaf76a718

import Definitions.Def_AaronsonAmbainis_Dual_Sets
import Definitions.Def_AaronsonAmbainis_Dual_Functional
import Definitions.Def_AaronsonAmbainis_Dual_Core
import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Theorems.Thm_AaronsonAmbainis_Dual_exists_cover

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution : CoverDuality :=
  fun _ _ _ t K _ _ hpack => Dual.exists_cover t K hpack
end AaronsonAmbainis
