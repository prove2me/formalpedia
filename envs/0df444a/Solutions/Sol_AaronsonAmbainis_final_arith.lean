-- Prove2me | solution 1 for AaronsonAmbainis.final_arith
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:36:15.95253+00:00
-- url     : https://prove2.me/submissions/e8df5160-582c-4411-9606-8279338d43ab

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_TwoSided_RemoveWeights

set_option autoImplicit true
open AaronsonAmbainis
open Finset
namespace AaronsonAmbainis
theorem _root_.solution {VO VN T τ : ℝ} (hT : 0 < T) (h : VO * VN ≤ T * T * τ / 4) :
    4 * (VO / T) * (VN / T) ≤ τ := by
  have h1 : 4 * (VO / T) * (VN / T) = 4 * (VO * VN) / (T * T) := by ring
  rw [h1, div_le_iff₀ (mul_pos hT hT)]
  linarith
end AaronsonAmbainis
