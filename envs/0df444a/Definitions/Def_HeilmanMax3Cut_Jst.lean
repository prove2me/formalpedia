-- Prove2me | Definitions.Def_HeilmanMax3Cut_Jst
-- name    : HeilmanMax3Cut_Jst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:42.093047+00:00
-- url     : https://prove2.me/theorems/05b86630-c410-43ee-a3f0-6a508b82eec5
-- title:
--   The corrected multiplier $J_*=J_0+B^{(1)}$
-- statement:
--   $$J_*(t)=J_0(t)+B^{(1)}(t);$$
--
--   $M_{J_*}$ denotes multiplication by $J_*$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (104), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_J0
import Definitions.Def_HeilmanMax3Cut_B1

namespace HeilmanMax3Cut

/-- **The corrected multiplier `J_*`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (104), p.31: `J_*(t) := J₀(t) + B^{(1)}(t)`;
`M_{J_*}` denotes multiplication by `J_*`. -/
noncomputable def Jst (σ t : ℝ) : ℝ :=
  J0 σ t + B1 σ t

end HeilmanMax3Cut


