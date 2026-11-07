-- Prove2me | Definitions.Def_HeilmanMax3Cut_Kst
-- name    : HeilmanMax3Cut_Kst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:21.045067+00:00
-- url     : https://prove2.me/theorems/da3c444b-1e17-4c44-8e05-56c16733f07c
-- title:
--   The corrected kernel $K_*=K_0+4B$
-- statement:
--   $$K_*(t,s)=K_0(t,s)+4B(t,s).$$
--
--   $K_*$ is the kernel of the integral operator in the quadratic expression (105) obtained by integrating Corollary 8.4 over the radii.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (104), p.31

import Mathlib
import Definitions.Def_HeilmanMax3Cut_K0
import Definitions.Def_HeilmanMax3Cut_Bk

namespace HeilmanMax3Cut

/-- **The corrected radial kernel `K_*`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (104), p.31: `K_*(t, s) := K₀(t, s) + 4B(t, s)`. -/
noncomputable def Kst (σ t s : ℝ) : ℝ :=
  K0 σ t s + 4 * Bk σ t s

end HeilmanMax3Cut


