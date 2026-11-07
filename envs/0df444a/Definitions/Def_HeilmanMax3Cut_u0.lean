-- Prove2me | Definitions.Def_HeilmanMax3Cut_u0
-- name    : HeilmanMax3Cut_u0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:06.716207+00:00
-- url     : https://prove2.me/theorems/407e51a4-2ed9-45b0-b480-316f5a11ec98
-- title:
--   $u_0=K_01$
-- statement:
--   $$u_0(t)=\int_0^\infty K_0(t,s)\,d\nu(s).$$
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Lemma 9.2, Eq. (118), p.33

import Mathlib
import Definitions.Def_HeilmanMax3Cut_K0
import Definitions.Def_HeilmanMax3Cut_nuExp
open MeasureTheory

namespace HeilmanMax3Cut

/-- **`u₀ := K₀ 1`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Lemma 9.2, Eq. (118), p.33: `u₀(t) := ∫₀^∞ K₀(t, s) dν(s)`. -/
noncomputable def u0 (σ t : ℝ) : ℝ :=
  ∫ s, K0 σ t s ∂nuExp

end HeilmanMax3Cut


