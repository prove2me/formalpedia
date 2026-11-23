-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:23.361809+00:00
-- url     : https://prove2.me/theorems/4de6c68a-3f8c-4cdb-ab05-49a6d4c0f2c2
-- title:
--   Comp Exp
-- statement:
--   Definitions and structural lemmas for Comp Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CompExp.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsUltrametricDist
universe u
namespace Formalism.ELL.MultiplicativeWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)
def W (w : ℤ) (f : MvPowerSeries σ K) : Prop :=
  ∀ e : σ →₀ ℕ, ‖MvPowerSeries.coeff e f‖ ≤ c ^ (w - (e.degree : ℤ))
variable {c}
end Formalism.ELL.MultiplicativeWeight
namespace Formalism.ELL
end Formalism.ELL


