-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
-- name    : Formalism_EllipticTorsion_CompExpWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:36.920818+00:00
-- url     : https://prove2.me/theorems/f678a5a3-f349-4cad-89d4-56a8c2af1d77
-- title:
--   Comp Exp Weight
-- statement:
--   Definitions and structural lemmas for Comp Exp Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/CompExpWeight.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
namespace Formalism.ELL
open Formalism.G
def CompExpWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (σ : Type) [Finite σ] (c : ℝ),
    0 < c → c ≤ 1 →
    ∀ E : PowerSeries K, constantCoeff E = 0 →
      (∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) →
    ∀ G : MvPowerSeries σ K, IntegralMv G → ∀ α : σ →₀ ℕ,
      ‖MvPowerSeries.coeff α
          (MvPowerSeries.subst (fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) G)‖
        ≤ c ^ (-(α.degree : ℤ))
end Formalism.ELL


