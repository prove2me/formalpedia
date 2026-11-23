-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupConstCoeffZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:32.063811+00:00
-- url     : https://prove2.me/theorems/9e522331-0f03-4e39-9892-0544b872a5bf
-- title:
--   Formal Group Const Coeff Zero
-- statement:
--   Definitions and structural lemmas for Formal Group Const Coeff Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupConstCoeffZero.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
namespace CubeR
open Univ CurveSer
local notation "cc" => MvPowerSeries.constantCoeff
section Tools
variable {σ : Type*} {A : Type u} {B : Type v} [CommRing A] [CommRing B]
end Tools
section Two
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)
def lhs2 : MvPowerSeries (Fin 2) A :=
  U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) A)
    - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) A)
def diff2 : MvPowerSeries (Fin 2) A :=
  MvPowerSeries.subst
    (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) A)] : Fin 2 → MvPowerSeries (Fin 2) A) (fgl W)
end Two
section Three
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] (W : WeierstrassCurve A)
def lhs3 : MvPowerSeries (Fin 3) A :=
  (Matrix.of fun i : Fin 3 =>
    ![(MvPowerSeries.X i : MvPowerSeries (Fin 3) A) ^ 3,
      MvPowerSeries.X i * (xS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) A),
      (yS W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) A)]).det
def sum3 : MvPowerSeries (Fin 3) A :=
  MvPowerSeries.subst
    (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 3) A) (fgl W), MvPowerSeries.X 2] :
      Fin 2 → MvPowerSeries (Fin 3) A) (fgl W)
end Three
end CubeR
open CubeR Univ
end Formalism.L2.Th1.A


