-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_CubeThree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:42.369965+00:00
-- url     : https://prove2.me/theorems/381b5292-1c7b-44ff-bda7-80bd899f1527
-- title:
--   Cube Three
-- statement:
--   Definitions and structural lemmas for Cube Three, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CubeThree.lean

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
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
noncomputable section
namespace Formalism.ELL
namespace CubeThreeAlt
open WeierstrassChordSeries
section Alg
variable {R : Type*} [CommRing R]
def Hv (a1 a2 a3 a4 a6 z v v' : R) : R :=
  a1 * z + a2 * z ^ 2 + a3 * (v + v') + a4 * z * (v + v') + a6 * (v ^ 2 + v * v' + v' ^ 2) - 1
end Alg
section Mser
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
abbrev TT (W : WeierstrassCurve K) (σ : Type) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map (algebraMap (Sadj W) K)).range
variable {W : WeierstrassCurve K} {σ : Type}
def GG (W : WeierstrassCurve K) (z v : MvPowerSeries σ K) : MvPowerSeries σ K :=
  G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄)
    (MvPowerSeries.C W.a₆) z v
def chordCoeffCubicAt (W : WeierstrassCurve K) (l : MvPowerSeries σ K) : MvPowerSeries σ K :=
  c3 (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) l
def chordCoeffQuadraticAt (W : WeierstrassCurve K) (l n : MvPowerSeries σ K) : MvPowerSeries σ K :=
  c2 (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄)
    (MvPowerSeries.C W.a₆) l n
def DDs (W : WeierstrassCurve K) (l n z : MvPowerSeries σ K) : MvPowerSeries σ K :=
  -1 + MvPowerSeries.C W.a₁ * z + MvPowerSeries.C W.a₃ * (l * z + n)
def HHs (W : WeierstrassCurve K) (z v v' : MvPowerSeries σ K) : MvPowerSeries σ K :=
  Hv (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃) (MvPowerSeries.C W.a₄)
    (MvPowerSeries.C W.a₆) z v v'
variable {w : PowerSeries K}
end Mser
end CubeThreeAlt
end Formalism.ELL
namespace Formalism.ELL
open CubeThreeAlt WeierstrassChordSeries
end Formalism.ELL


