-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:40.915106+00:00
-- url     : https://prove2.me/theorems/f42f48fa-3810-4b45-89fe-ad365575bbc5
-- title:
--   Formal Group Eq WSeries
-- statement:
--   Definitions and structural lemmas for Formal Group Eq WSeries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/WeierstrassSubstitution/FormalGroupEqWSeries.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
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
namespace Univ
abbrev Z : Type := MvPolynomial (Fin 5) ℤ
def W₀ : WeierstrassCurve Z :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩
def φ_of {R : Type u} [CommRing R] (W : WeierstrassCurve R) : Z →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
abbrev K₀ : Type := FractionRing Z
def ι : Z →+* K₀ := algebraMap Z K₀
instance charZero_K₀ : CharZero K₀ := charZero_of_injective_algebraMap (IsFractionRing.injective Z K₀)
def WK : WeierstrassCurve K₀ := W₀.map ι
end Univ
namespace Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
section Tools
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
end Tools
section W
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
end W
section Map
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)
end Map
section Coeffs
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
abbrev Wi (i : Fin 2) : MvPowerSeries (Fin 2) R :=
  (wSer W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)
abbrev dd : MvPowerSeries (Fin 2) R :=
  -1 + MvPowerSeries.C W.a₁ * uThird W + MvPowerSeries.C W.a₃ * wThird W
end Coeffs
section Map2
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)
end Map2
section Third
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
end Third
section Field
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
end Field
end Fgl1
end Formalism.L2.Th1.A


