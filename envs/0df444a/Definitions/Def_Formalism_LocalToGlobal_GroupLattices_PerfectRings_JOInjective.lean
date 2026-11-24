-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective
-- name    : Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:54.605694+00:00
-- url     : https://prove2.me/theorems/18ba0062-a1f0-488c-bf8c-ff92d0a3d4f7
-- title:
--   JOInjective
-- statement:
--   Definitions and structural lemmas for JOInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/JOInjective.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_L2_G_Quad_algebraMap_injective
import Theorems.Thm_Formalism_L2_G_jW_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.G
open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
abbrev QQ : Type := FractionRing (WQ p n)
abbrev OO : Type := QuadraticAlgebra (W2 p n) (p : W2 p n) 0
instance instDomOO : IsDomain (OO p n) := GatR.isDomain (WittVector.irreducible p)
instance instDvrOO : IsDiscreteValuationRing (OO p n) := GatR.isDVR (WittVector.irreducible p)
abbrev KO : Type := FractionRing (OO p n)
def wU : OO p n := ω
def jO : WQ p n →+* OO p n := (algebraMap (W2 p n) (OO p n)).comp (jW p n)
theorem jO_injective : Function.Injective (jO p n) :=
  (Quad.algebraMap_injective _).comp (jW_injective p n)
theorem inj_WK : Function.Injective ((algebraMap (OO p n) (KO p n)).comp (jO p n)) :=
  (IsFractionRing.injective (OO p n) (KO p n)).comp (jO_injective p n)
def iota : QQ p n →+* KO p n := IsFractionRing.lift (inj_WK p n)
end Formalism.L2.G


