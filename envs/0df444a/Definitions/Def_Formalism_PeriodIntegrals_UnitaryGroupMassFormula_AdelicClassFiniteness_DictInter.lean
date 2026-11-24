-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictInter
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:32.838808+00:00
-- url     : https://prove2.me/theorems/18a748ce-c268-473e-baaa-592b840947c1
-- title:
--   Dict Inter
-- statement:
--   Definitions and structural lemmas for Dict Inter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicClassFiniteness/DictInter.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
namespace DictInter
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def tau (w : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ
    TensorProduct.map ((Algebra.trace F E) ∘ₗ LinearMap.mulLeft F w) LinearMap.id
variable (F E) in

def dualSet : Set E := {w | ∀ a : 𝓞 E, Algebra.trace F E (w * (a : E)) ∈ (algebraMap (𝓞 F) F).range}
def tSet (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Set (E ⊗[F] Af F) :=
  {r | ∀ w ∈ dualSet F E, tau w r ∈ Formalism.UG.intAd F}
end DictInter
end PIW.AdelClassFin


