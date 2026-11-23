-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:14:36.054898+00:00
-- url     : https://prove2.me/theorems/2fe7b383-8f9f-4105-a1e4-d712f33817a8
-- title:
--   Mod Vec
-- statement:
--   Definitions and structural lemmas for Mod Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/ModVec.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
variable (D : Dat A n r)
def L (w : Fin r → n → A) (s : Fin r → Fin r → A) : (n → A) →ₗ[A] (n → A) :=
  LinearMap.id + ∑ b, (D.hL (D.e b)).smulRight (w b + ∑ a, s a b • D.e a) -
    ∑ a, ((D.hL (w a)).comp D.pW).smulRight (D.e a)
def PerpX (S : (n → A) →ₗ[A] (n → A)) : Prop :=
  ∀ v, (∀ a, D.h (D.e a) v = 0) → S v - v ∈ Submodule.span A (Set.range D.e)
variable {D}
end Dat
end PI.VolSemiDirect.W.PG


