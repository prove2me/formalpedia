-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:37.610121+00:00
-- url     : https://prove2.me/theorems/875aad93-9a0e-4f66-8980-193c0d19456f
-- title:
--   St Lam Of
-- statement:
--   Definitions and structural lemmas for St Lam Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnitaryOrbits/StLamOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
def QuadGen : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 →
    (∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) →
    ∃ (θ : E) (d : F), θ ^ 2 = algebraMap F E d ∧ σ θ = -θ ∧ d ≠ 0 ∧
      ∀ e : E, ∃ p q : F, e = algebraMap F E p + algebraMap F E q * θ
section Tensor
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
variable (R : Type) [CommRing R] [Algebra F R]
end Tensor
end PIW.AdelicOrbitU
namespace PIW.AdelicOrbitU
end PIW.AdelicOrbitU


