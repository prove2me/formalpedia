-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_Assemble
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:11:59.547635+00:00
-- url     : https://prove2.me/theorems/c4e0b89d-dc6c-41e3-a8e8-7c21210d95be
-- title:
--   Assemble
-- statement:
--   Definitions and structural lemmas for Assemble, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalPrimitiveFrame/Assemble.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct
section Assemble
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
def Assemble_bc (ψ : (Fin n → E) →ₗ[E] E) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v ⊗[F] E] Fv F v ⊗[F] E :=
  ∑ i, inclR (F := F) (Fv F v) (ψ fun j => if i = j then 1 else 0) • LinearMap.proj i
end Assemble
end PI.LocFramePrimWork


