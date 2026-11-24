-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:33:55.824652+00:00
-- url     : https://prove2.me/theorems/664e9b7e-9f7e-43d3-9b02-6772c047b070
-- title:
--   Split Iso
-- statement:
--   Definitions and structural lemmas for Split Iso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicIndexEquality/SplitIso.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
open scoped TensorProduct
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
def sigT (σ : E →ₐ[F] E) : K ⊗[F] E →ₐ[F] K ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id F K) σ
variable (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0)
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
end


