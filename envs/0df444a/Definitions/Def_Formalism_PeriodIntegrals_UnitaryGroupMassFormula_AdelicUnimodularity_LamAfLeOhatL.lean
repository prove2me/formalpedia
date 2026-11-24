-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:02:12.566686+00:00
-- url     : https://prove2.me/theorems/28400f24-3ab0-4831-b54e-7e25b20fd044
-- title:
--   Lam Af Le Ohat L
-- statement:
--   Definitions and structural lemmas for Lam Af Le Ohat L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/LamAfLeOhatL.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WAU
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "Af" => FiniteAdeleRing (𝓞 F) F
def ohatL (L : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → E ⊗[F] Af) :=
  AddSubgroup.closure {y | ∃ c ∈ Ohat F, ∃ l ∈ L, y = ((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) Af (l i)}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end PI.WAU


