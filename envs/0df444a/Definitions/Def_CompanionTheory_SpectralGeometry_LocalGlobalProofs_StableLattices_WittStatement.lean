-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:19.210801+00:00
-- url     : https://prove2.me/theorems/31f98179-72e9-4a63-8b07-0307911715b1
-- title:
--   Witt Statement
-- statement:
--   Definitions and structural lemmas for Witt Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WittStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB
namespace GlobalTheory.CompanionTheory.FlWitt
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}
def pairMap (e f : Fin l → V) : ((Fin l → L) × (Fin l → L)) →ₗ[L] V where
  toFun p := ∑ i, p.1 i • e i + ∑ i, p.2 i • f i
  map_add' p r := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c p := by
    simp [mul_smul, Finset.smul_sum, smul_add]
end GlobalTheory.CompanionTheory.FlWitt
end


