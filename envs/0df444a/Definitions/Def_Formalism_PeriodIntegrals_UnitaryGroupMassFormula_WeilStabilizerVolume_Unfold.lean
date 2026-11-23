-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unfold
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unfold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:33:05.649376+00:00
-- url     : https://prove2.me/theorems/bab2c961-01e6-4212-a190-d8da89db168b
-- title:
--   Unfold
-- statement:
--   Definitions and structural lemmas for Unfold, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/Unfold.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_InvInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbsAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Theorems.Thm_Formalism_UG_P_bc_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Set
open scoped TensorProduct ENNReal Pointwise
section Inst
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
theorem inclR_comp_sigma :
    (inclR (F := F) (AF F) : E →+* AF F ⊗[F] E).comp (σ : E →+* E) = (sigR (AF F) σ).comp (inclR (F := F) (AF F)) := by
  ext e
  simp [inclR, sigR]
def ratEl (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HFinIn (AF F) σ J :=
  ⟨⟨Formalism.UG.bc (inclR (F := F) (AF F)) g, Formalism.UG.P.bc_mem _ _ _ (inclR_comp_sigma σ) J g hg⟩,
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨g, hg, rfl⟩)⟩
def GamA : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
def ratElA (g : GL (Fin M) E) (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : HA (AF F) σ J :=
  (ratEl σ J g hg : HR (AF F) σ J)
instance nontrivAF : Nontrivial (AF F) := by
  haveI : Nontrivial (Ainf F) := by
    first
    | exact inferInstance
    | (haveI : Nonempty (NumberField.InfinitePlace F) := inferInstance; exact Pi.nontrivial)
  first
  | exact inferInstance
  | exact inferInstanceAs (Nontrivial (Ainf F × Af F))
  | exact (Prod.nontrivial_left : Nontrivial (Ainf F × Af F))
end Inst
end PI.VolStabW


