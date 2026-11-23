-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:07.567488+00:00
-- url     : https://prove2.me/theorems/85fc42df-1702-4012-92e3-9d307d5e6eda
-- title:
--   Det Adm A
-- statement:
--   Definitions and structural lemmas for Det Adm A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DetAdmA.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_NuInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoPolish
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isCompact_integers
import Theorems.Thm_ReciprocityTheory_GeneralLinearIntegers_GeneralLinearIntegersOpenCompact_isOpen_integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW.DeterminantAdmissible
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabSW.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct
section Borel
variable {F : Type} [Field F] [NumberField F]
instance borel_Ainf : BorelSpace (Ainf F) := ⟨rfl⟩
instance borel_Af : BorelSpace (Af F) := ⟨rfl⟩
instance borel_AF : BorelSpace (AF F) := ⟨rfl⟩
instance borel_Fv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩
instance borel_tens {E : Type} [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
end Borel
section Local
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
theorem isCompact_intV : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v
theorem isClopen_intV : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ⟨(isCompact_intV v).isClosed, ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v⟩
instance lc_Fv : LocallyCompactSpace (Fv F v) :=
  (isCompact_intV v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isClopen_intV v).isOpen.mem_nhds (zero_mem (v.adicCompletionIntegers F)))
end Local
section Box1
variable {F : Type} [Field F] [NumberField F]
end Box1
end PI.VolStabSW.DeterminantAdmissible


