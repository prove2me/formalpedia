-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_SecondCountableTopologyAndT2Space
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaussianDualMeasure_SecondCountableTopologyAndT2Space
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:33.028132+00:00
-- url     : https://prove2.me/theorems/82b74d92-cf52-4573-ad52-209265d9731b
-- title:
--   Second Countable Topology And T2 Space
-- statement:
--   Definitions and structural lemmas for Second Countable Topology And T2 Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaussianDualMeasure/SecondCountableTopologyAndT2Space.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory
noncomputable section
namespace PI.GI
section Top
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
theorem secondCountableTopology_and_t2Space : SecondCountableTopology F ∧ T2Space F :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  letI : (Valued.v (R := F)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := F).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  ⟨inferInstance, inferInstance⟩
instance secondCountable : SecondCountableTopology F := (secondCountableTopology_and_t2Space F).1
instance t2Space : T2Space F := (secondCountableTopology_and_t2Space F).2
end Top
section Meas
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
example (d : ℕ) : BorelSpace (Fin d → F) := inferInstance
end Meas
section Char
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
end Char
end PI.GI


