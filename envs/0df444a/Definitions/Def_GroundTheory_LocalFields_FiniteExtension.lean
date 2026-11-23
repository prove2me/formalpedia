-- Prove2me | Definitions.Def_GroundTheory_LocalFields_FiniteExtension
-- name    : GroundTheory_LocalFields_FiniteExtension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:53.002797+00:00
-- url     : https://prove2.me/theorems/0cc893d7-3dd3-40b4-bda7-5117481058b2
-- title:
--   Finite Extension
-- statement:
--   Definitions and structural lemmas for Finite Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel
section Base
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
@[instance_reducible]
def normedField : NontriviallyNormedField K :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
theorem normedField_norm_le_norm_iff (x y : K) :
    letI := normedField K
    ‖x‖ ≤ ‖y‖ ↔ x ≤ᵥ y := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  let : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  rw [(valuation K).vle_iff_le]
  exact Valued.toNormedField.norm_le_iff
theorem normedField_isUltrametricDist :
    letI := normedField K
    IsUltrametricDist K := by
  let := normedField K
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  rcases vle_add_cases x y with h | h
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_left _ _)
  · exact ((normedField_norm_le_norm_iff K _ _).2 h).trans (le_max_right _ _)
theorem normedField_completeSpace :
    letI := normedField K
    CompleteSpace K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  exact (inferInstance : CompleteSpace K)
end Base
section Extension
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
@[instance_reducible]
def spectralNormedField : NontriviallyNormedField L :=
  letI := normedField K
  haveI := normedField_isUltrametricDist K
  haveI := normedField_completeSpace K
  spectralNorm.nontriviallyNormedField K L
theorem spectralNormedField_isUltrametricDist :
    letI := spectralNormedField K L
    IsUltrametricDist L := by
  let := normedField K
  have := normedField_isUltrametricDist K
  have := normedField_completeSpace K
  let := spectralNormedField K L
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (isNonarchimedean_spectralNorm (K := K) (L := L))
structure LocalFieldStructure (L : Type*) [Field L] where

  rel : ValuativeRel L

  top : TopologicalSpace L
@[instance_reducible]
def finiteExtensionStructure : LocalFieldStructure L :=
  letI := spectralNormedField K L
  haveI := spectralNormedField_isUltrametricDist K L
  { rel := ValuativeRel.ofValuation (NormedField.valuation (K := L))
    top := inferInstance }
end Extension
end GroundTheory.LocalField


