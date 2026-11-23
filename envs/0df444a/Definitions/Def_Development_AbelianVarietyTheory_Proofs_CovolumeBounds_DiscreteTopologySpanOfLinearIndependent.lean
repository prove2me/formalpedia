-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:11.991083+00:00
-- url     : https://prove2.me/theorems/24ac3803-ad57-4800-af49-0fdf3237950e
-- title:
--   Discrete Topology Span Of Linear Independent
-- statement:
--   Definitions and structural lemmas for Discrete Topology Span Of Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
namespace GlobalTheory
section Gram
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
end Gram
section Def
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem free_of_fg {V : Type*} [AddCommGroup V] [Module ℝ V] {L : Submodule ℤ V} (h : L.FG) :
    Module.Free ℤ L := by
  have : Module.Finite ℤ L := .of_fg h
  have : IsAddTorsionFree V := .of_isTorsionFree ℝ V
  infer_instance
open Classical in

noncomputable def spanCovol (L : Submodule ℤ E) : ℝ :=
  if h : L.FG then
    haveI : Module.Finite ℤ L := .of_fg h
    haveI : Module.Free ℤ L := free_of_fg h
    √(gram ℝ fun i => (finBasis ℤ L i : E)).det
  else 0
end Def
section Discrete
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
end Discrete
section Main
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
instance discreteTopology_comap_subtype (L : Submodule ℤ E) [DiscreteTopology L]
    (S : Submodule ℝ E) : DiscreteTopology (ZLattice.comap ℝ L S.subtype) :=
  ZLattice.comap_discreteTopology ℝ L continuous_subtype_val S.injective_subtype
instance isZLattice_comap_subtype_span (L : Submodule ℤ E) [DiscreteTopology L] :
    IsZLattice ℝ (ZLattice.comap ℝ L (span ℝ (L : Set E)).subtype) :=
  ⟨span_span_coe_preimage⟩
noncomputable def projAlong (L N : Submodule ℤ E) : Submodule ℤ E :=
  L.map ((span ℝ (N : Set E))ᗮ.starProjection.toLinearMap.restrictScalars ℤ)
end Main
end GlobalTheory


