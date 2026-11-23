-- Prove2me | Definitions.Def_ImportCompatibility_Normability
-- name    : ImportCompatibility_Normability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:47:48.468155+00:00
-- url     : https://prove2.me/theorems/55852162-c427-4d76-a1e6-24fb8694415c
-- title:
--   Normability
-- statement:
--   Definitions and structural lemmas for Normability, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
set_option autoImplicit true
open Topology
section NormabilityBackport
variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable (𝕜 E) in
class IsNormableSpace [topology : TopologicalSpace E] where
  withSeminorms' : ∃ (p : Seminorm 𝕜 E), WithSeminorms (fun (_ : Unit) ↦ p)
end NormabilityBackport
instance {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] : IsNormableSpace 𝕜 E :=
  ⟨⟨normSeminorm 𝕜 E, by
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf, iInf_const,
      coe_normSeminorm, comap_norm_nhds_zero]⟩⟩
section NormabilityBackport
variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [t : TopologicalSpace E] [hn : IsNormableSpace 𝕜 E]
variable (𝕜 E)
noncomputable def IsNormableSpace.seminorm : Seminorm 𝕜 E := hn.withSeminorms'.choose
lemma IsNormableSpace.withSeminorms_seminorm : WithSeminorms (fun (_ : Unit) ↦ hn.seminorm 𝕜 E) :=
  hn.withSeminorms'.choose_spec
noncomputable abbrev IsNormableSpace.toSeminormedAddCommGroup : SeminormedAddCommGroup E := by
  let : Norm E := ⟨IsNormableSpace.seminorm 𝕜 E⟩
  let c : SeminormedSpace.Core 𝕜 E :=
  { norm_nonneg x := apply_nonneg _ x
    norm_smul c x := map_smul_eq_mul _ c x
    norm_triangle x y := map_add_le_add _ x y }
  refine SeminormedAddCommGroup.ofCoreReplaceTopology c ?_
  have ht := hn.withSeminorms_seminorm (𝕜 := 𝕜) (E := E)
  letI := ht.topologicalAddGroup
  rw [(SeminormFamily.withSeminorms_iff_topologicalSpace_eq_iInf _).mp ht, ciInf_unique]
noncomputable abbrev IsNormableSpace.toNormedSpace :
    letI : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup 𝕜 E
    NormedSpace 𝕜 E :=
  letI : SeminormedAddCommGroup E := IsNormableSpace.toSeminormedAddCommGroup 𝕜 E
  { norm_smul_le c x := (map_smul_eq_mul (IsNormableSpace.seminorm 𝕜 E) c x).le }
end NormabilityBackport
section Transport
variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
end Transport
section FiniteDimensionalBackport
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]
end FiniteDimensionalBackport


