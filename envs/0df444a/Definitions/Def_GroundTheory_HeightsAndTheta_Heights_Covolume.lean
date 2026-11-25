-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
-- name    : GroundTheory_HeightsAndTheta_Heights_Covolume
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:57:39.306886+00:00
-- url     : https://prove2.me/theorems/bfc6203f-160d-4e68-8a9c-c6e82dc6f0d2
-- title:
--   Covolume
-- statement:
--   Definitions and structural lemmas for Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Covolume.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RealSpace_ofModule_injective_8cc11d3e2f7f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module
open scoped Kronecker
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
section Real
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)
namespace RealSpace
instance instMeasurableSpace : MeasurableSpace (RealSpace h) := borel _
instance instBorelSpace : BorelSpace (RealSpace h) := ⟨rfl⟩
end RealSpace
def arithEuler : ℝ := -Real.log (ZLattice.covolume (RealSpace.lattice h))
end Real
section Gram
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
def towerVec (s : ι → E) (p : ι × (K →+* ℂ)) : RealSpace h :=
  RealSpace.ofModule h (RingOfIntegers.basis K (equivReindex K p.2) • s p.1)
end Gram
section RiemannRoch
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {s : ι → E}
def towerBasis (hs : LinearIndependent (𝓞 K) s) :
    Basis (ι × (K →+* ℂ)) ℤ (Submodule.span (𝓞 K) (Set.range s)) :=
  ((RingOfIntegers.basis K).smulTower' (Basis.span hs)).reindex
    (Equiv.prodCongr (Equiv.refl ι) (equivReindex K).symm)
def spanToReal (s : ι → E) : Submodule.span (𝓞 K) (Set.range s) →ₗ[ℤ] RealSpace h :=
  (RealSpace.ofModule h).toIntLinearMap ∘ₗ
    ((Submodule.span (𝓞 K) (Set.range s)).subtype.restrictScalars ℤ)
omit [Fintype ι] [DecidableEq ι] in
theorem spanToReal_injective (s : ι → E) : Function.Injective (spanToReal h s) :=
  (RealSpace.ofModule_injective h).comp Subtype.val_injective
def spanLattice (s : ι → E) : Submodule ℤ (RealSpace h) := LinearMap.range (spanToReal h s)
omit [Fintype ι] [DecidableEq ι] in
theorem spanLattice_le (s : ι → E) : spanLattice h s ≤ RealSpace.lattice h := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, rfl⟩
instance (s : ι → E) : DiscreteTopology (spanLattice h s) := by
  have : DiscreteTopology (RealSpace.lattice h : Set (RealSpace h)) :=
    (inferInstance : DiscreteTopology (RealSpace.lattice h))
  exact DiscreteTopology.of_subset this (spanLattice_le h s)
def spanLatticeBasis (hs : LinearIndependent (𝓞 K) s) :
    Basis (ι × (K →+* ℂ)) ℤ (spanLattice h s) :=
  (towerBasis hs).map (AddEquiv.ofBijective (spanToReal h s).rangeRestrict.toAddMonoidHom
    ⟨fun _ _ hxy ↦ spanToReal_injective h s (congrArg Subtype.val hxy),
      LinearMap.surjective_rangeRestrict _⟩).toIntLinearEquiv
end RiemannRoch
def HermitianBundle.arithEuler (A : HermitianBundle K) : ℝ := Heights.arithEuler A.metric
namespace HermitianExtension
variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')
end HermitianExtension
end
end GroundTheory.Heights₂.Heights


