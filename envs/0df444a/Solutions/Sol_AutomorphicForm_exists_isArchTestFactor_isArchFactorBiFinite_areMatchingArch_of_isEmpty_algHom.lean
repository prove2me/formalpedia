-- Prove2me | solution 1 for AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/95e74002-4f7d-5b1e-ad7f-04b77b26cc93

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Analysis.Normed.Group.Bounded
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom

set_option autoImplicit false

section OddDegreeEmbeddings

open NumberField
open scoped NumberField.LiesOver

namespace InfinitePlaceEmbedding

section NoNumberFieldNeeded

variable (K L : Type) [Field K] [Field L] [Algebra K L]

private noncomputable def placeHom (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w ∈ InfinitePlace.unramifiedPlacesOver L v) : L →ₐ[K] v.Completion :=
  haveI : w.1.LiesOver v.1 := (Set.mem_setOf.1 hw).1
  have h1 : Module.finrank v.Completion w.Completion = 1 :=
    InfinitePlace.Completion.finrank_eq_one_of_isUnramified v (Set.mem_setOf.1 hw).2
  have hb : Function.Bijective (algebraMap v.Completion w.Completion) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1
  let e : v.Completion ≃+* w.Completion := RingEquiv.ofBijective (algebraMap v.Completion w.Completion) hb
  { toRingHom := (e.symm : w.Completion →+* v.Completion).comp (algebraMap L w.Completion)
    commutes' := fun c => by
      apply e.injective
      change e (e.symm (algebraMap L w.Completion (algebraMap K L c))) = e (algebraMap K v.Completion c)
      rw [RingEquiv.apply_symm_apply]
      change algebraMap L w.Completion (algebraMap K L c)
        = algebraMap v.Completion w.Completion (algebraMap K v.Completion c)
      rw [← IsScalarTower.algebraMap_apply K L w.Completion,
        ← IsScalarTower.algebraMap_apply K v.Completion w.Completion] }

private theorem nonempty_algHom_of_forall_nonempty_unramifiedPlacesOver
    (h : ∀ v : InfinitePlace K, (InfinitePlace.unramifiedPlacesOver L v).Nonempty) :
    Nonempty (L →ₐ[K] InfiniteAdeleRing K) :=
  ⟨Pi.algHom K (fun v : InfinitePlace K => v.Completion) fun v => placeHom K L v (h v).some (h v).some_mem⟩

end NoNumberFieldNeeded

section CountFormula

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem nonempty_algHom_of_finrank_eq_three (h3 : Module.finrank K L = 3) :
    Nonempty (L →ₐ[K] InfiniteAdeleRing K) := by
  refine nonempty_algHom_of_forall_nonempty_unramifiedPlacesOver K L fun v => ?_
  have hc := InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank L v
  rw [h3] at hc
  exact Set.nonempty_of_ncard_ne_zero (by omega)

end CountFormula

end InfinitePlaceEmbedding

end OddDegreeEmbeddings

section ArchMatching

section AutomorphismPowerLemmas

open AutomorphicForm
open scoped TensorProduct

namespace RegularCentralizer

section Twisted

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem pow_finrank_eq_one [FiniteDimensional K L] (σ : L ≃ₐ[K] L) : σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
  exact Dvd.intro_left _
    (Module.finrank_mul_finrank K (IntermediateField.fixedField (Subgroup.zpowers σ)) L)

end Twisted

end RegularCentralizer

end AutomorphismPowerLemmas

section CarrierTopologyAndHaar

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct Topology
open scoped TensorProduct.RightActions
open AutomorphicForm

namespace OrbitalCarriers

section GLCarrier

variable (A : Type) [CommRing A] [TopologicalSpace A]

private theorem secondCountableTopology_gl [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private theorem locallyCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem sigmaCompactSpace_gl [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    [SecondCountableTopology A] : SigmaCompactSpace (GL (Fin 2) A) := by
  haveI := locallyCompactSpace_gl A
  haveI := secondCountableTopology_gl A
  exact sigmaCompactSpace_of_locallyCompact_secondCountable

end GLCarrier

section ArchCarriers

open NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

private theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

private theorem secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  exact secondCountableTopology_gl (InfiniteAdeleRing K)

private theorem isHaarMeasure_archHaarK :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf (InfiniteAdeleRing K)) (archHaarK K) := by
  letI := glBorelOf (InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_gl (InfiniteAdeleRing K)
  unfold archHaarK
  infer_instance

private theorem isHaarMeasure_archHaarL :
    @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] InfiniteAdeleRing K)) (archHaarL K L) := by
  letI := glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensorGL K L (InfiniteAdeleRing K)
  unfold archHaarL
  infer_instance

end ArchCarriers

end OrbitalCarriers

end CarrierTopologyAndHaar

section ArchimedeanIdentification

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace TensorProduct AutomorphicForm
open scoped TensorProduct.RightActions

namespace SplitMatching

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

private theorem secondCountableTopology_tensor [SecondCountableTopology A] : SecondCountableTopology (L ⊗[K] A) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (L ⊗[K] A)
  have hq : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  exact hq.isQuotientMap.secondCountableTopology hq.isOpenMap

end Generic

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem _root_.SplitMatching.secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

p2m_export "SplitMatching" "secondCountableTopology_infiniteAdeleRing"
private noncomputable def archIdentEquiv : (L ⊗[K] InfiniteAdeleRing K) ≃+* InfiniteAdeleRing L :=
  (Algebra.TensorProduct.comm K L (InfiniteAdeleRing K)).toRingEquiv.trans
    (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv

private theorem coe_archIdentEquiv : ⇑(archIdentEquiv K L) = ⇑(archIdent K L) := rfl

private theorem archIdent_comp_algebraMap :
    (archIdent K L).comp (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) =
      (M4aHerbrand.ArchSemilocal.genuineInfinitePlaceData (K := K) (L := L)).conorm :=
  RingHom.ext fun _ => rfl

private theorem coe_archIdentGL (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    ((archIdentGL K L g : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
      = (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (archIdent K L) := by
  ext i j
  simp [archIdentGL, Matrix.GeneralLinearGroup.map_apply]

private noncomputable def archIdentGLInv :
    GL (Fin 2) (InfiniteAdeleRing L) →* GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (archIdentEquiv K L).symm.toRingHom

private theorem coe_archIdentGLInv (h : GL (Fin 2) (InfiniteAdeleRing L)) :
    ((archIdentGLInv K L h : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      = (h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)).map (archIdentEquiv K L).symm := by
  ext i j
  simp [archIdentGLInv, Matrix.GeneralLinearGroup.map_apply]

private theorem archIdentGLInv_archIdentGL (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    archIdentGLInv K L (archIdentGL K L g) = g := by
  apply Units.ext
  ext i j
  rw [coe_archIdentGLInv, Matrix.map_apply, coe_archIdentGL, Matrix.map_apply, ← coe_archIdentEquiv]
  exact (archIdentEquiv K L).symm_apply_apply _

private theorem archIdentGL_archIdentGLInv (h : GL (Fin 2) (InfiniteAdeleRing L)) :
    archIdentGL K L (archIdentGLInv K L h) = h := by
  apply Units.ext
  ext i j
  rw [coe_archIdentGL, Matrix.map_apply, coe_archIdentGLInv, Matrix.map_apply, ← coe_archIdentEquiv]
  exact (archIdentEquiv K L).apply_symm_apply _

variable [FiniteDimensional K L]

private theorem continuous_archIdent : Continuous (archIdent K L) := by
  haveI := isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  refine IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing K) (archIdent K L) ?_
  rw [archIdent_comp_algebraMap]
  exact M4aHerbrand.ArchSemilocal.continuous_conorm (K := K) (L := L)

private theorem isOpenMap_archIdent : IsOpenMap (archIdent K L) := by
  haveI := isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI := locallyCompactSpace_tensor K L (InfiniteAdeleRing K)
  haveI := secondCountableTopology_infiniteAdeleRing K
  haveI := secondCountableTopology_tensor K L (InfiniteAdeleRing K)
  exact (archIdent K L).toAddMonoidHom.isOpenMap_of_sigmaCompact (archIdentEquiv K L).surjective
    (continuous_archIdent K L)

private noncomputable def archIdentHomeomorph : (L ⊗[K] InfiniteAdeleRing K) ≃ₜ InfiniteAdeleRing L :=
  (archIdentEquiv K L).toEquiv.toHomeomorphOfContinuousOpen (continuous_archIdent K L) (isOpenMap_archIdent K L)

private theorem continuous_archIdentEquiv_symm : Continuous (archIdentEquiv K L).symm :=
  (archIdentHomeomorph K L).symm.continuous

private theorem continuous_archIdentGL : Continuous (archIdentGL K L) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ archIdentGL K L) = fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
        (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (archIdent K L) :=
      funext fun g => coe_archIdentGL K L g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_archIdent K L)
  · have h : (fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          ((archIdentGL K L g)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)).val) =
        fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          ((g⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (archIdent K L) :=
      funext fun g => by rw [← map_inv, coe_archIdentGL]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_archIdent K L)

private theorem continuous_archIdentGLInv : Continuous (archIdentGLInv K L) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : (Units.val ∘ archIdentGLInv K L) = fun g : GL (Fin 2) (InfiniteAdeleRing L) =>
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)).map (archIdentEquiv K L).symm :=
      funext fun g => coe_archIdentGLInv K L g
    rw [h]
    exact Units.continuous_val.matrix_map (continuous_archIdentEquiv_symm K L)
  · have h : (fun g : GL (Fin 2) (InfiniteAdeleRing L) =>
          ((archIdentGLInv K L g)⁻¹ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).val) =
        fun g : GL (Fin 2) (InfiniteAdeleRing L) =>
          ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)).map
            (archIdentEquiv K L).symm :=
      funext fun g => by rw [← map_inv, coe_archIdentGLInv]
    rw [h]
    exact Units.continuous_coe_inv.matrix_map (continuous_archIdentEquiv_symm K L)

private noncomputable def archIdentGLHomeomorph :
    GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ GL (Fin 2) (InfiniteAdeleRing L) where
  toFun := archIdentGL K L
  invFun := archIdentGLInv K L
  left_inv := archIdentGLInv_archIdentGL K L
  right_inv := archIdentGL_archIdentGLInv K L
  continuous_toFun := continuous_archIdentGL K L
  continuous_invFun := continuous_archIdentGLInv K L

private theorem coe_archIdentGLHomeomorph : ⇑(archIdentGLHomeomorph K L) = ⇑(archIdentGL K L) := rfl

end Transport

section TestFactor

variable (F : Type) [Field F]

open scoped Classical in
private theorem continuous_archEntries : Continuous (archEntries F) := by
  have hc : Continuous fun x : InfiniteAdeleRing F => InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact hc.comp (hval.matrix_elem i j)

variable [NumberField F]

open scoped Classical in
private theorem continuous_of_isArchTestFactor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := hfa
  have h : fa = Φ ∘ archEntries F := funext hfa
  rw [h]
  exact hΦ.continuous.comp (continuous_archEntries F)

end TestFactor

end SplitMatching

end ArchimedeanIdentification

section ArchTestFactorLemmas

open NumberField MeasureTheory AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace ArchMatchingAssembly

section TestFunctions

variable (F : Type) [Field F] [NumberField F]

private theorem measurable_of_isArchTestFactor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) : Measurable[glBorelOf (InfiniteAdeleRing F)] fa := by
  letI := glBorelOf (InfiniteAdeleRing F)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing F)
  exact (SplitMatching.continuous_of_isArchTestFactor F fa hfa).measurable

private theorem bounded_of_isArchTestFactor (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) : ∃ C : ℝ, ∀ g, ‖fa g‖ ≤ C :=
  (SplitMatching.continuous_of_isArchTestFactor F fa hfa).bounded_above_of_compact_support hfa.2

end TestFunctions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)

private theorem measurable_comp_archIdentGL_of_isArchTestFactor (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (hφa : IsArchTestFactor L φa) :
    Measurable[glBorelOf (L ⊗[K] InfiniteAdeleRing K)] (φa ∘ archIdentGL K L) := by
  letI := glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI := borelSpace_glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  exact ((SplitMatching.continuous_of_isArchTestFactor L φa hφa).comp
    (SplitMatching.continuous_archIdentGL K L)).measurable

private theorem areMatchingArch_of_forall_exists_eq_of_forall_zero
    [SecondCountableTopology (InfiniteAdeleRing K)]
    (hσ : σ ^ Module.finrank K L = 1)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] InfiniteAdeleRing K)) (archHaarL K L))
    (hμK : @Measure.IsHaarMeasure _ _ _ (glBorelOf (InfiniteAdeleRing K)) (archHaarK K))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (hφm : Measurable[glBorelOf (L ⊗[K] InfiniteAdeleRing K)] (φa ∘ archIdentGL K L))
    (hφb : ∃ C : ℝ, ∀ g, ‖φa g‖ ≤ C)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (hfm : Measurable[glBorelOf (InfiniteAdeleRing K)] fa)
    (hfb : ∃ C : ℝ, ∀ g, ‖fa g‖ ≤ C)
    (hW1 : ∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ δ) →
      ∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
          (centralizerBorel (InfiniteAdeleRing K) γ))
        (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
          (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
        Coupled K L (InfiniteAdeleRing K) σ γ δ y τ τ' →
        ∃ I : ℂ,
          IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ' (φa ∘ archIdentGL K L) I ∧
            IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I)
    (hW2 : ∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
      (¬ ∃ δ, IsNormOf K L (InfiniteAdeleRing K) σ γ δ) →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
          (centralizerBorel (InfiniteAdeleRing K) γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
        IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa 0) :
    AreMatchingArch K L σ φa fa := by
  have hφb' : ∃ C : ℝ, ∀ g, ‖(φa ∘ archIdentGL K L) g‖ ≤ C := hφb.imp fun C hC g => hC _
  unfold AreMatchingArch AreMatchingOn
  refine ⟨fun δ hδ γ hγ y hy τ τ' hτ hτ' hc I I' hI' hI => ?_, fun γ hγ hn τ hτ I hI => ?_⟩
  · obtain ⟨I₀, hT, hR⟩ := hW1 δ hδ γ hγ y hy τ τ' hτ hτ' hc
    have h₁ : I' = I₀ :=
      AutomorphicForm.IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L
        (InfiniteAdeleRing K) σ hσ (archHaarL K L) hμL δ hδ τ' hτ' (φa ∘ archIdentGL K L) hφm hφb' hI' hT
    have h₂ : I = I₀ :=
      AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple (InfiniteAdeleRing K) (archHaarK K) hμK
        γ hγ τ hτ fa hfm hfb hI hR
    rw [h₁, h₂]
  · exact AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple (InfiniteAdeleRing K) (archHaarK K)
      hμK γ hγ τ hτ fa hfm hfb hI (hW2 γ hγ hn τ hτ)

private theorem areMatchingArch_of_isArchTestFactor_of_forall_exists_eq_of_forall_zero
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : IsArchTestFactor K fa)
    (hW1 : ∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ δ) →
      ∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
          (centralizerBorel (InfiniteAdeleRing K) γ))
        (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
          (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
        Coupled K L (InfiniteAdeleRing K) σ γ δ y τ τ' →
        ∃ I : ℂ,
          IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ' (φa ∘ archIdentGL K L) I ∧
            IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I)
    (hW2 : ∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
      (¬ ∃ δ, IsNormOf K L (InfiniteAdeleRing K) σ γ δ) →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
          (centralizerBorel (InfiniteAdeleRing K) γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
        IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa 0) :
    AreMatchingArch K L σ φa fa := by
  haveI := OrbitalCarriers.secondCountableTopology_infiniteAdeleRing K
  exact areMatchingArch_of_forall_exists_eq_of_forall_zero K L σ (RegularCentralizer.pow_finrank_eq_one K L σ)
    (OrbitalCarriers.isHaarMeasure_archHaarL K L) (OrbitalCarriers.isHaarMeasure_archHaarK K)
    φa (measurable_comp_archIdentGL_of_isArchTestFactor K L φa hφa) (bounded_of_isArchTestFactor L φa hφa)
    fa (measurable_of_isArchTestFactor K fa hfa) (bounded_of_isArchTestFactor K fa hfa) hW1 hW2

end ArchMatchingAssembly

end ArchTestFactorLemmas

end ArchMatching

open NumberField AutomorphicForm

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hι : IsEmpty (L →ₐ[K] InfiniteAdeleRing K)) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧ AreMatchingArch K L σ φa fa := by
  rcases hdeg with h2 | h3
  · obtain ⟨tysK, fa, hfa, hfaT, hW1, hW2⟩ :=
      AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom
        K L h2 σ hσ hι tysL φa hφa hφt
    exact ⟨tysK, fa, hfa, hfaT,
      ArchMatchingAssembly.areMatchingArch_of_isArchTestFactor_of_forall_exists_eq_of_forall_zero
        K L σ φa hφa fa hfa hW1 hW2⟩
  · exact (hι.false (InfinitePlaceEmbedding.nonempty_algHom_of_finrank_eq_three K L h3).some).elim

end S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom
end P2MW
export P2MW.S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom (solution)
