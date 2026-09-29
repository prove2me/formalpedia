-- Prove2me | solution 1 for AutomorphicForm.lintegral_orbital_comp_inv_mul_eq_and_weightedOrbital_eq_of_glArch_eq_one_of_isSemiLocalFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a3451c59-d021-52f9-ac30-fa71cd006f7e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_ringEquiv_prod_forall_act_eq
import Theorems.Thm_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
import Theorems.Thm_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_orbital_comp_inv_mul_eq_and_weightedOrbital_eq_of_glArch_eq_one_of_isSemiLocalFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option synthInstance.maxHeartbeats 1600000

open TopologicalSpace Filter Topology
open scoped TensorProduct.RightActions

noncomputable section

namespace TranslGlue

open AutomorphicForm
open scoped ENNReal

section IntegralUnitsAlgebra

variable {A : Type*} [CommRing A]

theorem mul_mem_integralUnitsSet (B : Subring A) {g h : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (B : Set A)) (hh : h ∈ AutomorphicForm.integralUnitsSet (B : Set A)) :
    g * h ∈ AutomorphicForm.integralUnitsSet (B : Set A) := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (hh.2 i k) (hg.2 k j)

theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet U) : g⁻¹ ∈ AutomorphicForm.integralUnitsSet U := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem isClosed_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] {U : Set A} (hU : IsClosed U) :
    IsClosed (AutomorphicForm.integralUnitsSet (A := A) U) := by
  rw [AutomorphicForm.integralUnitsSet_eq_preimage]
  have hC : IsClosed (AutomorphicForm.integralMatrixSet (A := A) U) := by
    rw [AutomorphicForm.integralMatrixSet_eq_pi]
    exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hU
  exact (hC.prod (MulOpposite.opHomeomorph.isClosedMap _ hC)).preimage Units.continuous_embedProduct

theorem continuous_glMap {B : Type*} [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

end IntegralUnitsAlgebra

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalHomeomorph_apply (x : L ⊗[K] v.adicCompletion K) :
    AutomorphicForm.semiLocalHomeomorph K L v x =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x :=
  rfl

theorem semiLocalEval_apply (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) :=
  rfl

theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L v (AutomorphicForm.semiLocalEval K L v a) w = a w.1 := by
  rw [semiLocalHomeomorph_apply, semiLocalEval_apply, AlgEquiv.apply_symm_apply]
  rfl

theorem semiLocalEval_mem_semiLocalIntegers_iff (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  refine forall_congr' fun w => ?_
  rw [semiLocalHomeomorph_semiLocalEval, SetLike.mem_coe]

theorem semiLocalComponent_apply (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    (AutomorphicForm.semiLocalComponent K L v h : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
      AutomorphicForm.semiLocalEval K L v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) :=
  rfl

theorem semiLocalComponent_mem_iff (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      ∀ w : v.Extension (𝓞 L), AdelicLevel.finComponent (𝓞 L) L w.1 h ∈ AutomorphicForm.localIntegralSet L w.1 := by
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet]
  simp only [← map_inv, semiLocalComponent_apply, semiLocalEval_mem_semiLocalIntegers_iff,
    AutomorphicForm.mem_localIntegralSet, AdelicLevel.finComponent_apply]
  constructor
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w⟩
  · intro hw
    exact ⟨fun i j w => (hw w).1 i j, fun i j w => (hw w).2 i j⟩

theorem continuous_semiLocalEval : Continuous (AutomorphicForm.semiLocalEval K L v) := by
  have h1 : Continuous fun a : FiniteAdeleRing (𝓞 L) L =>
      (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) :=
    continuous_pi fun w => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1
  have h2 : Continuous (AutomorphicForm.semiLocalHomeomorph K L v).symm :=
    (AutomorphicForm.semiLocalHomeomorph K L v).symm.continuous
  have key : ∀ a : FiniteAdeleRing (𝓞 L) L, AutomorphicForm.semiLocalEval K L v a =
      (AutomorphicForm.semiLocalHomeomorph K L v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) := by
    intro a
    apply (AutomorphicForm.semiLocalHomeomorph K L v).injective
    rw [Homeomorph.apply_symm_apply]
    funext w
    exact semiLocalHomeomorph_semiLocalEval K L v a w
  have heq : (fun a : FiniteAdeleRing (𝓞 L) L => AutomorphicForm.semiLocalEval K L v a) =
      fun a => (AutomorphicForm.semiLocalHomeomorph K L v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) := funext key
  show Continuous fun a : FiniteAdeleRing (𝓞 L) L => AutomorphicForm.semiLocalEval K L v a
  rw [heq]
  exact h2.comp h1

theorem continuous_semiLocalComponent : Continuous (AutomorphicForm.semiLocalComponent K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact continuous_glMap _ (continuous_semiLocalEval K L v)

end SemiLocal

section FiniteFactor

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

def above : Finset (HeightOneSpectrum (𝓞 L)) :=
  HeightOneSpectrum.preimageComapFinset (𝓞 K) K L (𝓞 L) S

variable {K L S}

theorem mem_above_iff {w : HeightOneSpectrum (𝓞 L)} : w ∈ above K L S ↔ w.under (𝓞 K) ∈ S := by
  rw [above, HeightOneSpectrum.preimageComapFinset, Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe]

variable (K L S)

def intOutside : Subring (FiniteAdeleRing (𝓞 L) L) where
  carrier := {x | ∀ w, w ∉ above K L S → x w ∈ w.adicCompletionIntegers L}
  mul_mem' ha hb w hw := by rw [AdelicLevel.coe_mul_apply]; exact mul_mem (ha w hw) (hb w hw)
  one_mem' w _ := by rw [AdelicLevel.coe_one_apply]; exact one_mem _
  add_mem' ha hb w hw := by rw [AdelicLevel.coe_add_apply]; exact add_mem (ha w hw) (hb w hw)
  zero_mem' w _ := by rw [AdelicLevel.coe_zero_apply]; exact zero_mem _
  neg_mem' ha w hw := by rw [AdelicLevel.coe_neg_apply]; exact neg_mem (ha w hw)

theorem mem_intOutside {x : FiniteAdeleRing (𝓞 L) L} :
    x ∈ intOutside K L S ↔ ∀ w, w ∉ above K L S → x w ∈ w.adicCompletionIntegers L := Iff.rfl

theorem isOpen_intOutside : IsOpen (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (A := fun w : HeightOneSpectrum (𝓞 L) => (w.adicCompletionIntegers L : Set (w.adicCompletion L)))
    Fact.out (p := fun w => w ∉ above K L S)

theorem isClosed_intOutside : IsClosed (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) := by
  have : (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L)) = ⋂ w ∈ ((↑(above K L S) : Set (HeightOneSpectrum (𝓞 L)))ᶜ),
      (fun x : FiniteAdeleRing (𝓞 L) L => x w) ⁻¹' (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := by
    ext x
    simp only [SetLike.mem_coe, mem_intOutside, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
  rw [this]
  exact isClosed_biInter fun w _ =>
    (AdelicLevel.isClosed_adicCompletionIntegers w).preimage (AdelicLevel.continuous_finAdeleEval (𝓞 L) L w)

def unitsOutside : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) where
  carrier := AutomorphicForm.integralUnitsSet (intOutside K L S : Set (FiniteAdeleRing (𝓞 L) L))
  mul_mem' ha hb := mul_mem_integralUnitsSet _ ha hb
  one_mem' := AutomorphicForm.one_mem_integralUnitsSet (zero_mem _) (one_mem _)
  inv_mem' ha := inv_mem_integralUnitsSet _ ha

variable {K L S}

theorem mem_unitsOutside_iff {g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} :
    g ∈ unitsOutside K L S ↔
      ∀ w, w ∉ above K L S → AdelicLevel.finComponent (𝓞 L) L w g ∈ AutomorphicForm.localIntegralSet L w := by
  show g ∈ AutomorphicForm.integralUnitsSet _ ↔ _
  simp only [AutomorphicForm.mem_integralUnitsSet, SetLike.mem_coe, mem_intOutside,
    AutomorphicForm.mem_localIntegralSet, AdelicLevel.finComponent_apply, ← map_inv]
  exact ⟨fun h w hw => ⟨fun i j => h.1 i j w hw, fun i j => h.2 i j w hw⟩,
    fun h => ⟨fun i j w hw => (h w hw).1 i j, fun i j w hw => (h w hw).2 i j⟩⟩

theorem mem_unitsOutside_iff_semiLocal {g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} :
    g ∈ unitsOutside K L S ↔
      ∀ v ∉ S, AutomorphicForm.semiLocalComponent K L v g ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  rw [mem_unitsOutside_iff]
  constructor
  · intro h v hv
    rw [semiLocalComponent_mem_iff]
    intro w
    apply h
    rw [mem_above_iff, w.2]
    exact hv
  · intro h w hw
    have hv : w.under (𝓞 K) ∉ S := fun h' => hw (mem_above_iff.mpr h')
    have := (semiLocalComponent_mem_iff K L (w.under (𝓞 K)) g).mp (h _ hv) ⟨w, rfl⟩
    exact this

variable (K L S)

theorem isOpen_unitsOutside : IsOpen (unitsOutside K L S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :=
  AutomorphicForm.isOpen_integralUnitsSet (isOpen_intOutside K L S)

theorem isClosed_unitsOutside : IsClosed (unitsOutside K L S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :=
  isClosed_integralUnitsSet (isClosed_intOutside K L S)

theorem finiteIntegralGL2_le_unitsOutside : AdelicLevel.finiteIntegralGL2 (𝓞 L) L ≤ unitsOutside K L S := by
  intro g hg
  rw [AdelicLevel.mem_finiteIntegralGL2_iff] at hg
  exact ⟨fun i j w _ => hg.1 i j w, fun i j w _ => hg.2 i j w⟩

def gluedAbove (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : ℂ :=
  (unitsOutside K L S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))).indicator
    (fun h => ∏ v ∈ S, φS v (AutomorphicForm.semiLocalComponent K L v h)) h

variable {K L S}

theorem gluedAbove_of_mem {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hh : h ∈ unitsOutside K L S) :
    gluedAbove K L S φS h = ∏ v ∈ S, φS v (AutomorphicForm.semiLocalComponent K L v h) := by
  unfold gluedAbove
  rw [Set.indicator_of_mem (show h ∈ (unitsOutside K L S : Set _) from hh)]

theorem gluedAbove_of_not_mem {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hh : h ∉ unitsOutside K L S) : gluedAbove K L S φS h = 0 := by
  unfold gluedAbove
  rw [Set.indicator_of_notMem (show h ∉ (unitsOutside K L S : Set _) from hh)]

theorem isLocallyConstant_finset_prod {X : Type*} [TopologicalSpace X] {ι : Type*} (s : Finset ι)
    (F : ι → X → ℂ) (hF : ∀ i ∈ s, IsLocallyConstant (F i)) :
    IsLocallyConstant fun x => ∏ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const 1
  | insert a s ha ih =>
    have h1 : IsLocallyConstant (F a) := hF a (Finset.mem_insert_self a s)
    have h2 : IsLocallyConstant fun x => ∏ i ∈ s, F i x := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have := h1.mul h2
    simp only [Finset.prod_insert ha]
    exact this

theorem isLocallyConstant_gluedAbove
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφS : ∀ v ∈ S, AutomorphicForm.IsSemiLocalTestFn K L v (φS v)) : IsLocallyConstant (gluedAbove K L S φS) := by
  have hprod : IsLocallyConstant fun h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) =>
      ∏ v ∈ S, φS v (AutomorphicForm.semiLocalComponent K L v h) :=
    isLocallyConstant_finset_prod S (fun v h => φS v (AutomorphicForm.semiLocalComponent K L v h)) fun v hv =>
      (hφS v hv).1.comp_continuous (continuous_semiLocalComponent K L v)
  have hind : IsLocallyConstant ((unitsOutside K L S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))).indicator
      fun _ => (1 : ℂ)) :=
    AutomorphicForm.isLocallyConstant_indicator_one (isOpen_unitsOutside K L S) (isClosed_unitsOutside K L S)
  have := hind.mul hprod
  convert this using 1
  funext h
  simp only [gluedAbove, Pi.mul_apply]
  by_cases hh : h ∈ unitsOutside K L S
  · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, one_mul]
  · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, zero_mul]

variable (K L S) in
theorem isCompact_box (D : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L))
    (hD : ∀ w ∈ above K L S, IsCompact (D w))
    (hD' : ∀ w, w ∉ above K L S → D w = (w.adicCompletionIntegers L : Set (w.adicCompletion L))) :
    IsCompact {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ D w} := by
  set T : Set (HeightOneSpectrum (𝓞 L)) := (↑(above K L S) : Set (HeightOneSpectrum (𝓞 L)))ᶜ with hT
  have hTc : Filter.cofinite ≤ 𝓟 T := by
    rw [Filter.le_principal_iff, hT]
    exact (above K L S).finite_toSet.compl_mem_cofinite
  let RR : HeightOneSpectrum (𝓞 L) → Type := fun w => w.adicCompletion L
  let AA : ∀ w : HeightOneSpectrum (𝓞 L), Set (RR w) := fun w =>
    (w.adicCompletionIntegers L : Set (w.adicCompletion L))
  let ι := RestrictedProduct.inclusion RR AA hTc
  set B' : Set (RestrictedProduct RR AA (𝓟 T)) := {y | ∀ w, y w ∈ D w} with hB'
  have hDall : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ above K L S
    · exact hD w hw
    · rw [hD' w hw]
      exact isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w)
  have hB'c : IsCompact B' := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := RR) (A := AA) (S := T)).isCompact_iff]
    have heq : (DFunLike.coe '' B' : Set (∀ w, RR w)) = Set.pi Set.univ D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ w -
        exact hy w
      · intro hx
        have hx' : ∀ᶠ w in 𝓟 T, x w ∈ AA w := by
          rw [Filter.eventually_principal]
          intro w hw
          have hwS : w ∉ above K L S := hw
          have := hx w (Set.mem_univ w)
          rwa [hD' w hwS] at this
        exact ⟨⟨x, hx'⟩, fun w => hx w (Set.mem_univ w), rfl⟩
    rw [heq]
    exact isCompact_univ_pi hDall
  have himage : ι '' B' = {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ D w} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ w
      exact hy w
    · intro hx
      have hx' : ∀ᶠ w in 𝓟 T, (x : ∀ w, RR w) w ∈ AA w := by
        rw [Filter.eventually_principal]
        intro w hw
        have hwS : w ∉ above K L S := hw
        have := hx w
        rwa [hD' w hwS] at this
      refine ⟨⟨(x : ∀ w, RR w), hx'⟩, fun w => hx w, ?_⟩
      exact RestrictedProduct.ext _ _ fun w => rfl
  rw [← himage]
  exact hB'c.image (RestrictedProduct.continuous_inclusion hTc)

theorem isCompact_entrySetAbove (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    {T : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))} (hT : IsCompact T) :
    IsCompact (⋃ p : Fin 2 × Fin 2,
      ((fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          AutomorphicForm.semiLocalHomeomorph K L v ((g : Matrix (Fin 2) (Fin 2) _) p.1 p.2) w) '' T ∪
       (fun g : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
          AutomorphicForm.semiLocalHomeomorph K L v
            (((g⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) p.1 p.2) w) '' T)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  have hev : Continuous fun x : L ⊗[K] v.adicCompletion K => AutomorphicForm.semiLocalHomeomorph K L v x w :=
    (continuous_apply w).comp (AutomorphicForm.semiLocalHomeomorph K L v).continuous
  refine isCompact_iUnion fun p => (hT.image ?_).union (hT.image ?_)
  · exact hev.comp (Units.continuous_val.matrix_elem p.1 p.2)
  · exact hev.comp (Units.continuous_coe_inv.matrix_elem p.1 p.2)

theorem hasCompactSupport_gluedAbove
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφS : ∀ v ∈ S, AutomorphicForm.IsSemiLocalTestFn K L v (φS v)) : HasCompactSupport (gluedAbove K L S φS) := by
  classical

  let C : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w =>
    ⋃ p : Fin 2 × Fin 2,
      ((fun g : GL (Fin 2) (L ⊗[K] (w.under (𝓞 K)).adicCompletion K) =>
          AutomorphicForm.semiLocalHomeomorph K L (w.under (𝓞 K)) ((g : Matrix (Fin 2) (Fin 2) _) p.1 p.2)
            ⟨w, rfl⟩) '' tsupport (φS (w.under (𝓞 K))) ∪
       (fun g : GL (Fin 2) (L ⊗[K] (w.under (𝓞 K)).adicCompletion K) =>
          AutomorphicForm.semiLocalHomeomorph K L (w.under (𝓞 K))
            (((g⁻¹ : GL (Fin 2) (L ⊗[K] (w.under (𝓞 K)).adicCompletion K)) : Matrix (Fin 2) (Fin 2) _) p.1 p.2)
            ⟨w, rfl⟩) '' tsupport (φS (w.under (𝓞 K))))
  let D : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w =>
    if w ∈ above K L S then C w else (w.adicCompletionIntegers L : Set (w.adicCompletion L))
  have hD : ∀ w ∈ above K L S, IsCompact (D w) := by
    intro w hw
    simp only [D, if_pos hw]
    exact isCompact_entrySetAbove (w.under (𝓞 K)) ⟨w, rfl⟩ (hφS _ (mem_above_iff.mp hw)).2
  have hD' : ∀ w, w ∉ above K L S → D w = (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := by
    intro w hw
    simp only [D, if_neg hw]
  have hbox := isCompact_box K L S D hD hD'
  have hbig : IsCompact (AutomorphicForm.integralUnitsSet (A := FiniteAdeleRing (𝓞 L) L)
      {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ D w}) :=
    AutomorphicForm.isCompact_integralUnitsSet hbox
  refine HasCompactSupport.intro hbig fun h hh => ?_
  by_contra hne
  apply hh
  have hmem : h ∈ unitsOutside K L S := by
    by_contra hnot
    exact hne (gluedAbove_of_not_mem hnot)
  rw [gluedAbove_of_mem hmem] at hne
  have hfac : ∀ v ∈ S, φS v (AutomorphicForm.semiLocalComponent K L v h) ≠ 0 := fun v hv h0 =>
    hne (Finset.prod_eq_zero hv h0)
  have hsupp : ∀ v ∈ S, AutomorphicForm.semiLocalComponent K L v h ∈ tsupport (φS v) := fun v hv =>
    subset_tsupport _ (Function.mem_support.mpr (hfac v hv))
  rw [mem_unitsOutside_iff] at hmem
  rw [AutomorphicForm.mem_integralUnitsSet]

  have key : ∀ (w : HeightOneSpectrum (𝓞 L)) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2),
      ((g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w =
        AutomorphicForm.semiLocalHomeomorph K L (w.under (𝓞 K))
          ((AutomorphicForm.semiLocalComponent K L (w.under (𝓞 K)) g : Matrix (Fin 2) (Fin 2) _) i j)
          ⟨w, rfl⟩ := by
    intro w g i j
    rw [semiLocalComponent_apply, semiLocalHomeomorph_semiLocalEval]
  refine ⟨fun i j w => ?_, fun i j w => ?_⟩
  · by_cases hw : w ∈ above K L S
    · simp only [D, if_pos hw]
      refine Set.mem_iUnion.mpr ⟨(i, j), Set.mem_union_left _ ⟨_, hsupp _ (mem_above_iff.mp hw), ?_⟩⟩
      exact (key w h i j).symm
    · simp only [D, if_neg hw]
      have := (AutomorphicForm.mem_localIntegralSet L w).mp (hmem w hw)
      have h1 := this.1 i j
      rwa [AdelicLevel.finComponent_apply] at h1
  · by_cases hw : w ∈ above K L S
    · simp only [D, if_pos hw]
      refine Set.mem_iUnion.mpr ⟨(i, j), Set.mem_union_right _ ⟨_, hsupp _ (mem_above_iff.mp hw), ?_⟩⟩
      have e1 : (AutomorphicForm.semiLocalComponent K L (w.under (𝓞 K)) h)⁻¹ =
          AutomorphicForm.semiLocalComponent K L (w.under (𝓞 K)) h⁻¹ := (map_inv _ _).symm
      simp only [e1]
      exact (key w h⁻¹ i j).symm
    · simp only [D, if_neg hw]
      have := (AutomorphicForm.mem_localIntegralSet L w).mp (hmem w hw)
      have h1 := this.2 i j
      rwa [← map_inv, AdelicLevel.finComponent_apply] at h1

theorem isFinTestFactor_gluedAbove
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (hφS : ∀ v ∈ S, AutomorphicForm.IsSemiLocalTestFn K L v (φS v)) :
    AutomorphicForm.IsFinTestFactor L (gluedAbove K L S φS) :=
  ⟨isLocallyConstant_gluedAbove hφS, hasCompactSupport_gluedAbove hφS⟩

end FiniteFactor

section GL2

variable {R : Type*} [CommRing R]

private theorem _root_.TranslGlue.scalar_apply (u : Rˣ) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j =
      if i = j then (u : R) else 0 := by
  show ((Matrix.scalar (Fin 2)) (u : R)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]

p2m_export "TranslGlue" "scalar_apply"

theorem commute_of_diagonal {g h : GL (Fin 2) R}
    (hg10 : (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) (hg01 : (g : Matrix (Fin 2) (Fin 2) R) 0 1 = 0)
    (hh10 : (h : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) (hh01 : (h : Matrix (Fin 2) (Fin 2) R) 0 1 = 0) :
    Commute g h := by
  refine Units.ext ?_
  show (g : Matrix (Fin 2) (Fin 2) R) * (h : Matrix (Fin 2) (Fin 2) R) =
    (h : Matrix (Fin 2) (Fin 2) R) * (g : Matrix (Fin 2) (Fin 2) R)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg10, hg01, hh10, hh01, mul_comm]

def unipUp : GL (Fin 2) R :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def unipLow : GL (Fin 2) R :=
  ⟨!![1, 0; 1, 1], !![1, 0; -1, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem exists_scalar_of_mem_center {ζ : GL (Fin 2) R} (hζ : ζ ∈ Subgroup.center (GL (Fin 2) R)) :
    ∃ u : Rˣ, ζ = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  have hE := Subgroup.mem_center_iff.mp hζ unipUp
  have hF := Subgroup.mem_center_iff.mp hζ unipLow
  have hE' := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) hE
  have hF' := congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) hF
  simp only [Units.val_mul] at hE' hF'
  set M : Matrix (Fin 2) (Fin 2) R := (ζ : Matrix (Fin 2) (Fin 2) R) with hM
  have e00 := congrFun (congrFun hE' 0) 0
  have e01 := congrFun (congrFun hE' 0) 1
  have f10 := congrFun (congrFun hF' 1) 0
  have f00 := congrFun (congrFun hF' 0) 0
  simp only [unipUp, unipLow, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 f10 f00
  norm_num at e00 e01 f10 f00

  have h10 : M 1 0 = 0 := e00
  have h01 : M 0 1 = 0 := f00
  have h11 : M 1 1 = M 0 0 := by linear_combination e01
  have hdet : IsUnit M.det := by
    rw [hM]; exact (Matrix.GeneralLinearGroup.det ζ).isUnit
  rw [Matrix.det_fin_two, h10, h01, h11, mul_zero, sub_zero] at hdet
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hdet
  refine ⟨u, Units.ext ?_⟩
  ext i j
  rw [scalar_apply]
  fin_cases i <;> fin_cases j
  · exact hu.symm
  · exact h01
  · exact h10
  · simpa using h11.trans hu.symm

theorem inv_mul_eq_of_mul_inv_mem_center {G : Type*} [Group G] {h k : G}
    (hc : k * h⁻¹ ∈ Subgroup.center G) : h⁻¹ * k = k * h⁻¹ := by
  have := Subgroup.mem_center_iff.mp hc h

  calc h⁻¹ * k = h⁻¹ * (k * h⁻¹ * h) := by group
    _ = h⁻¹ * (h * (k * h⁻¹)) := by rw [this]
    _ = k * h⁻¹ := by group

theorem measurable_comp_out {G β : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace β] (H : Subgroup G)
    {f : G → β} (hf : Measurable f) (hinv : ∀ h ∈ H, ∀ y, f (h * y) = f y) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => f q.out := by
  rw [measurable_from_quotient]
  have e : (fun q : MulAction.orbitRel.Quotient H G => f q.out) ∘ Quotient.mk'' = f := by
    funext y
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk'' y : MulAction.orbitRel.Quotient H G))))
    show f ((Quotient.mk'' y : MulAction.orbitRel.Quotient H G).out) = f y
    rw [← hk]
    exact hinv k k.2 y
  rw [e]
  exact hf

end GL2

section Adelic

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

local notation "𝔸" => AdeleRing (𝓞 L) L

theorem centralScalar_apply (z : (𝔸)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 L) L z : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      if i = j then (z : 𝔸) else 0 :=
  scalar_apply z i j

theorem sigmaAdelicAct_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      D.act σ ((g : Matrix (Fin 2) (Fin 2) 𝔸) i j) :=
  rfl

theorem globalPoints_apply (t : GL (Fin 2) L) (i j : Fin 2) :
    ((globalPoints (𝓞 L) L t : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      algebraMap L 𝔸 ((t : Matrix (Fin 2) (Fin 2) L) i j) :=
  rfl

theorem coe_unitsAct (z : (𝔸)ˣ) : ((D.unitsAct σ z : (𝔸)ˣ) : 𝔸) = D.act σ (z : 𝔸) := rfl

theorem sigmaAdelicAct_centralScalar (z : (𝔸)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Units.ext ?_
  ext i j
  rw [sigmaAdelicAct_apply, centralScalar_apply, centralScalar_apply, coe_unitsAct]
  split_ifs
  · rfl
  · exact map_zero _

theorem centralScalar_commute (z : (𝔸)ˣ) (g : AdelicGL2 (𝓞 L) L) : Commute (centralScalar (𝓞 L) L z) g := by
  refine Units.ext ?_
  show ((Matrix.scalar (Fin 2)) (z : 𝔸)) * (g : Matrix (Fin 2) (Fin 2) 𝔸) =
    (g : Matrix (Fin 2) (Fin 2) 𝔸) * (Matrix.scalar (Fin 2)) (z : 𝔸)
  exact (Matrix.scalar_commute (z : 𝔸) (fun r => mul_comm _ r) _).eq

theorem unitsAct_unitsAct_inv (u : (𝔸)ˣ) : D.unitsAct σ (D.unitsAct σ⁻¹ u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem exists_idele_forall_conj_eq {h : AdelicGL2 (𝓞 L) L}
    (hh10 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0) (hh01 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = 0)
    (hcen : sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L))
    (t : GL (Fin 2) L) (ht10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    ∃ u : (𝔸)ˣ, ∀ (y : AdelicGL2 (𝓞 L) L) (z : (𝔸)ˣ),
      (h * y)⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (h * y)) =
        y⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (u * z) * y) := by
  obtain ⟨u₀, hu₀⟩ := exists_scalar_of_mem_center hcen
  refine ⟨D.unitsAct σ⁻¹ u₀, fun y z => ?_⟩

  have hgt10 : ((globalPoints (𝓞 L) L t : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := by
    rw [globalPoints_apply, ht10, map_zero]
  have hgt01 : ((globalPoints (𝓞 L) L t : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = 0 := by
    rw [globalPoints_apply, ht01, map_zero]
  have e2 : h⁻¹ * globalPoints (𝓞 L) L t = globalPoints (𝓞 L) L t * h⁻¹ :=
    ((commute_of_diagonal hgt10 hgt01 hh10 hh01).inv_right).eq.symm
  have e3 : h⁻¹ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) =
      sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) * h⁻¹ := by
    rw [sigmaAdelicAct_centralScalar]
    exact ((centralScalar_commute L _ h⁻¹).eq).symm
  have e4 : h⁻¹ * sigmaAdelicAct K L D σ h = centralScalar (𝓞 L) L u₀ := by
    rw [inv_mul_eq_of_mul_inv_mem_center hcen, hu₀]; rfl
  have e5 : sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) * centralScalar (𝓞 L) L u₀ =
      sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (D.unitsAct σ⁻¹ u₀ * z)) := by
    rw [sigmaAdelicAct_centralScalar, sigmaAdelicAct_centralScalar, ← map_mul, map_mul (D.unitsAct σ),
      unitsAct_unitsAct_inv, mul_comm]
  calc (h * y)⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (h * y))
      = y⁻¹ * (h⁻¹ * globalPoints (𝓞 L) L t) *
          (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) * (sigmaAdelicAct K L D σ h * sigmaAdelicAct K L D σ y)) := by
        rw [map_mul, map_mul]; group
    _ = y⁻¹ * (globalPoints (𝓞 L) L t * h⁻¹) *
          (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) * (sigmaAdelicAct K L D σ h * sigmaAdelicAct K L D σ y)) := by
        rw [e2]
    _ = y⁻¹ * globalPoints (𝓞 L) L t * (h⁻¹ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z)) *
          (sigmaAdelicAct K L D σ h * sigmaAdelicAct K L D σ y) := by group
    _ = y⁻¹ * globalPoints (𝓞 L) L t * (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) * h⁻¹) *
          (sigmaAdelicAct K L D σ h * sigmaAdelicAct K L D σ y) := by rw [e3]
    _ = y⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) *
          (h⁻¹ * sigmaAdelicAct K L D σ h) * sigmaAdelicAct K L D σ y := by group
    _ = y⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) *
          centralScalar (𝓞 L) L u₀ * sigmaAdelicAct K L D σ y := by rw [e4]
    _ = y⁻¹ * globalPoints (𝓞 L) L t * (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) *
          centralScalar (𝓞 L) L u₀) * sigmaAdelicAct K L D σ y := by group
    _ = y⁻¹ * globalPoints (𝓞 L) L t * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (D.unitsAct σ⁻¹ u₀ * z)) *
          sigmaAdelicAct K L D σ y := by rw [e5]
    _ = y⁻¹ * globalPoints (𝓞 L) L t *
          sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (D.unitsAct σ⁻¹ u₀ * z) * y) := by
        rw [map_mul (sigmaAdelicAct K L D σ) (centralScalar (𝓞 L) L _) y]; group

theorem adelicWeyl_apply (i j : Fin 2) :
    ((adelicWeyl (𝓞 L) L : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      algebraMap L 𝔸 ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) L) i j) :=
  rfl

theorem diagOne_apply (a : (𝔸)ˣ) (i j : Fin 2) :
    ((AdelicLevel.diagOne a : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) 𝔸) i j =
      Matrix.diagonal ![(a : 𝔸), 1] i j :=
  rfl

theorem exists_eq_centralScalar_mul_diagOne {h : AdelicGL2 (𝓞 L) L}
    (hh10 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0) (hh01 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = 0) :
    ∃ a d : (𝔸)ˣ, (a : 𝔸) = (h : Matrix (Fin 2) (Fin 2) 𝔸) 0 0 ∧ (d : 𝔸) = (h : Matrix (Fin 2) (Fin 2) 𝔸) 1 1 ∧
      h = centralScalar (𝓞 L) L d * AdelicLevel.diagOne (a * d⁻¹) ∧
      adelicWeyl (𝓞 L) L * h = centralScalar (𝓞 L) L a * AdelicLevel.diagOne (d * a⁻¹) * adelicWeyl (𝓞 L) L := by
  have hdet : IsUnit ((h : Matrix (Fin 2) (Fin 2) 𝔸).det) := Matrix.isUnits_det_units h
  rw [Matrix.det_fin_two, hh10, hh01, mul_zero, sub_zero] at hdet
  obtain ⟨a, ha⟩ := isUnit_of_mul_isUnit_left hdet
  obtain ⟨d, hd⟩ := isUnit_of_mul_isUnit_right hdet
  refine ⟨a, d, ha, hd, Units.ext ?_, Units.ext ?_⟩
  · ext i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, centralScalar_apply, centralScalar_apply,
      diagOne_apply, diagOne_apply]
    fin_cases i <;> fin_cases j
    · simp [← ha]; rw [mul_left_comm, Units.mul_inv, mul_one]
    · simp [hh01]
    · simp [hh10]
    · simp [← hd]
  · ext i j
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [adelicWeyl_apply, centralScalar_apply, diagOne_apply]
    fin_cases i <;> fin_cases j <;> simp [hh10, hh01, ← ha, ← hd]
    all_goals rw [mul_left_comm, Units.mul_inv, mul_one]

theorem ideleNorm_one : TateGlobal.ideleNorm L (1 : (𝔸)ˣ) = 1 := by
  simp [TateGlobal.ideleNorm]

theorem weight_diag_mul {h : AdelicGL2 (𝓞 L) L}
    (hh10 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0) (hh01 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = 0)
    (y : AdelicGL2 (𝓞 L) L) :
    (-Real.log (AdelicHeight.adelicHeight L (h * y))
        - Real.log (AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * (h * y)))) =
      (-Real.log (AdelicHeight.adelicHeight L y)
        - Real.log (AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * y))) := by
  obtain ⟨a, d, -, -, hdec, hweyl⟩ := exists_eq_centralScalar_mul_diagOne L hh10 hh01
  have hcs := (AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2
  have e1 : AdelicHeight.adelicHeight L (h * y) =
      TateGlobal.ideleNorm L (a * d⁻¹) * AdelicHeight.adelicHeight L y := by
    rw [hdec, mul_assoc, hcs, AdelicHeight.adelicHeight_diagOne_mul]
  have e2 : AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * (h * y)) =
      TateGlobal.ideleNorm L (d * a⁻¹) * AdelicHeight.adelicHeight L (adelicWeyl (𝓞 L) L * y) := by
    rw [← mul_assoc, hweyl, mul_assoc, mul_assoc, hcs, AdelicHeight.adelicHeight_diagOne_mul]
  have hN : TateGlobal.ideleNorm L (a * d⁻¹) * TateGlobal.ideleNorm L (d * a⁻¹) = 1 := by
    rw [← TateGlobal.ideleNorm_mul, show a * d⁻¹ * (d * a⁻¹) = 1 by group, ideleNorm_one]
  have h1 := TateGlobal.ideleNorm_pos (F := L) (a * d⁻¹)
  have h2 := TateGlobal.ideleNorm_pos (F := L) (d * a⁻¹)
  have hy := AdelicHeight.adelicHeight_pos (F := L) y
  have hwy := AdelicHeight.adelicHeight_pos (F := L) (adelicWeyl (𝓞 L) L * y)
  rw [e1, e2, Real.log_mul h1.ne' hy.ne', Real.log_mul h2.ne' hwy.ne']
  have hlog : Real.log (TateGlobal.ideleNorm L (a * d⁻¹)) + Real.log (TateGlobal.ideleNorm L (d * a⁻¹)) = 0 := by
    rw [← Real.log_mul h1.ne' h2.ne', hN, Real.log_one]
  linarith

end Adelic

section Transl

set_option linter.unusedSectionVars false

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (σ : L ≃ₐ[K] L)

def sigmaV (v : HeightOneSpectrum (𝓞 K)) : L ⊗[K] v.adicCompletion K →+* L ⊗[K] v.adicCompletion K :=
  (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom

theorem sigmaV_apply (v : HeightOneSpectrum (𝓞 K)) (x : L ⊗[K] v.adicCompletion K) :
    sigmaV K L σ v x =
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) x := rfl

theorem sigmaV_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K)) {x : L ⊗[K] v.adicCompletion K}
    (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) : sigmaV K L σ v x ∈ AutomorphicForm.semiLocalIntegers K L v := by
  obtain ⟨t, rfl⟩ := hx
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact AutomorphicForm.zero_mem_semiLocalIntegers K L v
  | tmul b y =>
    refine ⟨(galRestrict (𝓞 K) K L (𝓞 L) σ b) ⊗ₜ y, ?_⟩
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul,
      algebraMap_galRestrict_apply, sigmaV_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    rfl
  | add s t hs ht =>
    obtain ⟨s', hs'⟩ := hs
    obtain ⟨t', ht'⟩ := ht
    exact ⟨s' + t', by rw [map_add, map_add, map_add, hs', ht']⟩

theorem map_sigmaV_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K))
    {k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)} (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    Matrix.GeneralLinearGroup.map (sigmaV K L σ v) k ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet] at hk ⊢
  refine ⟨fun i j => sigmaV_mem_semiLocalIntegers K L σ v (hk.1 i j), fun i j => ?_⟩
  rw [← map_inv]
  exact sigmaV_mem_semiLocalIntegers K L σ v (hk.2 i j)

variable [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem semiLocalComponent_sigmaAdelicAct (v : HeightOneSpectrum (𝓞 K)) (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) =
      Matrix.GeneralLinearGroup.map (sigmaV K L σ v)
        (AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact (AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
    K L D σ v).2.2 g i j

theorem glArch_sigmaAdelicAct_eq_one {g : AutomorphicForm.AdelicGL2 (𝓞 L) L}
    (hg : AdelicLevel.glArch (𝓞 L) L g = 1) :
    AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) = 1 := by
  obtain ⟨A, B, -, -, hAB⟩ := M4aHerbrand.IdeleGaloisDescent.exists_ringEquiv_prod_forall_act_eq K L D σ
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1) =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j := by
    rw [← AdelicLevel.glArch_apply, hg]; rfl
  rw [Units.val_one, AdelicLevel.glArch_apply, sigmaAdelicAct_apply, hAB]
  show A (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1) = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j
  rw [h1]
  by_cases hij : i = j
  · subst hij; rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, map_zero]

variable (S T : Finset (HeightOneSpectrum (𝓞 K))) [DecidableEq (HeightOneSpectrum (𝓞 K))]

theorem apply_mul_sigmaAdelicAct_eq
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hfact : AutomorphicForm.IsSemiLocalFactorization K L (S ∪ T) φ φa φf ψ)
    (hψ : ∀ v ∈ T, ∀ (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ k ∈ AutomorphicForm.semiLocalIntegralSet K L v,
      ψ v (x * k) = ψ v x)
    {g : AutomorphicForm.AdelicGL2 (𝓞 L) L} (hg1 : AdelicLevel.glArch (𝓞 L) L g = 1)
    (hg2 : AdelicLevel.glFin (𝓞 L) L g ∈ AdelicLevel.finiteIntegralGL2 (𝓞 L) L)
    (hg3 : ∀ v ∉ T, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) = 1)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    φ (x * AutomorphicForm.sigmaAdelicAct K L D σ g) = φ x := by
  obtain ⟨-, -, -, h4, h5, h6⟩ := hfact
  set G' := AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g) with hG'

  have hgint : ∀ v, AutomorphicForm.semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L g) ∈
      AutomorphicForm.semiLocalIntegralSet K L v := fun v =>
    (mem_unitsOutside_iff_semiLocal.mp (finiteIntegralGL2_le_unitsOutside K L (∅ : Finset _) hg2)) v
      (Finset.notMem_empty v)
  have hG'int : ∀ v, AutomorphicForm.semiLocalComponent K L v G' ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
    intro v; rw [hG', semiLocalComponent_sigmaAdelicAct]; exact map_sigmaV_mem_semiLocalIntegralSet K L σ v (hgint v)
  have hG'T : ∀ v ∉ T, AutomorphicForm.semiLocalComponent K L v G' = 1 := by
    intro v hv; rw [hG', semiLocalComponent_sigmaAdelicAct, hg3 v hv, map_one]
  rw [h6, h6, map_mul, glArch_sigmaAdelicAct_eq_one K L σ D hg1, mul_one, map_mul]
  congr 1
  set h := AdelicLevel.glFin (𝓞 L) L x with hh
  show φf (h * G') = φf h
  by_cases hE : ∀ v ∉ S ∪ T, AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v
  · have hE' : ∀ v ∉ S ∪ T, AutomorphicForm.semiLocalComponent K L v (h * G') ∈
        AutomorphicForm.semiLocalIntegralSet K L v := by
      intro v hv; rw [map_mul, hG'T v (fun h' => hv (Finset.mem_union_right S h'))]; rw [mul_one]; exact hE v hv
    rw [h4 _ hE', h4 _ hE]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [map_mul]
    by_cases hvT : v ∈ T
    · exact hψ v hvT _ _ (hG'int v)
    · rw [hG'T v hvT, mul_one]
  · have hE' : ¬ ∀ v ∉ S ∪ T, AutomorphicForm.semiLocalComponent K L v (h * G') ∈
        AutomorphicForm.semiLocalIntegralSet K L v := by
      intro hcon; apply hE; intro v hv
      have := hcon v hv
      rw [map_mul, hG'T v (fun h' => hv (Finset.mem_union_right S h')), mul_one] at this
      exact this
    push Not at hE hE'
    rw [h5 _ hE', h5 _ hE]

end Transl

section Inv

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure]

local notation "𝔸" => AdeleRing (𝓞 L) L

theorem lintegral_mul_left_eq (ψ : AdelicGL2 (𝓞 L) L → ℂ) {t : GL (Fin 2) L}
    (ht10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    {h : AdelicGL2 (𝓞 L) L}
    (hh10 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0) (hh01 : (h : Matrix (Fin 2) (Fin 2) 𝔸) 0 1 = 0)
    (hcen : sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)) (y : AdelicGL2 (𝓞 L) L) :
    (∫⁻ z, ENNReal.ofReal ‖ψ ((h * y)⁻¹ * globalPoints (𝓞 L) L t *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (h * y)))‖ ∂νZL) =
      ∫⁻ z, ENNReal.ofReal ‖ψ (y⁻¹ * globalPoints (𝓞 L) L t *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y))‖ ∂νZL := by
  obtain ⟨u, hu⟩ := exists_idele_forall_conj_eq K L D σ hh10 hh01 hcen t ht10 ht01
  simp_rw [hu y]
  exact lintegral_mul_left_eq_self (fun z : (𝔸)ˣ => ENNReal.ofReal ‖ψ (y⁻¹ * globalPoints (𝓞 L) L t *
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y))‖) u

end Inv

section Final

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_adelicGL2 : SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 L) L))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

end Final

end TranslGlue

end

open AutomorphicForm

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K)))
      (ψ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
      (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ φa φf ψ →
      (∀ v ∈ T, ∀ (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ k ∈ semiLocalIntegralSet K L v,
          ψ v (x * k) = ψ v x) →
      ∀ (g : AdelicGL2 (𝓞 L) L),
        NumberField.AdelicLevel.glArch (𝓞 L) L g = 1 →
        NumberField.AdelicLevel.glFin (𝓞 L) L g ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L →
        (∀ v ∉ T, semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L g) = 1) →
      ∀ t ∈ Δ,
        (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖(fun x => φ (g⁻¹ * x)) (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) =
          (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ∧
        (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖(fun x => φ (g⁻¹ * x)) (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) =
          (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) := by
  intro T ψ φ φf hfact hψ g hg1 hg2 hg3 t ht
  classical
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := TranslGlue.secondCountableTopology_adelicGL2 L
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar L
  obtain ⟨ht10, ht01, -⟩ := hΔd t ht
  have hinv : ∀ x, φ (x * sigmaAdelicAct K L D σ g) = φ x :=
    TranslGlue.apply_mul_sigmaAdelicAct_eq K L σ D S T φ φa φf ψ hfact hψ hg1 hg2 hg3

  have hZ : ∀ y : AdelicGL2 (𝓞 L) L,
      (∫⁻ z, ENNReal.ofReal ‖(fun x => φ (g⁻¹ * x)) ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y)))‖ ∂νZL) =
        (∫⁻ z, ENNReal.ofReal ‖φ ((y * g)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y * g)))‖ ∂νZL) := by
    intro y
    refine lintegral_congr fun z => ?_
    dsimp only
    rw [← hinv (g⁻¹ * (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)))]
    congr 1
    rw [show AutomorphicForm.centralScalar (𝓞 L) L z * (y * g) = AutomorphicForm.centralScalar (𝓞 L) L z * y * g
      from (mul_assoc _ _ _).symm, map_mul (AutomorphicForm.sigmaAdelicAct K L D σ) _ g]
    group

  have hgK : g ∈ AutomorphicForm.adelicMaximalCompact L := by
    refine AutomorphicForm.mem_adelicMaximalCompact_iff.mpr ⟨hg2, fun w => ?_⟩
    have h1 := (AutomorphicForm.mem_adelicMaximalCompact_iff.mp (AutomorphicForm.adelicMaximalCompact L).one_mem).2 w
    rw [hg1]
    rwa [map_one] at h1
  have hW : ∀ y : AdelicGL2 (𝓞 L) L,
      ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (y * g))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (y * g))))| =
      ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L y)
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))| := by
    intro y
    rw [← mul_assoc, NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact L y g hgK,
      NumberField.AdelicHeight.adelicHeight_mul_of_mem_adelicMaximalCompact L _ g hgK]

  have hZinv : ∀ x ∈ H, ∀ y : AdelicGL2 (𝓞 L) L,
      (∫⁻ z, ENNReal.ofReal ‖φ ((x * y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (x * y)))‖ ∂νZL) =
      (∫⁻ z, ENNReal.ofReal ‖φ ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y)))‖ ∂νZL) := by
    intro x hx y
    obtain ⟨hx10, hx01, hcen⟩ := (hH x).mp hx
    exact TranslGlue.lintegral_mul_left_eq K L D σ νZL φ ht10 ht01 hx10 hx01 hcen y
  have hWinv : ∀ x ∈ H, ∀ y : AdelicGL2 (𝓞 L) L,
      ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (x * y))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (x * y))))| =
      ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L y)
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))| := by
    intro x hx y
    obtain ⟨hx10, hx01, -⟩ := (hH x).mp hx
    rw [TranslGlue.weight_diag_mul L hx10 hx01 y]
  refine ⟨?_, ?_⟩
  · refine (lintegral_congr fun q => hZ _).trans ?_
    exact HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq (adelicGLHaar (Fin 2) (𝓞 L) L) H hHc μH
      (fun y : AdelicGL2 (𝓞 L) L => (∫⁻ z, ENNReal.ofReal ‖φ ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y)))‖ ∂νZL))
      hZinv g (map_mul_right_eq_self _ g)
  · calc (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖(fun x => φ (g⁻¹ * x)) (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH))
        = ∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (fun y : AdelicGL2 (𝓞 L) L => ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L y)
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))| * (∫⁻ z, ENNReal.ofReal ‖φ ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y)))‖ ∂νZL)) ((q.out : AdelicGL2 (𝓞 L) L) * g)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by
          refine lintegral_congr fun q => ?_
          dsimp only
          rw [hW, hZ]
      _ = ∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
            (fun y : AdelicGL2 (𝓞 L) L => ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L y)
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))| * (∫⁻ z, ENNReal.ofReal ‖φ ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y)))‖ ∂νZL)) (q.out : AdelicGL2 (𝓞 L) L)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) :=
          HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq (adelicGLHaar (Fin 2) (𝓞 L) L) H hHc μH
            (fun y : AdelicGL2 (𝓞 L) L => ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L y)
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))| * (∫⁻ z, ENNReal.ofReal ‖φ ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y)))‖ ∂νZL))
            (fun x hx y => by rw [hZinv x hx y, hWinv x hx y]) g (map_mul_right_eq_self _ g)

end S_AutomorphicForm_lintegral_orbital_comp_inv_mul_eq_and_weightedOrbital_eq_of_glArch_eq_one_of_isSemiLocalFactorization
end P2MW
export P2MW.S_AutomorphicForm_lintegral_orbital_comp_inv_mul_eq_and_weightedOrbital_eq_of_glArch_eq_one_of_isSemiLocalFactorization (solution)
