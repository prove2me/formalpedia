-- Prove2me | solution 1 for AutomorphicForm.sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3a0fd9d8-a9b1-5147-b658-eb92df80995e

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
import Theorems.Thm_AutomorphicForm_exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet
import Theorems.Thm_AutomorphicForm_exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card
import Theorems.Thm_AutomorphicForm_lintegral_orbital_comp_inv_mul_eq_and_weightedOrbital_eq_of_glArch_eq_one_of_isSemiLocalFactorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

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

namespace AvgGlue

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

section Kgroup

set_option linter.unusedSectionVars false

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def semiLocalIntegersSubring : Subring (L ⊗[K] v.adicCompletion K) :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).toRingHom.range

theorem coe_semiLocalIntegersSubring :
    (semiLocalIntegersSubring K L v : Set (L ⊗[K] v.adicCompletion K)) = AutomorphicForm.semiLocalIntegers K L v := by
  ext x
  simp only [semiLocalIntegersSubring, AutomorphicForm.semiLocalIntegers, Set.mem_range, SetLike.mem_coe,
    RingHom.mem_range]
  exact Iff.rfl

theorem mul_mem_semiLocalIntegralSet {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) (hh : h ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    g * h ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
  unfold AutomorphicForm.semiLocalIntegralSet at *
  rw [← coe_semiLocalIntegersSubring] at *
  exact mul_mem_integralUnitsSet _ hg hh

theorem inv_mem_semiLocalIntegralSet {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ AutomorphicForm.semiLocalIntegralSet K L v) : g⁻¹ ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
  inv_mem_integralUnitsSet _ hg

theorem indicator_inv_mul_mul_eq (a x : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    {k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)} (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (a⁻¹ * (x * k)) =
      (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (a⁻¹ * x) := by
  by_cases hx : a⁻¹ * x ∈ AutomorphicForm.semiLocalIntegralSet K L v
  · have : a⁻¹ * (x * k) ∈ AutomorphicForm.semiLocalIntegralSet K L v := by
      rw [← mul_assoc]; exact mul_mem_semiLocalIntegralSet K L v hx hk
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem this]
  · have : a⁻¹ * (x * k) ∉ AutomorphicForm.semiLocalIntegralSet K L v := by
      intro h
      apply hx
      have := mul_mem_semiLocalIntegralSet K L v h (inv_mem_semiLocalIntegralSet K L v hk)
      rwa [← mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this]

end Kgroup

section Generic

theorem list_prod_map_eq_of_forall_ne {α M : Type*} [Monoid M] [DecidableEq α] :
    ∀ (l : List α), l.Nodup → ∀ (x₀ : α), x₀ ∈ l → ∀ (f : α → M), (∀ x ∈ l, x ≠ x₀ → f x = 1) →
      (l.map f).prod = f x₀
  | [], _, x₀, hx, _, _ => absurd hx (by simp)
  | (a :: l), hl, x₀, hx, f, hf => by
    rw [List.map_cons, List.prod_cons]
    rw [List.nodup_cons] at hl
    by_cases ha : a = x₀
    · subst ha
      have : (l.map f).prod = 1 := List.prod_eq_one fun y hy => by
        obtain ⟨x, hxl, rfl⟩ := List.mem_map.mp hy
        exact hf x (List.mem_cons_of_mem _ hxl) fun h => hl.1 (h ▸ hxl)
      rw [this, mul_one]
    · have hx' : x₀ ∈ l := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm ha
        · exact h
      rw [hf a (by simp) ha, one_mul]
      exact list_prod_map_eq_of_forall_ne l hl.2 x₀ hx' f fun x hxl => hf x (List.mem_cons_of_mem _ hxl)

theorem list_prod_map_eq_one {α M : Type*} [Monoid M] (l : List α) (f : α → M) (hf : ∀ x ∈ l, f x = 1) :
    (l.map f).prod = 1 :=
  List.prod_eq_one fun y hy => by
    obtain ⟨x, hxl, rfl⟩ := List.mem_map.mp hy
    exact hf x hxl

theorem sum_indicator_eq_indicator_iUnion {X : Type*} {m : ℕ} (s : Fin m → Set X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j)) (x : X) :
    ∑ i, (s i).indicator (fun _ => (1 : ℂ)) x = (⋃ i, s i).indicator (fun _ => (1 : ℂ)) x := by
  classical
  by_cases hx : x ∈ ⋃ i, s i
  · rw [Set.indicator_of_mem hx]
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · exact Set.indicator_of_mem hi _
    · intro j _ hji
      exact Set.indicator_of_notMem (Set.disjoint_left.mp (hdisj i j (Ne.symm hji)) hi) _
  · rw [Set.indicator_of_notMem hx]
    refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (fun hi => hx (Set.mem_iUnion.mpr ⟨i, hi⟩)) _

open scoped ENNReal in

theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc (∫⁻ x, f a x ∂μ) + ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ (∫⁻ x, f a x ∂μ) + ∫⁻ x, ∑ i ∈ s, f i x ∂μ :=
          add_le_add_right ih _
      _ ≤ ∫⁻ x, (f a x + ∑ i ∈ s, f i x) ∂μ := le_lintegral_add _ _
      _ = ∫⁻ x, ∑ i ∈ insert a s, f i x ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [Finset.sum_insert ha]

end Generic

section Pointwise

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [DecidableEq (HeightOneSpectrum (𝓞 K))]

open AutomorphicForm

theorem norm_eq_re_of_zero_or_one {z : ℂ} (h : z = 0 ∨ z = 1) : ‖z‖ = z.re := by
  rcases h with rfl | rfl <;> simp

theorem indicator_zero_or_one {X : Type*} (s : Set X) (x : X) :
    s.indicator (fun _ => (1 : ℂ)) x = 0 ∨ s.indicator (fun _ => (1 : ℂ)) x = 1 := by
  by_cases hx : x ∈ s
  · exact Or.inr (Set.indicator_of_mem hx _)
  · exact Or.inl (Set.indicator_of_notMem hx _)

theorem prod_zero_or_one {ι : Type*} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1) :
    (∏ i ∈ s, f i) = 0 ∨ (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rcases hf a (Finset.mem_insert_self a s) with h | h
    · left; rw [h, zero_mul]
    · rw [h, one_mul]; exact ih fun i hi => hf i (Finset.mem_insert_of_mem hi)

theorem sum_ofReal_norm_mul_eq {ι : Type*} [Fintype ι] (c : ℂ) (P : ι → ℂ) (hP : ∀ p, P p = 0 ∨ P p = 1)
    (D : ℂ) (hD : D = 0 ∨ D = 1) (hsum : ∑ p, P p = D) :
    ∑ p, ENNReal.ofReal ‖c * P p‖ = ENNReal.ofReal ‖c * D‖ := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => norm_nonneg _)]
  congr 1
  simp_rw [norm_mul]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [norm_eq_re_of_zero_or_one (hP _), norm_eq_re_of_zero_or_one hD, ← hsum, Complex.re_sum]

end Pointwise

section Bookkeeping

open scoped ENNReal

theorem sum_lintegral_lintegral_le {Q Z ι : Type*} [MeasurableSpace Q] [MeasurableSpace Z] (μ : Measure Q)
    (ν : Measure Z) (s : Finset ι) (f : ι → Q → Z → ℝ≥0∞) (g : Q → Z → ℝ≥0∞)
    (hfg : ∀ q z, g q z = ∑ i ∈ s, f i q z) :
    ∑ i ∈ s, ∫⁻ q, ∫⁻ z, f i q z ∂ν ∂μ ≤ ∫⁻ q, ∫⁻ z, g q z ∂ν ∂μ := by
  calc ∑ i ∈ s, ∫⁻ q, ∫⁻ z, f i q z ∂ν ∂μ ≤ ∫⁻ q, ∑ i ∈ s, ∫⁻ z, f i q z ∂ν ∂μ := sum_lintegral_le μ s _
    _ ≤ ∫⁻ q, ∫⁻ z, ∑ i ∈ s, f i q z ∂ν ∂μ := lintegral_mono fun q => sum_lintegral_le ν s _
    _ = ∫⁻ q, ∫⁻ z, g q z ∂ν ∂μ := by
        refine lintegral_congr fun q => lintegral_congr fun z => (hfg q z).symm

theorem sum_lintegral_mul_lintegral_le {Q Z ι : Type*} [MeasurableSpace Q] [MeasurableSpace Z] (μ : Measure Q)
    (ν : Measure Z) (s : Finset ι) (f : ι → Q → Z → ℝ≥0∞) (g : Q → Z → ℝ≥0∞)
    (hfg : ∀ q z, g q z = ∑ i ∈ s, f i q z) (w : Q → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ q, w q * ∫⁻ z, f i q z ∂ν ∂μ ≤ ∫⁻ q, w q * ∫⁻ z, g q z ∂ν ∂μ := by
  calc ∑ i ∈ s, ∫⁻ q, w q * ∫⁻ z, f i q z ∂ν ∂μ ≤ ∫⁻ q, ∑ i ∈ s, w q * ∫⁻ z, f i q z ∂ν ∂μ :=
        sum_lintegral_le μ s _
    _ = ∫⁻ q, w q * ∑ i ∈ s, ∫⁻ z, f i q z ∂ν ∂μ := lintegral_congr fun q => (Finset.mul_sum _ _ _).symm
    _ ≤ ∫⁻ q, w q * ∫⁻ z, ∑ i ∈ s, f i q z ∂ν ∂μ :=
        lintegral_mono fun q => mul_le_mul_right (sum_lintegral_le ν s _) _
    _ = ∫⁻ q, w q * ∫⁻ z, g q z ∂ν ∂μ := by
        refine lintegral_congr fun q => ?_
        rw [lintegral_congr fun z => (hfg q z).symm]

theorem sum_mul_card_le {ι J : Type*} [Fintype J] (s : Finset ι) (A B A' B' : ι → ℝ≥0∞) (Aj Bj : ι → J → ℝ≥0∞)
    (hA : ∀ t ∈ s, ∑ j, Aj t j ≤ A' t) (hB : ∀ t ∈ s, ∑ j, Bj t j ≤ B' t)
    (hAj : ∀ t ∈ s, ∀ j, Aj t j = A t) (hBj : ∀ t ∈ s, ∀ j, Bj t j = B t) (M : ℝ≥0∞)
    (hM : M = Fintype.card J) :
    (∑ t ∈ s, (A t + B t)) * M ≤ ∑ t ∈ s, (A' t + B' t) := by
  rw [hM, Finset.sum_mul]
  refine Finset.sum_le_sum fun t ht => ?_
  have eA : ∑ j, Aj t j = Fintype.card J * A t := by
    rw [Finset.sum_congr rfl fun j _ => hAj t ht j, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have eB : ∑ j, Bj t j = Fintype.card J * B t := by
    rw [Finset.sum_congr rfl fun j _ => hBj t ht j, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (A t + B t) * Fintype.card J = ∑ j, Aj t j + ∑ j, Bj t j := by rw [eA, eB]; ring
    _ ≤ A' t + B' t := add_le_add (hA t ht) (hB t ht)

theorem indicator_smul_smul {G : Type*} [Group G] (k a x : G) (s : Set G) :
    (k • (a • s)).indicator (fun _ => (1 : ℂ)) x = s.indicator (fun _ => (1 : ℂ)) (a⁻¹ * (k⁻¹ * x)) := by
  classical
  simp only [Set.indicator_apply, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

end Bookkeeping

namespace TranslatesGlueLite
theorem prod_union_ite {α β : Type*} [CommMonoid β] [DecidableEq α] (S T : Finset α) (X Y : α → β) :
    ∏ v ∈ S ∪ T, (if v ∈ T then X v else Y v) = (∏ v ∈ S \ T, Y v) * ∏ v ∈ T, X v := by
  rw [← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_neg (Finset.mem_sdiff.mp hv).2
  · exact Finset.prod_congr rfl fun v hv => if_pos hv
end TranslatesGlueLite

end AvgGlue

end

open AutomorphicForm AvgGlue

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
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
      (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
      (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ φa φf
        (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
          else φS v) →
    ∀ (φ' : AdelicGL2 (𝓞 L) L → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ' φa φf'
        (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} * semiLocalIntegralSet K L v).indicator
              (fun _ => (1 : ℂ)) x
          else φS v) →
    ∀ (Δφ : Finset (GL (Fin 2) L)), (↑Δφ ⊆ Δ) →
      (∑ t ∈ Δφ,
          ((∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) +
           (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))) *
        (∏ v ∈ T, AutomorphicForm.semiLocalHaar K L v
          (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} * semiLocalIntegralSet K L v)) ≤
      (∑ t ∈ Δφ,
          ((∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              (∫⁻ z, ENNReal.ofReal ‖φ' (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) +
           (∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ENNReal.ofReal |(-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))))| *
              (∫⁻ z, ENNReal.ofReal ‖φ' (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L))))‖ ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)))) := by
  intro T ws ρ φ φf hfact φ' φf' hfact' Δφ hΔφ
  classical

  have hC := fun v : HeightOneSpectrum (𝓞 K) =>
    AutomorphicForm.exists_doubleCoset_semiLocalIntegralSet_eq_iUnion_smul_and_semiLocalHaar_eq_card K L v
      (semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))
  choose m k hk using hC
  have hKp := fun (v : HeightOneSpectrum (𝓞 K)) (i : Fin (m v)) =>
    AutomorphicForm.exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet K L v (k v i)
      ((hk v).1 i)
  choose gl hgl using hKp
  set LT : List ↥T := (Finset.univ : Finset ↥T).toList with hLT
  have hLTnd : LT.Nodup := Finset.nodup_toList _
  have hLTmem : ∀ v : ↥T, v ∈ LT := fun v => Finset.mem_toList.mpr (Finset.mem_univ v)
  let gp : ((v : ↥T) → Fin (m v)) → AdelicGL2 (𝓞 L) L := fun p => (LT.map fun v : ↥T => gl v (p v)).prod
  have hg1 : ∀ p, AdelicLevel.glArch (𝓞 L) L (gp p) = 1 := fun p => by
    show AdelicLevel.glArch (𝓞 L) L (LT.map fun v : ↥T => gl v (p v)).prod = 1
    rw [map_list_prod, List.map_map]
    exact list_prod_map_eq_one _ _ fun v _ => (hgl v (p v)).1
  have hg2 : ∀ p, AdelicLevel.glFin (𝓞 L) L (gp p) ∈ AdelicLevel.finiteIntegralGL2 (𝓞 L) L := fun p => by
    show AdelicLevel.glFin (𝓞 L) L (LT.map fun v : ↥T => gl v (p v)).prod ∈ _
    rw [map_list_prod, List.map_map]
    exact Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      exact (hgl v (p v)).2.1
  have hg3 : ∀ p, ∀ v ∉ T, semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (gp p)) = 1 := fun p v hv => by
    show semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (LT.map fun w : ↥T => gl w (p w)).prod) = 1
    rw [map_list_prod, List.map_map, map_list_prod, List.map_map]
    exact list_prod_map_eq_one _ _ fun w _ => (hgl w (p w)).2.2.2 v fun h => hv (by rw [h]; exact w.2)
  have hg4 : ∀ p (v : ↥T), semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (gp p)) = k v (p v) :=
    fun p v => by
    show semiLocalComponent K L v (AdelicLevel.glFin (𝓞 L) L (LT.map fun w : ↥T => gl w (p w)).prod) = _
    rw [map_list_prod, List.map_map, map_list_prod, List.map_map]
    exact (list_prod_map_eq_of_forall_ne LT hLTnd v (hLTmem v) _ fun w _ hw =>
      (hgl w (p w)).2.2.2 v fun h => hw (Subtype.ext h.symm)).trans (hgl v (p v)).2.2.1

  have hinvU : ∀ v ∈ T, ∀ (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)), ∀ k' ∈ semiLocalIntegralSet K L v,
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
          else φS v) v (x * k') =
      (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
          else φS v) v x := by
    intro v hv x k' hk'
    dsimp only
    rw [if_pos hv]
    exact indicator_inv_mul_mul_eq K L v _ x hk'

  have hT := fun p : ((v : ↥T) → Fin (m v)) =>
    AutomorphicForm.lintegral_orbital_comp_inv_mul_eq_and_weightedOrbital_eq_of_glArch_eq_one_of_isSemiLocalFactorization
      K L νZL D σ hgen S φa φS H hHc hH μH Δ hΔd hΔdisj T _ φ φf hfact hinvU (gp p) (hg1 p) (hg2 p) (hg3 p)

  have hpt : ∀ X : AdelicGL2 (𝓞 L) L,
      ENNReal.ofReal ‖φ' X‖ = ∑ p : ((v : ↥T) → Fin (m v)), ENNReal.ofReal ‖φ ((gp p)⁻¹ * X)‖ := by
    intro X
    obtain ⟨-, -, -, h4, h5, h6⟩ := hfact
    obtain ⟨-, -, -, h4', h5', h6'⟩ := hfact'
    have eφ : ∀ p, φ ((gp p)⁻¹ * X) = φa (AdelicLevel.glArch (𝓞 L) L X) *
        φf ((AdelicLevel.glFin (𝓞 L) L (gp p))⁻¹ * AdelicLevel.glFin (𝓞 L) L X) := by
      intro p; rw [h6, map_mul, map_inv, hg1, inv_one, one_mul, map_mul, map_inv]
    rw [h6' X]
    simp_rw [eφ]
    set h := AdelicLevel.glFin (𝓞 L) L X with hh
    by_cases hE : h ∈ unitsOutside K L (S ∪ T)
    · have hint : ∀ v ∉ S ∪ T, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v :=
        mem_unitsOutside_iff_semiLocal.mp hE
      have hE' : ∀ p, (AdelicLevel.glFin (𝓞 L) L (gp p))⁻¹ * h ∈ unitsOutside K L (S ∪ T) := fun p =>
        mul_mem (inv_mem (finiteIntegralGL2_le_unitsOutside K L (S ∪ T) (hg2 p))) hE

      set a : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
        fun v => semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)) with ha
      set RR : ℂ := ∏ v ∈ S \ T, φS v (semiLocalComponent K L v h) with hRR
      set b : ∀ v : ↥T, Fin (m v) → ℂ := fun v i =>
        (k v i • (a v • semiLocalIntegralSet K L v)).indicator (fun _ => (1 : ℂ)) (semiLocalComponent K L v h) with hb
      set P : ((v : ↥T) → Fin (m v)) → ℂ := fun p => ∏ v : ↥T, b v (p v) with hP
      set D : ℂ := ∏ v : ↥T, (semiLocalIntegralSet K L v * {a v} * semiLocalIntegralSet K L v).indicator
        (fun _ => (1 : ℂ)) (semiLocalComponent K L v h) with hD
      have eD : φf' h = RR * D := by
        rw [h4' h hint]
        simp only [ite_apply]
        rw [TranslatesGlueLite.prod_union_ite, ← Finset.prod_coe_sort T]
      have eP : ∀ p, φf ((AdelicLevel.glFin (𝓞 L) L (gp p))⁻¹ * h) = RR * P p := by
        intro p
        rw [h4 _ (mem_unitsOutside_iff_semiLocal.mp (hE' p))]
        simp only [ite_apply, map_mul, map_inv]
        rw [TranslatesGlueLite.prod_union_ite, ← Finset.prod_coe_sort T]
        congr 1
        · refine Finset.prod_congr rfl fun v hv => ?_
          rw [hg3 p v (Finset.mem_sdiff.mp hv).2, inv_one, one_mul]
        · refine Finset.prod_congr rfl fun v _ => ?_
          rw [hg4 p v]
          simp only [hb, ha, indicator_smul_smul]
      have hb01 : ∀ (v : ↥T) i, b v i = 0 ∨ b v i = 1 := fun v i => indicator_zero_or_one _ _
      have hP01 : ∀ p, P p = 0 ∨ P p = 1 := fun p => prod_zero_or_one _ _ fun v _ => hb01 v (p v)
      have hD01 : D = 0 ∨ D = 1 := prod_zero_or_one _ _ fun v _ => indicator_zero_or_one _ _
      have hsum : ∑ p, P p = D := by
        rw [hP, hD, ← Fintype.prod_sum]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [(hk v).2.1]
        exact sum_indicator_eq_indicator_iUnion _ (hk v).2.2.1 _
      rw [eD]
      simp_rw [eP, ← mul_assoc]
      exact (sum_ofReal_norm_mul_eq _ P hP01 D hD01 hsum).symm
    · have hnot : ∃ v ∉ S ∪ T, semiLocalComponent K L v h ∉ semiLocalIntegralSet K L v := by
        by_contra hcon
        push Not at hcon
        exact hE (mem_unitsOutside_iff_semiLocal.mpr hcon)
      have hnot' : ∀ p, ∃ v ∉ S ∪ T, semiLocalComponent K L v ((AdelicLevel.glFin (𝓞 L) L (gp p))⁻¹ * h) ∉
          semiLocalIntegralSet K L v := by
        intro p
        by_contra hcon
        push Not at hcon
        have hmem : (AdelicLevel.glFin (𝓞 L) L (gp p))⁻¹ * h ∈ unitsOutside K L (S ∪ T) :=
          mem_unitsOutside_iff_semiLocal.mpr hcon
        have := mul_mem (finiteIntegralGL2_le_unitsOutside K L (S ∪ T) (hg2 p)) hmem
        rw [mul_inv_cancel_left] at this
        exact hE this
      rw [h5' h hnot]
      simp_rw [h5 _ (hnot' _)]
      simp

  have hM : (∏ v ∈ T, AutomorphicForm.semiLocalHaar K L v
        (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} * semiLocalIntegralSet K L v)) =
      Fintype.card ((v : ↥T) → Fin (m v)) := by
    rw [Fintype.card_pi, ← Finset.prod_coe_sort T]
    simp only [Fintype.card_fin, Nat.cast_prod]
    exact Finset.prod_congr rfl fun v _ => (hk v).2.2.2

  refine sum_mul_card_le Δφ _ _ _ _ _ _ (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht p => ((hT p) t (hΔφ ht)).1) (fun t ht p => ((hT p) t (hΔφ ht)).2) _ hM
  · exact sum_lintegral_lintegral_le _ νZL _ _ _ fun q z => hpt _
  · exact sum_lintegral_mul_lintegral_le _ νZL _ _ _ (fun q z => hpt _) _

end S_AutomorphicForm_sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le
end P2MW
export P2MW.S_AutomorphicForm_sum_lintegral_orbital_add_weightedOrbital_indicator_translate_mul_prod_measure_doubleCoset_le (solution)
