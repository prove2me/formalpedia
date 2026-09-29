-- Prove2me | solution 1 for AutomorphicForm.exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/526f39ac-fefe-544e-9919-c7fc304072a1

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate

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

namespace ExGlue

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

section DoubleCoset

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem isSemiLocalTestFn_indicator_doubleCoset (a : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.IsSemiLocalTestFn K L v (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
      (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v).indicator
        (fun _ => (1 : ℂ)) x) := by
  haveI hG := AutomorphicForm.isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (v.adicCompletion K)
  have hK := AutomorphicForm.isCompact_semiLocalIntegralSet K L v
  have hc : IsCompact (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
      AutomorphicForm.semiLocalIntegralSet K L v) := (hK.mul isCompact_singleton).mul hK
  have ho : IsOpen (AutomorphicForm.semiLocalIntegralSet K L v * {a} *
      AutomorphicForm.semiLocalIntegralSet K L v) :=
    (AutomorphicForm.isOpen_semiLocalIntegralSet K L v).mul_left
  exact ⟨AutomorphicForm.isLocallyConstant_indicator_one ho hc.isClosed,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

end DoubleCoset

end ExGlue

end

open AutomorphicForm

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ρ : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hφ : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
            else φS v)) :
    ∃ (φ' : AdelicGL2 (𝓞 L) L → ℂ) (φf' : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsSemiLocalFactorization K L (S ∪ T) φ' φa φf'
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) := by
  obtain ⟨hφa, -, hΨ, -, -, -⟩ := hφ
  have hΨ' : ∀ v ∈ S ∪ T, IsSemiLocalTestFn K L v
      ((fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) v) := by
    intro v hv
    by_cases hvT : v ∈ T
    · show IsSemiLocalTestFn K L v (if v ∈ T then _ else _)
      rw [if_pos hvT]
      exact ExGlue.isSemiLocalTestFn_indicator_doubleCoset K L v _
    · have := hΨ v hv
      have e : (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))⁻¹ * x)
            else φS v) v = φS v := if_neg hvT
      rw [e] at this
      show IsSemiLocalTestFn K L v (if v ∈ T then _ else _)
      rwa [if_neg hvT]
  refine ⟨fun g => φa (AdelicLevel.glArch (𝓞 L) L g) *
      ExGlue.gluedAbove K L (S ∪ T) (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v) (AdelicLevel.glFin (𝓞 L) L g),
    ExGlue.gluedAbove K L (S ∪ T) (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
              (semiLocalIntegralSet K L v * {(semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1 (ρ v)))} *
                  semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) x
            else φS v),
    hφa, ExGlue.isFinTestFactor_gluedAbove hΨ', hΨ', ?_, ?_, fun g => rfl⟩
  · intro h hint
    exact ExGlue.gluedAbove_of_mem (ExGlue.mem_unitsOutside_iff_semiLocal.mpr hint)
  · intro h hnot
    refine ExGlue.gluedAbove_of_not_mem fun hmem => ?_
    obtain ⟨v, hv, hnv⟩ := hnot
    exact hnv (ExGlue.mem_unitsOutside_iff_semiLocal.mp hmem v hv)

end S_AutomorphicForm_exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate
end P2MW
export P2MW.S_AutomorphicForm_exists_isSemiLocalFactorization_indicator_doubleCoset_of_isSemiLocalFactorization_indicator_translate (solution)
