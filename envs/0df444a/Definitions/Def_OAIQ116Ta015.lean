-- Prove2me | Definitions.Def_OAIQ116Ta015
-- name    : OAIQ116Ta015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:28:57.544776+00:00
-- url     : https://prove2.me/theorems/e3e3d70b-4ea0-4d4e-af22-4e25370b3c55
-- title:
--   Definitions bundle OAIQ116Ta015 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 33 definitions, 7 instances and 9 theorems. The definitions and types are `OAI.Tachikawa.Construction.XTensorIso`, `OAI.Tachikawa.Construction.XTensorTwistIso`, `OAI.Tachikawa.Construction.XTwistIso`, `OAI.Tachikawa.Construction.simpleResolutionTwist`, `OAI.Tachikawa.Construction.simpleResolutionTwistLift`, `OAI.Tachikawa.Construction.xTensorResolution`, `OAI.Tachikawa.Construction.xTensorTwist`, `OAI.Tachikawa.Construction.xTensorTwistLift`, `OAI.Tachikawa.OuterTensor.homBicomplex`, `OAI.Tachikawa.OuterTensor.homBicomplexEquiv`, `OAI.Tachikawa.OuterTensor.homTotalIso`, `OAI.Tachikawa.OuterTensor.tensorResolution`, `OAI.Tachikawa.OuterTensor.tensorResolutionTwist`, `OAI.Tachikawa.OuterTensor.tensorTwistLift`, `OAI.Tachikawa.TotalDualPairing.comparison`, `OAI.Tachikawa.TotalDualPairing.iso`, `OAI.Tachikawa.Triangular.D₁FreeInclusion`, `OAI.Tachikawa.Triangular.diagonal₀`, `OAI.Tachikawa.Triangular.diagonal₁`, `OAI.Tachikawa.Triangular.downCross`, `OAI.Tachikawa.Triangular.down₀`, `OAI.Tachikawa.Triangular.down₁`, `OAI.Tachikawa.Triangular.regIn₀`, `OAI.Tachikawa.Triangular.regIn₁`, `OAI.Tachikawa.Triangular.regOut₀`, `OAI.Tachikawa.Triangular.regOut₁`, `OAI.Tachikawa.TrivialInduction.inducedResolution`, `OAI.Tachikawa.VectorSplit.homologyIsoH`, `OAI.Tachikawa.VectorSplit.tensorHomologyHomotopyEquiv`, `OAI.Tachikawa.VectorSplit.tensorHomologyIso`, `OAI.Tachikawa.coresolutionCyclesToExt`, `OAI.Tachikawa.coresolutionTwistHom`, `OAI.Tachikawa.resolutionTwistHom`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Cone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Cone.lean), [`Tachikawa_Coresolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Coresolution.lean), [`Tachikawa_DerivedInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/DerivedInduction.lean), [`Tachikawa_DownHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/DownHom.lean), [`Tachikawa_Nakayama`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Nakayama.lean), [`Tachikawa_OuterExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/OuterExt.lean), [`Tachikawa_Socle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Socle.lean), [`Tachikawa_Triangular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Triangular.lean), [`Tachikawa_TwistHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/TwistHom.lean).
--
--   **Imports.** It imports the bundles `OAIQ116Ta010`, `OAIQ116Ta011` and `OAIQ116Ta012` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ116Ta016`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta010
import Definitions.Def_OAIQ116Ta011
import Definitions.Def_OAIQ116Ta012

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorBifunctor _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.VectorSplit.tensorFunctor_linear _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I₁ I₂ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K₁ : HomologicalComplex (ModuleCat k) c₁) (K₂ : HomologicalComplex (ModuleCat k) c₂)
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ (tensorFunctor (k := k)) c]
  [HasMapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c]

def tensorHomologyHomotopyEquiv :
    HomotopyEquiv (mapBifunctor K₁ K₂ (tensorFunctor (k := k)) c)
      (mapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c) :=
  bifunctorHomotopyEquiv _ c (homologyHomotopyEquiv K₁) (homologyHomotopyEquiv K₂)

omit [HasMapBifunctor K₁ K₂ (tensorFunctor (k := k)) c] in
lemma tensorHomology_d (j j' : J) :
    (mapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c).d j j' = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro i₁ i₂ h
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂, Limits.comp_zero]
  simp only [HomologicalComplex₂.d₁, HomologicalComplex₂.d₂,
    Functor.mapBifunctorHomologicalComplex_obj_obj_d_f,
    Functor.mapBifunctorHomologicalComplex_obj_obj_X_d]
  change (ComplexShape.ε₁ c₁ c₂ c (i₁,i₂) •
    ((tensorFunctor (k := k)).map 0).app _ ≫ _) +
    (ComplexShape.ε₂ c₁ c₂ c (i₁,i₂) •
    ((tensorFunctor (k := k)).obj _).map 0 ≫ _) = 0
  dsimp only [homologyComplex,Functor.mapBifunctorHomologicalComplex]
  simp only [Functor.map_zero, Limits.zero_app]
  erw [Limits.zero_comp, Limits.zero_comp]
  have zero_sum (domain codomain : ModuleCat k) (sign₁ sign₂ : ℤˣ) :
      sign₁ • (0 : domain ⟶ codomain) + sign₂ • (0 : domain ⟶ codomain) = 0 := by
    simp only [smul_zero, add_zero]
  exact zero_sum _ _ _ _

def tensorHomologyIso (j : J) :
    (mapBifunctor K₁ K₂ (tensorFunctor (k := k)) c).homology j ≅
      (mapBifunctor (homologyComplex K₁) (homologyComplex K₂) (tensorFunctor (k := k)) c).X j :=
  (tensorHomologyHomotopyEquiv K₁ K₂ c).toHomologyIso j ≪≫
    zeroDifferentialHomologyIso _ (tensorHomology_d K₁ K₂ c) j

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {M N : ModuleCat R} (Q : ProjectiveResolution M)

lemma extMk_zeroDegree_eq_zero (f : Q.complex.X 0 ⟶ N)
    (hf : Q.complex.d 1 0 ≫ f = 0) :
    Q.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  simp only [← Q.extEquivCohomologyClass.apply_eq_iff_eq,
    ProjectiveResolution.extEquivCohomologyClass_extMk,
    ProjectiveResolution.extEquivCohomologyClass_zero, CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by norm_num)]
  have hz := CochainComplex.isZero_of_isStrictlyLE Q.cochainComplex 0 1
  constructor
  · rintro ⟨g,hg⟩
    have hg0 : g = 0 := hz.eq_of_src _ _
    rw [hg0, Limits.comp_zero] at hg
    have h := congrArg (fun h => (Q.cochainComplexXIso (-(0 : ℕ)) 0 rfl).inv ≫ h) hg.symm
    simpa using h
  · intro h
    subst f
    exact ⟨0,by simp⟩

lemma resolutionBoundary_zero :
    VectorSplit.boundary (resolutionHom k R Q.complex N) 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change Q.complex.X ((ComplexShape.up ℕ).prev 0) ⟶ N at x
  change Q.complex.d 0 ((ComplexShape.up ℕ).prev 0) ≫ x = 0
  rw [Q.complex.shape _ _ (by change ¬ _+1=0; omega), Limits.zero_comp]

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : CochainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

lemma coresolutionHom_memZ (n : ℕ) (f : N ⟶ P.X n) :
    f ∈ VectorSplit.Z (coresolutionHom k R P N) n ↔ f ≫ P.d n (n+1) = 0 := by
  change (coresolutionHom k R P N).d n ((ComplexShape.up ℕ).next n) f = 0 ↔ _
  rw [show (ComplexShape.up ℕ).next n = n+1 from (ComplexShape.up ℕ).next_eq' rfl]
  rfl

variable {k R} {M : ModuleCat R} (Q : InjectiveResolution M)

def coresolutionCyclesToExt (n : ℕ) :
    VectorSplit.Z (coresolutionHom k R Q.cocomplex N) n →ₗ[k] Ext N M n where
  toFun z := Q.extMk z.val (n+1) rfl ((coresolutionHom_memZ k R Q.cocomplex N n z.val).mp z.property)
  map_add' x y := (Q.add_extMk x.val y.val (n+1) rfl _ _).symm
  map_smul' r z := injective_extMk_smul N Q z.val
    ((coresolutionHom_memZ k R Q.cocomplex N n z.val).mp z.property) r _
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesInjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : InjectiveResolution X) (e : F.obj X ≅ X)

def coresolutionTwistHom (l : (mappedCoresolution F P).cocomplex ⟶ P.cocomplex) :
    coresolutionHom k R P.cocomplex X ⟶ coresolutionHom k R P.cocomplex X := by
  change (F.mapHomologicalComplex (.up ℕ)).obj P.cocomplex ⟶ P.cocomplex at l
  exact {
  f n := ModuleCat.ofHom
    (show (X ⟶ P.cocomplex.X n) →ₗ[k] (X ⟶ P.cocomplex.X n) from
    { toFun f := e.inv ≫ F.map f ≫ l.f n
      map_add' f g := by rw [F.map_add,Preadditive.add_comp,Preadditive.comp_add]
      map_smul' r f := by rw [F.map_smul,Linear.smul_comp,Linear.comp_smul]; rfl })
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change X ⟶ P.cocomplex.X i at f
    symm
    change e.inv ≫ F.map (f ≫ P.cocomplex.d i j) ≫ l.f j =
      e.inv ≫ F.map f ≫ l.f i ≫ P.cocomplex.d i j
    have hl := l.comm i j
    change l.f i ≫ P.cocomplex.d i j = F.map (P.cocomplex.d i j) ≫ l.f j at hl
    simp only [F.map_comp,Category.assoc]
    rw [hl] }

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_TwistHom
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (F : ModuleCat R ⥤ ModuleCat R) [F.Additive] [F.Linear k]
  [F.PreservesProjectiveObjects] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X : ModuleCat R} (P : ProjectiveResolution X) (e : F.obj X ≅ X)

def resolutionTwistHom (l : P.complex ⟶ (mappedResolution F P).complex) :
    resolutionHom k R P.complex X ⟶ resolutionHom k R P.complex X := by
  change P.complex ⟶ (F.mapHomologicalComplex (.down ℕ)).obj P.complex at l
  exact {
  f n := ModuleCat.ofHom
    (show (P.complex.X n ⟶ X) →ₗ[k] (P.complex.X n ⟶ X) from
    { toFun f := l.f n ≫ F.map f ≫ e.hom
      map_add' f g := by rw [F.map_add,Preadditive.add_comp,Preadditive.comp_add]
      map_smul' r f := by rw [F.map_smul,Linear.smul_comp,Linear.comp_smul]; rfl })
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change P.complex.X i ⟶ X at f
    symm
    change l.f j ≫ F.map (P.complex.d j i ≫ f) ≫ e.hom =
      P.complex.d j i ≫ l.f i ≫ F.map f ≫ e.hom
    have hl := l.comm j i
    change l.f j ≫ F.map (P.complex.d j i) = P.complex.d j i ≫ l.f i at hl
    simp only [F.map_comp,← Category.assoc]
    rw [hl] }

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteColimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteLimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))
  (hp₁ : ∀ i j (x : (G.X i).X j),
    p (i+1) j ((G.d i (i+1)).f j x) = (K.d (i+1) i).f j ≫ p i j x)
  (hp₂ : ∀ i j (x : (G.X i).X j),
    p i (j+1) ((G.X i).d j (j+1) x) = (K.X i).d (j+1) j ≫ p i j x)

include hp₁ hp₂ in
lemma comm (n : ℕ) :
    (G.total (.up ℕ)).d n (n+1) ≫ ModuleCat.ofHom (equiv K G N p (n+1)).toLinearMap =
    ModuleCat.ofHom (equiv K G N p n).toLinearMap ≫
      (resolutionHom k R (K.total (.down ℕ)) N).d n (n+1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j h
  erw [← Category.assoc, total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
    Preadditive.add_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (equiv K G N p (n+1) (G.d₁ (.up ℕ) i j (n+1) x)) +
    (equiv K G N p (n+1) (G.d₂ (.up ℕ) i j (n+1) x)) =
    (K.total (.down ℕ)).d (n+1) n ≫
      (equiv K G N p n (G.ιTotal (.up ℕ) i j n h x))
  apply HomologicalComplex₂.total.hom_ext
  intro a b h'
  erw [Preadditive.comp_add, horizontal K G N p hp₁ n i j a b h h' x,
    vertical K G N p hp₂ n i j a b h h' x, ← Category.assoc,
    total_d, Preadditive.comp_add, ι_D₁, ι_D₂, Preadditive.add_comp]

def comparison : G.total (.up ℕ) ⟶ resolutionHom k R (K.total (.down ℕ)) N where
  f n := ModuleCat.ofHom (equiv K G N p n).toLinearMap
  comm' n n' h := by
    change n+1=n' at h
    subst n'
    exact (comm K G N p hp₁ hp₂ n).symm

instance instIsIsoHomologicalComplexNatModuleCatUpComparison : IsIso (comparison K G N p hp₁ hp₂) := by
  have (n : ℕ) : IsIso ((comparison K G N p hp₁ hp₂).f n) :=
    (equiv K G N p n).toModuleIso.isIso_hom
  exact HomologicalComplex.Hom.isIso_of_components _

def iso : G.total (.up ℕ) ≅ resolutionHom k R (K.total (.down ℕ)) N :=
  asIso (comparison K G N p hp₁ hp₂)

end Tachikawa.TotalDualPairing



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (P : ChainComplex (ModuleCat A) ℕ) (Q : ChainComplex (ModuleCat B) ℕ)
  (U : ModuleCat A) (V : ModuleCat B)

abbrev homBicomplex := ((tensorF k).mapBifunctorHomologicalComplex (.up ℕ) (.up ℕ)).obj
  (resolutionHom k A P U) |>.obj (resolutionHom k B Q V)

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Finite B (Q.X n)]
  [∀ n, Module.Projective A (P.X n)] [∀ n, Module.Projective B (Q.X n)]
  [∀ n, FiniteDimensional k (P.X n)] [∀ n, FiniteDimensional k (Q.X n)]

def homBicomplexEquiv (i j : ℕ) : ((homBicomplex (k := k) P Q U V).X i).X j ≃ₗ[k]
    (((outerBicomplex k A B P Q).X i).X j ⟶ ((bifunctor k A B).obj U).obj V) :=
  homEquiv (k := k) (P.X i) U (Q.X j) V

lemma homBicomplexEquiv_horizontal (i j : ℕ) (x : ((homBicomplex (k := k) P Q U V).X i).X j) :
    homBicomplexEquiv P Q U V (i+1) j ((homBicomplex (k := k) P Q U V).d i (i+1) |>.f j <| x) =
      ((outerBicomplex k A B P Q).d (i+1) i).f j ≫ homBicomplexEquiv P Q U V i j x := by
  change (P.X i ⟶ U) ⊗[k] (Q.X j ⟶ V) at x
  change homMap (TensorProduct.map (precompose (k := k) (P.d (i+1) i)) LinearMap.id x) =
    morphism (P.d (i+1) i) (𝟙 (Q.X j)) ≫ homMap x
  have h := homMap_precompose (P.d (i+1) i) (𝟙 (Q.X j)) x
  rw [precompose_id] at h
  exact h

lemma homBicomplexEquiv_vertical (i j : ℕ) (x : ((homBicomplex (k := k) P Q U V).X i).X j) :
    homBicomplexEquiv P Q U V i (j+1) (((homBicomplex (k := k) P Q U V).X i).d j (j+1) x) =
      ((outerBicomplex k A B P Q).X i).d (j+1) j ≫ homBicomplexEquiv P Q U V i j x := by
  change (P.X i ⟶ U) ⊗[k] (Q.X j ⟶ V) at x
  change homMap (TensorProduct.map LinearMap.id (precompose (k := k) (Q.d (j+1) j)) x) =
    morphism (𝟙 (P.X i)) (Q.d (j+1) j) ≫ homMap x
  have h := homMap_precompose (𝟙 (P.X i)) (Q.d (j+1) j) x
  rw [precompose_id] at h
  exact h

variable [CharP k 2]

def homTotalIso :
    mapBifunctor (resolutionHom k A P U) (resolutionHom k B Q V) (tensorF k) (.up ℕ) ≅
    resolutionHom k (A ⊗[k] B) (mapBifunctor P Q (bifunctor k A B) (.down ℕ))
      (((bifunctor k A B).obj U).obj V) :=
  TotalDualPairing.iso (outerBicomplex k A B P Q) (homBicomplex (k := k) P Q U V) _
    (homBicomplexEquiv P Q U V) (homBicomplexEquiv_horizontal P Q U V)
    (homBicomplexEquiv_vertical P Q U V)

end Tachikawa.OuterTensor



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

def homologyIsoH (K : HomologicalComplex (ModuleCat k) c) (i : I) :
    K.homology i ≅ ModuleCat.of k (H K i) :=
  (homologyHomotopyEquiv K).toHomologyIso i ≪≫
    zeroDifferentialHomologyIso (homologyComplex K) (fun _ _ => rfl) i

end Tachikawa.VectorSplit



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B] [CharP k 2]
  {M U : ModuleCat A} {N V : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)] [∀ n, FiniteDimensional k (Q.complex.X n)]

abbrev tensorResolution := resolution k A B P Q (fun _ => inferInstance) (fun _ => inferInstance)

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)

variable {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (e : (algebraTwist σ).obj M ≅ M) (f : (algebraTwist τ).obj N ≅ N)
  (lP : ProjectiveResolution.Hom P (mappedResolution (algebraTwist σ) P) e.inv)
  (lQ : ProjectiveResolution.Hom Q (mappedResolution (algebraTwist τ) Q) f.inv)

variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]

lemma ι_resolution_π_zero :
    ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl ≫
      (tensorResolution (k := k) P Q).π.f 0 = morphism (P.π.f 0) (Q.π.f 0) := by
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc,ι_mapBifunctorMap]
  simp only [Category.assoc]
  erw [bifunctor_maps_assoc]
  change _ ≫ (bifunctorZeroIso (bifunctor k A B) _ _).inv ≫
    (bifunctorZeroIso (bifunctor k A B) _ _).hom = _
  rw [Iso.inv_hom_id,Category.comp_id]

def tensorTwistLift : ProjectiveResolution.Hom (tensorResolution (k := k) P Q)
    (mappedResolution (algebraTwist (Algebra.TensorProduct.congr σ τ))
      (tensorResolution (k := k) P Q)) (tensorTwistObjIso σ τ e f).inv where
  hom := tensorTwistLiftHom σ τ P Q e f lP lQ
  hom_f_zero_comp_π_f_zero := by
    dsimp only [mappedResolution] at lP lQ ⊢
    apply (cancel_epi (bifunctorZeroIso (bifunctor k A B) P.complex Q.complex).inv).mp
    change ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl ≫
      ((tensorTwistLiftHom σ τ P Q e f lP lQ).f 0 ≫
      (algebraTwist (Algebra.TensorProduct.congr σ τ)).map ((tensorResolution (k := k) P Q).π.f 0)) =
      ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl ≫
      ((tensorResolution (k := k) P Q).π.f 0 ≫ (tensorTwistObjIso σ τ e f).inv)
    rw [← Category.assoc,ι_tensorTwistLiftHom]
    simp only [Category.assoc]
    erw [
      ← (algebraTwist (Algebra.TensorProduct.congr σ τ)).map_comp
        (ιMapBifunctor P.complex Q.complex (bifunctor k A B) (.down ℕ) 0 0 0 rfl)
        ((tensorResolution (k := k) P Q).π.f 0),
      ι_resolution_π_zero,
      ← twistObjIso_natural σ τ (P.π.f 0) (Q.π.f 0),
      ← Category.assoc,← Category.assoc,
      morphism_comp (lP.hom.f 0) ((algebraTwist σ).map (P.π.f 0))
        (lQ.hom.f 0) ((algebraTwist τ).map (Q.π.f 0))]
    have hp : lP.hom.f 0 ≫ (algebraTwist σ).map (P.π.f 0) = P.π.f 0 ≫ e.inv :=
      lP.hom_f_zero_comp_π_f_zero
    have hq : lQ.hom.f 0 ≫ (algebraTwist τ).map (Q.π.f 0) = Q.π.f 0 ≫ f.inv :=
      lQ.hom_f_zero_comp_π_f_zero
    erw [hp,hq,← morphism_comp (P.π.f 0) e.inv (Q.π.f 0) f.inv,
      Category.assoc,ι_resolution_π_zero]
    rfl

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra

variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  [CharP k 2]
  {M : ModuleCat A} {N : ModuleCat B}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
  [∀ n, FiniteDimensional k (P.complex.X n)] [∀ n, FiniteDimensional k (Q.complex.X n)]

variable (σ : A ≃ₐ[k] A) (τ : B ≃ₐ[k] B)
  (e : (algebraTwist σ).obj M ≅ M) (f : (algebraTwist τ).obj N ≅ N)
  (lP : ProjectiveResolution.Hom P (mappedResolution (algebraTwist σ) P) e.inv)
  (lQ : ProjectiveResolution.Hom Q (mappedResolution (algebraTwist τ) Q) f.inv)

abbrev tensorResolutionTwist := resolutionTwistHom (k := k)
  (algebraTwist (Algebra.TensorProduct.congr σ τ)) (tensorResolution (k := k) P Q)
  (tensorTwistObjIso σ τ e f) (tensorTwistLift σ τ P Q e f lP lQ).hom

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.Construction.instInjectiveE _root_.OAI.Tachikawa.Construction.instIsScalarTowerEX _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.Construction.simpleTwist_preserves_projective _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instIsScalarTowerCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.TrivialInduction.instAdditiveModuleCatTrivialExtensionFunctor _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace TrivialInduction
variable {M : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

variable (C : ChainComplex (ModuleCat R) ℤ)

def inducedResolution (hC : TotallyAcyclic C)
    (fin : ∀ j, Module.Finite R (C.X j)) (proj : ∀ j, Module.Projective R (C.X j)) :
    ProjectiveResolution (ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0))) := by
  let X (n : ℕ) := ModuleCat.of (TrivialExtension k R) (Obj k R (C.X (n : ℤ)))
  let d (n : ℕ) : X (n+1) ⟶ X n := ModuleCat.ofHom (map (C.d ((n+1 : ℕ) : ℤ) (n : ℤ)).hom)
  let ε : X 0 ⟶ ModuleCat.of (TrivialExtension k R) (Obj k R (CokerAt C 0)) :=
    ModuleCat.ofHom (map (CokerAt.π C 0))
  apply resolutionOfExact _ X d ε
  · intro n
    apply map_exact
    · exact hC.1.adjacent C _ _ _ (by omega) (by omega)
    · exact (Nakayama.complex_exact (k := k) hC).adjacent _ _ _ _ (by omega) (by omega)
  · apply map_exact
    · exact fun x => Submodule.Quotient.mk_eq_zero _
    · exact Nakayama.map_exact _ _ (fun x => Submodule.Quotient.mk_eq_zero _) (CokerAt.π_surjective C 0)
  · exact map_surjective _ (CokerAt.π_surjective C 0)
  · intro n
    let := fin (n : ℤ)
    let := proj (n : ℤ)
    infer_instance

end TrivialInduction



end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCe _root_.OAI.Tachikawa.Construction.instFiniteCSubtypeMemSubmoduleCf _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleEC _root_.OAI.Tachikawa.Construction.instFiniteMulOppositeCSubtypeMemSubmoduleFC _root_.OAI.Tachikawa.Construction.instProjectiveMulOppositeC _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instAddCommGroupCarrierMulOppositeRightObj _root_.OAI.Tachikawa.Enveloping.instFiniteCarrierDualLeftObjOfFiniteDimensional _root_.OAI.Tachikawa.Enveloping.instModuleCarrierMulOppositeRightObj_1 _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.instAdditiveModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteColimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.OuterTensor.instPreservesFiniteLimitsModuleCatTensorProductObjFunctorFlipBifunctor _root_.OAI.Tachikawa.Triangular.instFiniteCarrierOneFree _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

def simpleResolutionTwistLift : ProjectiveResolution.Hom (sResolution q)
    (mappedResolution (C.tTwist q H hH) (sResolution q)) (C.simpleTwistIso q H hH).inv where
  hom := ProjectiveResolution.lift _ _ _
  hom_f_zero_comp_π_f_zero := ProjectiveResolution.lift_commutes_zero _ _ _

abbrev simpleResolutionTwist := resolutionTwistHom (k := k) (C.tTwist q H hH) (sResolution q)
  (C.simpleTwistIso q H hH) (simpleResolutionTwistLift q H hH).hom

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)
  (hq : q ≠ 0) (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

abbrev XTensorTwistIso := OuterTensor.tensorTwistObjIso
  (TrivialExtension.scaleDual (R := C k q) H hH) (TrivialExtension.scaleDual (R := C k q) H hH)
  (C.simpleTwistIso q H hH) (C.simpleTwistIso q H hH)
abbrev xTensorTwistLift := OuterTensor.tensorTwistLift
  (TrivialExtension.scaleDual (R := C k q) H hH) (TrivialExtension.scaleDual (R := C k q) H hH)
  (sResolution q) (sResolution q) (C.simpleTwistIso q H hH) (C.simpleTwistIso q H hH)
  (simpleResolutionTwistLift q H hH) (simpleResolutionTwistLift q H hH)
abbrev xTensorResolution := OuterTensor.tensorResolution (k := k) (sResolution q) (sResolution q)
abbrev xTensorTwist := resolutionTwistHom (k := k) (eTwist q H hH) (xTensorResolution q)
  (XTensorTwistIso q H hH) (xTensorTwistLift q H hH).hom

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
def XTensorIso : XTensorObj q ≅ ModuleCat.of (E q) (X q) := (XTensorEquiv q).toModuleIso

end Tachikawa.Construction



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra TensorProduct
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

def XTwistIso : (twistE q H hH).obj (ModuleCat.of (E q) (X q)) ≅ ModuleCat.of (E q) (X q) :=
  (eTwist q H hH).mapIso (XTensorIso q).symm ≪≫ XTensorTwistIso q H hH ≪≫ XTensorIso q

end Tachikawa.Construction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.Enveloping.eval_finite _root_.OAI.Tachikawa.Enveloping.instLinearModuleCatAlgEvaluation _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteColimits _root_.OAI.Tachikawa.Enveloping.rightFree_preservesFiniteLimits _root_.OAI.Tachikawa.HomBimodule.instFiniteDimensionalCarrierAlgObj _root_.OAI.Tachikawa.Triangular.instAddCommGroupOff _root_.OAI.Tachikawa.Triangular.instAddCommGroupTriple _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₀ _root_.OAI.Tachikawa.Triangular.instAdditiveModuleCatAlgD₁ _root_.OAI.Tachikawa.Triangular.instFiniteDimensionalAlgOfCarrierAlg _root_.OAI.Tachikawa.Triangular.instIsScalarTowerMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instIsScalarTowerProdOff _root_.OAI.Tachikawa.Triangular.instModuleAlgTriple _root_.OAI.Tachikawa.Triangular.instModuleMulOppositeProdOff _root_.OAI.Tachikawa.Triangular.instModuleOff _root_.OAI.Tachikawa.Triangular.instModuleProdOff _root_.OAI.Tachikawa.Triangular.instSMulCommClassProdMulOppositeOff _root_.OAI.Tachikawa.freeEndo_finite _root_.OAI.Tachikawa.freeKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R] {M : ModuleCat.{0} R}

namespace Enveloping
open scoped TensorProduct
variable {k S : Type} [Field k] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S] (φ : R →ₐ[k] S)

instance inducedRegularCochain_finite (i : ℤ) :
    Module.Finite (Alg k S S) ((inducedRegularCochain φ).X i) := by
  let P := regularResolution (k := k) (R := R)
  let : Module.Finite (Alg k R R) (P.cochainComplex.X i) :=
    finite_resolution_cochain P (fun _ => inferInstance) i
  let : FiniteDimensional k (P.cochainComplex.X i) := Module.Finite.trans (Alg k R R) _
  let : FiniteDimensional k ((AlgebraInduction.functor (envelopingMap φ)).obj
    (P.cochainComplex.X i)) := inferInstance
  change Module.Finite (Alg k S S) ((AlgebraInduction.functor (envelopingMap φ)).obj
    (P.cochainComplex.X i))
  exact Module.Finite.of_restrictScalars_finite k _ _

end Enveloping
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Triangular
attribute [-instance] _root_.OAI.Tachikawa.DownHom.instAddCommGroupCochain _root_.OAI.Tachikawa.DownHom.instModuleCochain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R)) (L N : ModuleCat R)
  (α : Enveloping.evalType L F →ₗ[R] N)

instance instModuleTriple : Module k (Triple F L N α) := inferInstanceAs (Module k (L × N))

instance instIsScalarTowerAlgTriple : IsScalarTower k (Alg F) (Triple F L N α) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    apply Prod.ext
    · exact IsScalarTower.algebraMap_smul R c x.1
    · change α (BalancedTensor.mk (0 : Enveloping.Obj F) x.1) +
        algebraMap k R c • x.2 = c • x.2
      simp

instance instFiniteDimensionalTripleOfCarrier [FiniteDimensional k L] [FiniteDimensional k N] :
    FiniteDimensional k (Triple F L N α) := inferInstanceAs (FiniteDimensional k (L × N))

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {F : ModuleCat (Enveloping.Alg k R R)} {L N L' N' : ModuleCat R}
  {α : Enveloping.evalType L F →ₗ[R] N} {β : Enveloping.evalType L' F →ₗ[R] N'}

variable (f : Triple F L N α →ₗ[Alg F] Triple F L' N' β)

lemma hom_compatible : (homLower f).comp α =
    β.comp (BalancedTensor.mapRight (M := Enveloping.Obj F) (homUpper f)) := by
  apply BalancedTensor.hom_ext
  intro m x
  have h := congrArg Prod.snd (f.map_smul (TrivSqZeroExt.inr (show Off F from m))
    (show Triple F L N α from (x,0)))
  change (f (0 • x, α (BalancedTensor.mk m x) + 0 • (0:N))).2 =
    β (BalancedTensor.mk m (f (x,0)).1) + 0 • (f (x,0)).2 at h
  change (f (0,α (BalancedTensor.mk m x))).2 =
    β (BalancedTensor.mk m (f (x,0)).1)
  simpa only [zero_smul,add_zero] using h

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R))

variable {F} {L L' : ModuleCat R}

def diagonal₀ : (D₀Obj F L ⟶ D₀Obj F L') ≃ₗ[k] (L ⟶ L') where
  toFun f := ModuleCat.ofHom (homUpper f.hom)
  invFun := D₀Map F
  left_inv f := by
    apply ModuleCat.hom_ext
    apply triple_hom_ext
    · rfl
    · have hc := hom_compatible f.hom
      apply LinearMap.ext
      intro x
      have he := LinearMap.congr_fun hc x
      exact he.symm
  right_inv f := rfl
  map_add' f g := by rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((algebraMap k (Alg F) c) • f.hom (x,0)).1 = c • (f.hom (x,0)).1
    exact congrArg Prod.fst (IsScalarTower.algebraMap_smul (Alg F) c (f.hom (x,0)))

def diagonal₁ : (D₁Obj F L ⟶ D₁Obj F L') ≃ₗ[k] (L ⟶ L') where
  toFun f := ModuleCat.ofHom (homLower f.hom)
  invFun := D₁Map F
  left_inv f := by
    apply ModuleCat.hom_ext
    apply triple_hom_ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv f := rfl
  map_add' f g := by rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((algebraMap k (Alg F) c) • f.hom (0,x)).2 = c • (f.hom (0,x)).2
    change ((TrivSqZeroExt.inl (algebraMap k R c,algebraMap k R c)) •
      f.hom (0,x)).2 = c • (f.hom (0,x)).2
    erw [diagonal_smul_triple]
    exact IsScalarTower.algebraMap_smul R c (f.hom (0,x)).2

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R)) (ι : Type) [Fintype ι]

def D₁FreeInclusion : D₁Obj F (freeObj (R := R) ι) →ₗ[Alg F] (ι → Alg F) where
  toFun x i := TrivSqZeroExt.inl (0,x.2 i)
  map_add' x y := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · simp
      · rfl
    · exact (zero_add (0 : Enveloping.Obj F)).symm
  map_smul' a x := by
    funext i
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · change (0:R) = upper F a * 0
        simp
      · change ((0 : freeObj (R := R) ι) + lower F a • x.2) i = lower F a * x.2 i
        rw [zero_add]
        rfl
    · change (0 : Enveloping.Obj F) = lower F a • 0 + (0 : Rᵐᵒᵖ) • off F a
      rw [smul_zero, zero_smul, add_zero]

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat (Enveloping.Alg k R R)) (L : ModuleCat R)

instance instFiniteDimensionalCarrierAlgD₀ObjOfAlg [FiniteDimensional k F] [FiniteDimensional k L] :
    FiniteDimensional k (D₀Obj F L) := by
  let : FiniteDimensional k (Enveloping.Obj F) := inferInstanceAs (FiniteDimensional k F)
  let : FiniteDimensional k (tensorObj F L) := moduleCatFinite _
  let : FiniteDimensional k (Triple F L (tensorObj F L) LinearMap.id) :=
    inferInstanceAs (FiniteDimensional k (L × (tensorObj F L)))
  exact moduleCatFinite (Triple F L (tensorObj F L) LinearMap.id)

instance instFiniteDimensionalCarrierAlgD₁Obj [FiniteDimensional k L] : FiniteDimensional k (D₁Obj F L) := by
  exact moduleCatFinite _

end Tachikawa.Triangular



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DownHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
open DownHom
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))

variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
abbrev down₀ (a : ℤ) : Cochain (D₀Complex F P) (D₀Complex F Q) a ≃ₗ[k] Cochain P Q a :=
  cochainEquiv (fun _ _ => diagonal₀) a
abbrev down₁ (a : ℤ) : Cochain (D₁Complex F P) (D₁Complex F Q) a ≃ₗ[k] Cochain P Q a :=
  cochainEquiv (fun _ _ => diagonal₁) a
abbrev downCross (a : ℤ) : Cochain (D₁Complex F P) (D₀Complex F Q) a ≃ₗ[k]
    Cochain P (Enveloping.tensorComplex F Q) a :=
  cochainEquiv (fun _ _ => cross₁₀) a

end Tachikawa.Triangular

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Cone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (F : ModuleCat.{0} (Enveloping.Alg k R R))
def regIn₀ : D₀Obj F (oneFree (R := R)) →ₗ[Alg F] Alg F :=
  (LinearMap.proj PUnit.unit).comp (D₀FreeInclusion F PUnit)
def regIn₁ : D₁Obj F (oneFree (R := R)) →ₗ[Alg F] Alg F :=
  (LinearMap.proj PUnit.unit).comp (D₁FreeInclusion F PUnit)
def regOut₀ : Alg F →ₗ[Alg F] D₀Obj F (oneFree (R := R)) :=
  (D₀FreeProjection F PUnit).comp (LinearMap.pi fun _ => LinearMap.id)
def regOut₁ : Alg F →ₗ[Alg F] D₁Obj F (oneFree (R := R)) :=
  (D₁FreeProjection F PUnit).comp (LinearMap.pi fun _ => LinearMap.id)

end Tachikawa.Triangular



end

end OAI
end


