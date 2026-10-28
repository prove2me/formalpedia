-- Prove2me | Definitions.Def_OAIQ032L005
-- name    : OAIQ032L005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:43:35.026272+00:00
-- url     : https://prove2.me/theorems/54c4796a-ab87-40c8-9a25-d63cacbb4b6d
-- title:
--   Definitions bundle OAIQ032L005 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 49 definitions, 1 inductive type or structure, 8 instances and 45 theorems. The definitions and types are `OAI.Lech.IdealGraded.Piece`, `OAI.Lech.IdealGraded.inclusion`, `OAI.Lech.IdealGraded.nextPower`, `OAI.Lech.IdealGraded.transition`, `OAI.Lech.IntegerWeights.SeparatelyAffine`, `OAI.Lech.IsFiniteHomologyComplex`, `OAI.Lech.IsMinimalComplex`, `OAI.Lech.Koszul.augmentation`, `OAI.Lech.Koszul.biprodShortComplex`, `OAI.Lech.Koszul.biprodSplitting`, `OAI.Lech.Koszul.cFst`, `OAI.Lech.Koszul.cInl`, `OAI.Lech.Koszul.cInr`, `OAI.Lech.Koszul.cSnd`, `OAI.Lech.Koszul.coneEntryHomotopy`, `OAI.Lech.Koszul.coneFst`, `OAI.Lech.Koszul.coneFunctor`, `OAI.Lech.Koszul.coneHomologyProjection`, `OAI.Lech.Koszul.coneRetraction`, `OAI.Lech.Koszul.coneScalarHomotopy`, `OAI.Lech.Koszul.coneShortComplex`, `OAI.Lech.Koszul.coneShortComplexIso`, `OAI.Lech.Koszul.coneShortComplexMap`, `OAI.Lech.Koszul.coneSplitting`, `OAI.Lech.Koszul.coneSwap`, `OAI.Lech.Koszul.coneSwapX`, `OAI.Lech.Koszul.coneTermEquiv`, `OAI.Lech.Koszul.entryIdeal`, `OAI.Lech.Koszul.inclusion`, `OAI.Lech.Koszul.powerMap`, `OAI.Lech.Koszul.projectionTerm`, `OAI.Lech.Koszul.quotientAugmentation`, `OAI.Lech.Koszul.retraction`, `OAI.Lech.Koszul.scalarCone`, `OAI.Lech.Koszul.tensor`, `OAI.Lech.Koszul.tensorFunctor`, `OAI.Lech.Koszul.tensorMap`, `OAI.Lech.Koszul.tensorScalarHomotopy`, `OAI.Lech.Koszul.termIso`, `OAI.Lech.LocalLine.instAlgebraTensorProduct_solutions` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_DuttaData`, `Multiplicity_FilteredCechAugmentationRing`, `Multiplicity_IdealFilteredLayers`, `Multiplicity_KoszulConeFunctor`, `Multiplicity_KoszulHomologyMap`, `Multiplicity_KoszulSwap`, `Multiplicity_LechBoundedEquiv`, `Multiplicity_LechFactorizationMap`, `Multiplicity_LechNatTrans`, `Multiplicity_MinimalComplexReduction`, `Multiplicity_ModuleComplexQuotient`, `Multiplicity_PowerSeriesFlatVariables`, `Multiplicity_ReesRootUnfiltered`, `Multiplicity_SourceGradedThickeningNat`, `Multiplicity_SymmetricAffine`, `Multiplicity_TensorTotalHomologyProperty`.
--
--   **Imports.** It imports the published bundle `Def_DuttaDomain`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L013`, `OAIQ032L014`, `OAIQ032L016` and `OAIQ032L018`; the statements `OAI.Lech.CharP.dutta_limit_from_perfection`, `OAI.Lech.CharP.dutta_minimal_estimate`, `OAI.Lech.CharP.perfection_complex_value`, `OAI.Lech.FrobeniusIntermediate.frobenius_homology_order_transfer`, `OAI.Lech.Koszul.length_quotient_tensor_le_sum`, `OAI.Lech.PerfectDomainStages.frobenius_homology_conductor_bound`, `OAI_Lech_ReesRoot_rootTotal_euler_nonnegative`, `OAI.Lech.SeparableOrder.frobenius_homology_tendsto_zero`, `OAI.Lech.exists_scalar_extension_homology_bound`, `OAI.Lech.finiteHomology_extendScalars`, `OAI.Lech.frobenius_quotient_homology_bound`, `OAI.Lech.frobenius_quotient_homology_finiteLength`, `OAI.Lech.frobenius_quotient_homology_tendsto_zero`, `OAI.Lech.frobenius_shortComplex_homology_finiteLength`, `OAI.Lech.nonminimal_complex_reduction`, `OAI.Lech.shortComplex_nullScalar_radical` and `OAI.Lech.short_rank_euler_zero`; the proofs of `OAI.Lech.CharP.dutta_lower_bound_infinite_perfect`, `OAI.Lech.dutta_dimension_zero`, `OAI.Lech.nonminimal_complex_reduction` and `OAI.Lech.shortComplex_nullScalar_radical`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_DuttaDomain

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechBoundedEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory


namespace Lech
namespace IdealGraded

variable {A : Type*} [CommRing A]

def nextPower (I : Ideal A) (n : ℕ) : Submodule A ↥(I ^ n) :=
  Submodule.comap (I ^ n).subtype (I ^ (n + 1))

abbrev Piece (I : Ideal A) (n : ℕ) := ↥(I ^ n) ⧸ nextPower I n

lemma pow_succ_le (I : Ideal A) (n : ℕ) : I ^ (n + 1) ≤ I ^ n := by
  exact Ideal.pow_le_pow_right (Nat.le_succ n)

lemma torsion_piece (I : Ideal A) (n : ℕ) :
    Module.IsTorsionBySet A (Piece I n) I := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x a ha
  change a * (x : A) ∈ I ^ (n + 1)
  rw [pow_succ']
  exact Ideal.mul_mem_mul ha x.property

noncomputable instance pieceModule (I : Ideal A) (n : ℕ) :
    Module (A ⧸ I) (Piece I n) := (torsion_piece I n).module

instance pieceTower (I : Ideal A) (n : ℕ) :
    IsScalarTower A (A ⧸ I) (Piece I n) :=
  (torsion_piece I n).isScalarTower

def inclusion (I : Ideal A) (n : ℕ) : Piece I n →ₗ[A] A ⧸ I ^ (n + 1) :=
  (nextPower I n).liftQ (((I ^ (n + 1)).mkQ).comp (I ^ n).subtype) (by
    intro x hx
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, nextPower, Submodule.mem_comap] using hx)

def transition (I : Ideal A) (n : ℕ) :
    (A ⧸ I ^ (n + 1)) →ₗ[A] (A ⧸ I ^ n) :=
  (I ^ (n + 1)).mapQ (I ^ n) LinearMap.id (pow_succ_le I n)

instance pieceFinite [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    Module.Finite (A ⧸ I) (Piece I n) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ I) (Piece I n)

end IdealGraded
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorTotalHomologyProperty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech
universe u v
variable {R : Type u} [CommRing R]

 
noncomputable def moduleQuotient (I : Ideal R) : ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj M := ModuleCat.of R (M ⧸ (I • (⊤ : Submodule R M)))
  map {M N} f := ModuleCat.ofHom ((I • (⊤ : Submodule R M)).mapQ
    (I • (⊤ : Submodule R N)) f.hom (Submodule.smul_top_le_comap_smul_top I f.hom))
  map_id M := by
    apply ModuleCat.hom_ext
    exact Submodule.mapQ_id _
  map_comp {M N P} f g := by
    ext x
    rfl

instance moduleQuotient_additive (I : Ideal R) : (moduleQuotient I : ModuleCat.{v} R ⥤ _).Additive where
  map_add {M N} f g := by
    ext x
    obtain ⟨x,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
    rfl

 
noncomputable def moduleQuotientπ (I : Ideal R) : 𝟭 (ModuleCat.{v} R) ⟶ moduleQuotient I where
  app M := ModuleCat.ofHom (I • (⊤ : Submodule R M)).mkQ
  naturality {M N} f := by
    ext x
    rfl

instance moduleQuotientπ_epi (I : Ideal R) (M : ModuleCat.{v} R) :
    Epi ((moduleQuotientπ I).app M) :=
  (ModuleCat.epi_iff_surjective _).mpr (I • (⊤ : Submodule R M)).mkQ_surjective

lemma moduleQuotient_annihilated (I : Ideal R) (r : R) (hr : r ∈ I)
    (M : ModuleCat.{v} R) : r • 𝟙 ((moduleQuotient I).obj M) = 0 := by
  ext x
  obtain ⟨x,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
  change (I • (⊤ : Submodule R M)).mkQ (r • x) = 0
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul hr trivial)

 
noncomputable def complexQuotient (I : Ideal R) {ι : Type*} (c : ComplexShape ι) :
    HomologicalComplex (ModuleCat.{v} R) c ⥤ HomologicalComplex (ModuleCat.{v} R) c :=
  (moduleQuotient I).mapHomologicalComplex c

noncomputable def complexQuotientπ (I : Ideal R) {ι : Type*} {c : ComplexShape ι}
    (F : HomologicalComplex (ModuleCat.{v} R) c) : F ⟶ (complexQuotient I c).obj F where
  f i := (moduleQuotientπ I).app (F.X i)
  comm' i j _hij := (moduleQuotientπ I).naturality (F.d i j)

lemma complexQuotient_annihilated (I : Ideal R) (r : R) (hr : r ∈ I)
    {ι : Type*} {c : ComplexShape ι} (F : HomologicalComplex (ModuleCat.{v} R) c) :
    r • 𝟙 ((complexQuotient I c).obj F) = 0 := by
  ext i : 1
  exact moduleQuotient_annihilated I r hr (F.X i)

end Lech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

 
def termTensorQuotientIso (I : Ideal R) :
    (curriedTensor (ModuleCat.{u} R)).flip.obj (ModuleCat.of R (R ⧸ I)) ≅ moduleQuotient I :=
  NatIso.ofComponents (fun M => (TensorProduct.tensorQuotEquivQuotSMul M I).toModuleIso)
    (fun {M N} f => by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m q
      obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
      change TensorProduct.tensorQuotEquivQuotSMul N I (f.hom m ⊗ₜ[R] Ideal.Quotient.mk I r) =
        ((moduleQuotient I).map f).hom (TensorProduct.tensorQuotEquivQuotSMul M I
          (m ⊗ₜ[R] Ideal.Quotient.mk I r))
      simp only [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
      change _ = Submodule.Quotient.mk (f.hom (r • m))
      rw [map_smul])



end Lech.TensorTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmentationRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [CommRing R]

 
noncomputable def moduleQuotientMap {I J : Ideal R} (h : I ≤ J) :
    (moduleQuotient I : ModuleCat.{v} R ⥤ _) ⟶ moduleQuotient J where
  app M := ModuleCat.ofHom (Submodule.factor (Submodule.smul_mono h le_rfl))
  naturality {M N} f := by
    ext x
    obtain ⟨x,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective x
    rfl

@[reassoc (attr := simp)]
lemma moduleQuotientπ_map {I J : Ideal R} (h : I ≤ J) (M : ModuleCat.{v} R) :
    (moduleQuotientπ I).app M ≫ (moduleQuotientMap h).app M =
      (moduleQuotientπ J).app M := by ext x; rfl

@[reassoc]
lemma moduleQuotientMap_comp {I J K : Ideal R} (h : I ≤ J) (h' : J ≤ K)
    (M : ModuleCat.{v} R) :
    (moduleQuotientMap h).app M ≫ (moduleQuotientMap h').app M =
      (moduleQuotientMap (h.trans h')).app M := by
  apply (cancel_epi ((moduleQuotientπ I).app M)).mp
  simp

noncomputable def complexQuotientMap {I J : Ideal R} (h : I ≤ J)
    {ι : Type*} (c : ComplexShape ι) :
    (complexQuotient I c : HomologicalComplex (ModuleCat.{v} R) c ⥤ _) ⟶
      complexQuotient J c := (moduleQuotientMap h).mapHomologicalComplex c

@[reassoc (attr := simp)]
lemma complexQuotientπ_map {I J : Ideal R} (h : I ≤ J)
    {ι : Type*} {c : ComplexShape ι} (F : HomologicalComplex (ModuleCat.{v} R) c) :
    complexQuotientπ I F ≫ (complexQuotientMap h c).app F = complexQuotientπ J F := by
  ext i : 1
  exact moduleQuotientπ_map h (F.X i)



end Lech


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]

@[reassoc] lemma termTensorQuotientIso_naturality {I J : Ideal R} (hIJ : I ≤ J)
    (M : ModuleCat.{u} R) :
    (M ◁ ModuleCat.ofHom (Submodule.factor hIJ)) ≫ (termTensorQuotientIso J).hom.app M =
      (termTensorQuotientIso I).hom.app M ≫ (moduleQuotientMap hIJ).app M := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m q
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective q
  change TensorProduct.tensorQuotEquivQuotSMul M J (m ⊗ₜ[R] Ideal.Quotient.mk J r) =
    (Submodule.factor (Submodule.smul_mono hIJ le_rfl))
      (TensorProduct.tensorQuotEquivQuotSMul M I (m ⊗ₜ[R] Ideal.Quotient.mk I r))
  simp [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]

end Lech.TensorTotal


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechFactorizationMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.LocalLine
open scoped TensorProduct
universe u v w z
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable (L : Type z) [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
local instance instAlgebraTensorProduct_solutions : Algebra S (L ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
end Lech.LocalLine


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SourceGradedThickeningNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

open CochainComplex CochainComplex.HomComplex
namespace Lech.Koszul

variable {R : Type*} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]
variable {F G : CochainComplex C ℤ}

omit [HasBinaryBiproducts C] in
lemma ofHom_smul (a : R) (f : F ⟶ G) :
    Cochain.ofHom (a • f) = a • Cochain.ofHom f := by
  ext i
  simp

 
noncomputable def coneRetraction {f : F ⟶ G} (h : Homotopy f 0) :
    mappingCone f ⟶ G :=
  mappingCone.desc f (Cochain.ofHomotopy h) (𝟙 G) (by simp)

@[simp] lemma inr_coneRetraction {f : F ⟶ G} (h : Homotopy f 0) :
    mappingCone.inr f ≫ coneRetraction h = 𝟙 G := by
  simp [coneRetraction]

 
noncomputable def coneScalarHomotopy (a b : R) (h : Homotopy (a • 𝟙 F) 0) :
    Homotopy (a • 𝟙 (mappingCone (b • 𝟙 F))) 0 := by
  let φ : F ⟶ F := b • 𝟙 F
  let H := Cochain.ofHomotopy h
  let α : Cochain F (mappingCone φ) (-2) :=
    -(H.comp (mappingCone.inl φ) (by norm_num))
  let β : Cochain F (mappingCone φ) (-1) :=
    H.comp (Cochain.ofHom (mappingCone.inr φ)) (add_zero (-1))
  refine (Cochain.equivHomotopy _ _).symm
    ⟨mappingCone.descCochain φ α β (by norm_num), ?_⟩
  have hH : δ (-1) 0 H = a • Cochain.ofHom (𝟙 F) := by
    simp [H, ofHom_smul]
  have hβ : δ (-1) 0 β = a • Cochain.ofHom (mappingCone.inr φ) := by
    dsimp [β]
    rw [δ_comp_ofHom]
    simp [hH, Cochain.smul_comp]
  have hα : δ (-2) (-1) α =
      -(H.comp (Cochain.ofHom φ) (add_zero (-1))).comp
        (Cochain.ofHom (mappingCone.inr φ)) (add_zero (-1)) +
      a • mappingCone.inl φ := by
    dsimp [α]
    rw [δ_neg, δ_comp H (mappingCone.inl φ) (by norm_num) 0 0 (-1)
      (by norm_num) (by norm_num) (by norm_num)]
    simp [mappingCone.δ_inl, hH, Cochain.smul_comp,
      Cochain.comp_assoc_of_second_is_zero_cochain, add_comm]
  rw [Cochain.ofHom_zero, add_zero, mappingCone.δ_descCochain _ _ _ _ 0 (by norm_num),
    hα, hβ]
  have hc : (H.comp (Cochain.ofHom φ) (add_zero (-1))).comp
        (Cochain.ofHom (mappingCone.inr φ)) (add_zero (-1)) =
      (Cochain.ofHom φ).comp β (by norm_num) := by
    simp [φ, β, ofHom_smul, Cochain.comp_smul, Cochain.smul_comp]
  rw [hc]
  simp only [Int.reduceNeg, Int.negOnePow_zero, one_smul]
  rw [show -(Cochain.ofHom φ).comp β (zero_add (-1)) + a • mappingCone.inl φ +
    (Cochain.ofHom φ).comp β (zero_add (-1)) = a • mappingCone.inl φ by abel]
  simp only [Cochain.comp_smul, ← smul_add, mappingCone.id, ofHom_smul]
  rfl

 
noncomputable def coneEntryHomotopy (a : R) (F : CochainComplex C ℤ) :
    Homotopy (a • 𝟙 (mappingCone (a • 𝟙 F))) 0 := by
  let φ : F ⟶ F := a • 𝟙 F
  refine (Cochain.equivHomotopy _ _).symm
    ⟨mappingCone.descCochain φ (0 : Cochain F (mappingCone φ) (-2))
      (mappingCone.inl φ) (by norm_num), ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ 0 (by norm_num)]
  simp only [δ_zero, zero_add, Int.negOnePow_zero, one_smul, mappingCone.δ_inl,
    Cochain.ofHom_zero, add_zero]
  simp only [φ, Linear.smul_comp, Category.id_comp, ofHom_smul, Cochain.smul_comp, Cochain.id_comp, Cochain.comp_smul,
    ← smul_add, mappingCone.id]

 
noncomputable def tensor (zs : List R) (F : CochainComplex C ℤ) : CochainComplex C ℤ :=
  zs.foldr (fun a K => mappingCone (a • 𝟙 K)) F

@[simp] lemma tensor_nil (F : CochainComplex C ℤ) : tensor ([] : List R) F = F := rfl
@[simp] lemma tensor_cons (a : R) (zs : List R) (F : CochainComplex C ℤ) :
    tensor (a :: zs) F = mappingCone (a • 𝟙 (tensor zs F)) := rfl

 
noncomputable def tensorScalarHomotopy (a : R) (zs : List R)
    (h : Homotopy (a • 𝟙 F) 0) : Homotopy (a • 𝟙 (tensor zs F)) 0 := by
  induction zs with
  | nil => exact h
  | cons b zs ih => exact coneScalarHomotopy a b ih


noncomputable def coneFunctor (a : R) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj F := mappingCone (a • 𝟙 F)
  map f := mappingCone.map _ _ f f (by simp [Linear.smul_comp, Linear.comp_smul])
  map_id _ := mappingCone.map_id _
  map_comp _ _ := mappingCone.map_comp _ _ _ _ _ _ _ _ _

instance instAdditiveCochainComplexIntConeFunctor (a : R) : (coneFunctor (C := C) a).Additive where
  map_add {F G} f g := by
    change mappingCone.map (a • 𝟙 F) (a • 𝟙 G) (f + g) (f + g)
        (by simp [Linear.smul_comp, Linear.comp_smul]) =
      mappingCone.map (a • 𝟙 F) (a • 𝟙 G) f f (by simp [Linear.smul_comp, Linear.comp_smul]) +
        mappingCone.map (a • 𝟙 F) (a • 𝟙 G) g g (by simp [Linear.smul_comp, Linear.comp_smul])
    ext i
    rw [HomologicalComplex.add_f_apply]
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map,
      HomologicalComplex.add_f_apply, Preadditive.add_comp, Preadditive.comp_add]

noncomputable def termIso (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    ((coneFunctor a).obj F).X i ≅ F.X (i + 1) ⊞ F.X i :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (a • 𝟙 F) i (i + 1) rfl

lemma coneFunctor_map_f (a : R) {F G : CochainComplex C ℤ} (f : F ⟶ G) (i : ℤ) :
    ((coneFunctor a).map f).f i = (termIso a F i).hom ≫
      biprod.map (f.f (i + 1)) (f.f i) ≫ (termIso a G i).inv := by
  apply (mappingCone.ext_from_iff _ (i + 1) i rfl _ _).mpr
  constructor
  · simp [coneFunctor, mappingCone.map]
    change _ = HomologicalComplex.homotopyCofiber.inlX _ _ _ _ ≫ _
    simp [termIso, mappingCone.inl]
    have hF := HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom (a • 𝟙 F) (i+1) i rfl
    have hG := HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv (a • 𝟙 G) (i+1) i rfl
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ biprod.map (f.f (i+1)) (f.f i) ≫ (termIso a G i).inv) hF).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (termIso a G i).inv) (biprod.inl_map (f.f (i+1)) (f.f i))).trans
            ((Category.assoc _ _ _).trans ((congrArg (f.f (i+1) ≫ ·) hG))))))).symm
  · simp [coneFunctor, mappingCone.map]
    change _ = HomologicalComplex.homotopyCofiber.inrX _ _ ≫ _
    simp [termIso, mappingCone.inr]
    have hF := HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom (a • 𝟙 F) (i+1) i rfl
    have hG := HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv (a • 𝟙 G) (i+1) i rfl
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ biprod.map (f.f (i+1)) (f.f i) ≫ (termIso a G i).inv) hF).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (termIso a G i).inv) (biprod.inr_map (f.f (i+1)) (f.f i))).trans
            ((Category.assoc _ _ _).trans ((congrArg (f.f i ≫ ·) hG))))))).symm

noncomputable def biprodShortComplex (S T : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g) (by
    ext <;> simp)

noncomputable def biprodSplitting {S T : ShortComplex C} (s : S.Splitting) (t : T.Splitting) :
    (biprodShortComplex S T).Splitting where
  r := biprod.map s.r t.r
  s := biprod.map s.s t.s
  f_r := by
    dsimp [biprodShortComplex]
    ext <;> simp
  s_g := by
    dsimp [biprodShortComplex]
    ext <;> simp
  id := by
    change biprod.map s.r t.r ≫ biprod.map S.f T.f +
      biprod.map S.g T.g ≫ biprod.map s.s t.s = 𝟙 (S.X₂ ⊞ T.X₂)
    apply biprod.hom_ext
    · simpa [Preadditive.comp_add, Preadditive.add_comp, Category.assoc] using
        (biprod.fst : S.X₂ ⊞ T.X₂ ⟶ S.X₂) ≫= s.id
    · simpa [Preadditive.comp_add, Preadditive.add_comp, Category.assoc] using
        (biprod.snd : S.X₂ ⊞ T.X₂ ⟶ T.X₂) ≫= t.id

noncomputable def coneShortComplexIso (a : R) (S : ShortComplex (CochainComplex C ℤ))
    (i : ℤ) : (S.map (coneFunctor a)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) i) ≅
      biprodShortComplex (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) (i + 1)))
        (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)) :=
  ShortComplex.isoMk (termIso a S.X₁ i) (termIso a S.X₂ i) (termIso a S.X₃ i)
    (by simp [biprodShortComplex]; change _ = ((coneFunctor a).map S.f).f i ≫ _; rw [coneFunctor_map_f]; erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl)
    (by simp [biprodShortComplex]; change _ = ((coneFunctor a).map S.g).f i ≫ _; rw [coneFunctor_map_f]; erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl)

noncomputable def coneSplitting (a : R) (S : ShortComplex (CochainComplex C ℤ))
    (hs : ∀ i, (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting) (i : ℤ) :
    ((S.map (coneFunctor a)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) i)).Splitting :=
  (biprodSplitting (hs (i + 1)) (hs i)).ofIso (coneShortComplexIso a S i).symm

 
noncomputable def tensorMap (zs : List R) {F G : CochainComplex C ℤ}
    (f : F ⟶ G) : tensor zs F ⟶ tensor zs G := by
  induction zs with
  | nil => exact f
  | cons a zs ih =>
    exact mappingCone.map (a • 𝟙 (tensor zs F)) (a • 𝟙 (tensor zs G)) ih ih
      (by simp [Linear.smul_comp, Linear.comp_smul])

lemma tensorMap_id (zs : List R) (F : CochainComplex C ℤ) :
    tensorMap zs (𝟙 F) = 𝟙 (tensor zs F) := by
  induction zs with
  | nil => rfl
  | cons a zs ih =>
    change mappingCone.map (a • 𝟙 (tensor zs F)) (a • 𝟙 (tensor zs F))
      (tensorMap zs (𝟙 F)) (tensorMap zs (𝟙 F))
      (by simp [Linear.smul_comp, Linear.comp_smul]) = _
    simp only [ih, mappingCone.map_id]
    rfl

lemma tensorMap_comp (zs : List R) {F G H : CochainComplex C ℤ}
    (f : F ⟶ G) (g : G ⟶ H) :
    tensorMap zs (f ≫ g) = tensorMap zs f ≫ tensorMap zs g := by
  induction zs with
  | nil => rfl
  | cons a zs ih =>
    change mappingCone.map (a • 𝟙 (tensor zs F)) (a • 𝟙 (tensor zs H))
      (tensorMap zs (f ≫ g)) (tensorMap zs (f ≫ g))
      (by simp [Linear.smul_comp, Linear.comp_smul]) = _
    simp only [ih]
    exact mappingCone.map_comp _ _ _ _ _
      (by simp [Linear.smul_comp, Linear.comp_smul]) _ _
      (by simp [Linear.smul_comp, Linear.comp_smul])

 
noncomputable def tensorFunctor (zs : List R) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := tensor zs
  map := tensorMap zs
  map_id := tensorMap_id zs
  map_comp := tensorMap_comp zs

@[simp] lemma tensorFunctor_obj (zs : List R) (F : CochainComplex C ℤ) :
    (tensorFunctor zs).obj F = tensor zs F := rfl


variable [HasZeroObject C]



variable [CategoryWithHomology C]

 
noncomputable def coneHomologyProjection (f : F ⟶ G) (i : ℤ) :
    (mappingCone f).homology i ⟶ F.homology (i + 1) :=
  ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app
    (mappingCone f)).inv ≫
  (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
    (mappingCone.triangleh f).mor₃ ≫
  ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso 1 i
    (i + 1) (by omega)).hom.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj F) ≫
  ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (i + 1)).app F).hom

end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulHomologyMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

@[simp] lemma homologyMap_smul {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear R C] {F G : CochainComplex C ℤ}
    (f : F ⟶ G) (a : R) (i : ℤ) [F.HasHomology i] [G.HasHomology i] :
    homologyMap (a • f) i = a • homologyMap f i := by
  exact ShortComplex.homologyMap_smul ((shortComplexFunctor C (ComplexShape.up ℤ) i).map f) a

def entryIdeal (zs : List R) : Ideal R := Ideal.span {x | x ∈ zs}

end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
universe u v
variable {R : Type u} [CommRing R]

 
noncomputable def inclusion (F : CochainComplex (ModuleCat.{v} R) ℤ) :
    (zs : List R) → F ⟶ tensor zs F
  | [] => 𝟙 F
  | r :: zs => inclusion F zs ≫ mappingCone.inr (r • 𝟙 _)

noncomputable def retraction (F : CochainComplex (ModuleCat.{v} R) ℤ) :
    (zs : List R) → (∀ r ∈ zs, Homotopy (r • 𝟙 F) 0) → (tensor zs F ⟶ F)
  | [], _ => 𝟙 F
  | r :: zs, H => coneRetraction
      (tensorScalarHomotopy r zs (H r (by simp))) ≫
        retraction F zs (fun s hs => H s (by simp [hs]))

@[reassoc (attr := simp)]
lemma inclusion_retraction (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (H : ∀ r ∈ zs, Homotopy (r • 𝟙 F) 0) :
    inclusion F zs ≫ retraction F zs H = 𝟙 F := by
  induction zs with
  | nil => simp [inclusion, retraction]
  | cons r zs ih =>
    change (inclusion F zs ≫ mappingCone.inr (r • 𝟙 (tensor zs F))) ≫
      (coneRetraction (tensorScalarHomotopy r zs (H r (by simp))) ≫
        retraction F zs (fun s hs => H s (by simp [hs]))) = 𝟙 F
    rw [Category.assoc, ← Category.assoc (mappingCone.inr _),
      inr_coneRetraction, Category.id_comp]
    exact ih _


noncomputable def powerMap (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (a b : ℕ) (hab : a ≤ b) :
    (zs : List R) → tensor (zs.map (· ^ b)) F ⟶ tensor (zs.map (· ^ a)) F
  | [] => 𝟙 F
  | r :: zs => mappingCone.map
      (r ^ b • 𝟙 (tensor (zs.map (· ^ b)) F))
      (r ^ a • 𝟙 (tensor (zs.map (· ^ a)) F))
      (r ^ (b-a) • powerMap F a b hab zs) (powerMap F a b hab zs) (by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
          Category.comp_id, smul_smul]
        rw [← pow_add, Nat.add_sub_of_le hab])

@[reassoc (attr := simp)]
lemma powerMap_inclusion (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (a b : ℕ) (hab : a ≤ b) (zs : List R) :
    inclusion F (zs.map (· ^ b)) ≫ powerMap F a b hab zs =
      inclusion F (zs.map (· ^ a)) := by
  induction zs with
  | nil => exact Category.id_comp _
  | cons r zs ih =>
    change (inclusion F (zs.map (· ^ b)) ≫ mappingCone.inr _) ≫
      mappingCone.map _ _ _ _ _ = inclusion F (zs.map (· ^ a)) ≫ mappingCone.inr _
    simp only [Category.assoc, mappingCone.map, mappingCone.inr_desc]
    exact congrArg (fun f => f ≫ mappingCone.inr _) ih




noncomputable def coneFst (F G : CochainComplex (ModuleCat.{v} R) ℤ) (f : F ⟶ G) :
    mappingCone f ⟶ F⟦(1 : ℤ)⟧ where
  f i := (mappingCone.fst f).1.v i (i + 1) rfl
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    subst j
    simp [mappingCone.d_fst_v _ i (i + 1) (i + 1 + 1) rfl rfl]

noncomputable def coneShortComplex {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) :=
  ShortComplex.mk (mappingCone.inr f) (coneFst F G f) (by
    ext i : 1
    simp [coneFst]
    all_goals rfl)

lemma coneShortComplex_shortExact {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) : (coneShortComplex f).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let s : ((coneShortComplex f).map
      (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) i)).Splitting :=
    { r := (mappingCone.snd f).v i i (by omega)
      s := (mappingCone.inl f).v (i+1) i (by omega)
      f_r := by
        change (mappingCone.inr f).f i ≫ (mappingCone.snd f).v i i _ = 𝟙 (G.X i)
        simp
      s_g := by
        change (mappingCone.inl f).v (i+1) i _ ≫ (mappingCone.fst f).1.v i (i+1) _ = 𝟙 (F.X (i+1))
        simp
      id := by
        change (mappingCone.snd f).v i i (by omega) ≫ (mappingCone.inr f).f i +
          (mappingCone.fst f).1.v i (i+1) rfl ≫ (mappingCone.inl f).v (i+1) i (by omega) =
            𝟙 ((mappingCone f).X i)
        exact (add_comm _ _).trans (mappingCone.id_X f i (i+1) rfl) }
  exact s.shortExact

noncomputable def coneShortComplexMap
    {F G F' G' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (f' : F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G')
    (h : f ≫ b = a ≫ f') : coneShortComplex f ⟶ coneShortComplex f' where
  τ₁ := b
  τ₂ := mappingCone.map f f' a b h
  τ₃ := (CategoryTheory.shiftFunctor _ (1 : ℤ)).map a
  comm₁₂ := by ext i : 1; simp [coneShortComplex, mappingCone.map]
  comm₂₃ := by
    ext i : 1
    apply (mappingCone.ext_from_iff _ (i+1) i rfl _ _).mpr
    constructor <;> simp [coneShortComplex, coneFst, mappingCone.map]




lemma scalar_comp_zero {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (r : R) (f : F ⟶ G) (h : r • 𝟙 G = 0) : (r • 𝟙 F) ≫ f = 0 := by
  calc (r • 𝟙 F) ≫ f = f ≫ (r • 𝟙 G) := by simp
       _ = 0 := by rw [h, comp_zero]

 
noncomputable def augmentation {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) : (zs : List R) → (∀ r ∈ zs, r • 𝟙 G = 0) → (tensor zs F ⟶ G)
  | [], _ => f
  | r :: zs, H => mappingCone.desc (r • 𝟙 (tensor zs F)) 0
      (augmentation f zs (fun s hs => H s (by simp [hs])))
      (by rw [scalar_comp_zero r _ (H r (by simp))]; simp)

@[reassoc (attr := simp)]
lemma inclusion_augmentation {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (zs : List R) (H : ∀ r ∈ zs, r • 𝟙 G = 0) :
    inclusion F zs ≫ augmentation f zs H = f := by
  induction zs with
  | nil => exact Category.id_comp _
  | cons r zs ih =>
    change (inclusion F zs ≫ mappingCone.inr (r • 𝟙 (tensor zs F))) ≫
      mappingCone.desc (r • 𝟙 (tensor zs F)) 0 _ _ = f
    simpa only [Category.assoc, mappingCone.inr_desc] using ih _

@[reassoc]
lemma augmentation_naturality_target
    {F G G' : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (g : G ⟶ G') (zs : List R)
    (H : ∀ r ∈ zs, r • 𝟙 G = 0) (H' : ∀ r ∈ zs, r • 𝟙 G' = 0) :
    augmentation f zs H ≫ g = augmentation (f ≫ g) zs H' := by
  induction zs with
  | nil => rfl
  | cons r zs ih =>
    change mappingCone.desc (r • 𝟙 (tensor zs F)) 0 _ _ ≫ g =
      mappingCone.desc (r • 𝟙 (tensor zs F)) 0 _ _
    ext i : 1
    apply (mappingCone.ext_from_iff (r • 𝟙 (tensor zs F)) (i+1) i rfl _ _).mpr
    constructor
    · simp [HomologicalComplex.comp_f]
    · simpa only [augmentation, HomologicalComplex.comp_f, Category.assoc,
        mappingCone.inr_f_desc_f_assoc, mappingCone.inr_f_desc_f] using
        congrArg (fun f => f.f i) (ih _ _)

 
@[reassoc]
lemma powerMap_augmentation {F G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ G) (zs : List R) (a b : ℕ) (hab : a ≤ b)
    (Ha : ∀ r ∈ zs.map (· ^ a), r • 𝟙 G = 0)
    (Hb : ∀ r ∈ zs.map (· ^ b), r • 𝟙 G = 0) :
    powerMap F a b hab zs ≫ augmentation f (zs.map (· ^ a)) Ha =
      augmentation f (zs.map (· ^ b)) Hb := by
  induction zs with
  | nil => exact Category.id_comp _
  | cons r zs ih =>
    change mappingCone.map _ _ _ _ _ ≫ mappingCone.desc _ 0 _ _ =
      mappingCone.desc _ 0 _ _
    ext i : 1
    apply (mappingCone.ext_from_iff _ (i+1) i rfl _ _).mpr
    constructor
    · simp [mappingCone.map, HomologicalComplex.comp_f, Category.assoc]
    · simpa [mappingCone.map, HomologicalComplex.comp_f, Category.assoc] using
        congrArg (fun f => f.f i) (ih _ _)

noncomputable def quotientAugmentation
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) :
    tensor zs F ⟶ (complexQuotient (entryIdeal zs) (.up ℤ)).obj F :=
  augmentation (complexQuotientπ _ F) zs (fun r hr =>
    complexQuotient_annihilated _ r (Ideal.subset_span hr) F)

@[reassoc (attr := simp)]
lemma quotientAugmentation_inclusion
    (F : CochainComplex (ModuleCat.{v} R) ℤ) (zs : List R) :
    inclusion F zs ≫ quotientAugmentation F zs =
      complexQuotientπ (entryIdeal zs) F :=
  inclusion_augmentation _ zs _

end Lech.Koszul
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechNatTrans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex HomologicalComplex
universe u v
variable {R : Type u} [CommRing R]

@[reassoc]
lemma augmentation_naturality_source
    {F F' G : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : F ⟶ F') (g : F' ⟶ G) (zs : List R) (H : ∀ r ∈ zs, r • 𝟙 G = 0) :
    (tensorFunctor zs).map f ≫ augmentation g zs H = augmentation (f ≫ g) zs H := by
  induction zs with
  | nil => rfl
  | cons r zs ih =>
    change mappingCone.map _ _ _ _ (by simp [Linear.smul_comp, Linear.comp_smul]) ≫ mappingCone.desc _ 0 _ _ =
      mappingCone.desc _ 0 _ _
    ext i : 1
    apply (mappingCone.ext_from_iff _ (i+1) i rfl _ _).mpr
    constructor
    · simp [mappingCone.map, HomologicalComplex.comp_f, Category.assoc]
    · simpa [mappingCone.map, HomologicalComplex.comp_f, Category.assoc, tensorFunctor, tensorMap] using
        congrArg (fun f => f.f i) (ih _)

@[reassoc]
lemma complexQuotientπ_naturality (I : Ideal R)
    {F G : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ G) :
    f ≫ complexQuotientπ I G = complexQuotientπ I F ≫ (complexQuotient I (.up ℤ)).map f := by
  ext i : 1
  exact (moduleQuotientπ I).naturality (f.f i)




lemma tensor_isZero_above (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (n : ℤ) (hF : ∀ j, n < j → IsZero (F.X j)) :
    ∀ j, n < j → IsZero ((tensor zs F).X j) := by
  induction zs with
  | nil => exact hF
  | cons r zs ih =>
    intro j hj
    have hS := coneShortComplex_shortExact (r • 𝟙 (tensor zs F))
    have := hS.mono_f
    have := hS.epi_g
    exact (hS.map (eval _ _ j)).exact.isZero_of_both_isZero
      (ih j hj) (ih (j+1) (by omega))

lemma coneInr_isIso_at_top (F G : CochainComplex (ModuleCat.{v} R) ℤ)
    (f : F ⟶ G) (n : ℤ) (hF : IsZero (F.X (n+1))) :
    IsIso ((mappingCone.inr f).f n) := by
  have hS := coneShortComplex_shortExact f
  have := hS.mono_f
  have := hS.epi_g
  exact (hS.map (eval _ _ n)).isIso_f_iff.mpr hF

lemma inclusion_isIso_at_top (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (n : ℤ) (hF : ∀ j, n < j → IsZero (F.X j)) :
    IsIso ((inclusion F zs).f n) := by
  induction zs with
  | nil => change IsIso (𝟙 (F.X n)); infer_instance
  | cons r zs ih =>
    have := coneInr_isIso_at_top _ _ (r • 𝟙 (tensor zs F)) n
      (tensor_isZero_above F zs n hF (n+1) (by omega))
    change IsIso ((inclusion F zs).f n ≫ (mappingCone.inr (r • 𝟙 (tensor zs F))).f n)
    infer_instance



noncomputable def projectionTerm (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) : (zs : List R) → ((tensor zs F).X n ⟶ F.X n)
  | [] => 𝟙 _
  | r :: zs => (mappingCone.snd (r • 𝟙 (tensor zs F))).v n n (by omega) ≫
      projectionTerm F n zs

@[reassoc (attr := simp)]
lemma inclusion_projectionTerm (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (n : ℤ) (zs : List R) :
    (inclusion F zs).f n ≫ projectionTerm F n zs = 𝟙 _ := by
  induction zs with
  | nil => simp [inclusion, projectionTerm]
  | cons r zs ih =>
    change ((inclusion F zs).f n ≫ (mappingCone.inr (r • 𝟙 (tensor zs F))).f n) ≫
      ((mappingCone.snd (r • 𝟙 (tensor zs F))).v n n (by omega) ≫ projectionTerm F n zs) = _
    simpa only [Category.assoc, mappingCone.inr_f_snd_v_assoc] using ih

lemma entryIdeal_cons_for_top (r : R) (zs : List R) :
    entryIdeal (r::zs) = Ideal.span {r} ⊔ entryIdeal zs := by
  simp only [entryIdeal, List.mem_cons, Set.ofPred_or, Set.ofPred_eq_eq_singleton,
    Ideal.span_union]



lemma augmentation_f_at_top
    {F G : CochainComplex (ModuleCat.{v} R) ℤ} (f : F ⟶ G) (zs : List R)
    (H : ∀ r ∈ zs, r • 𝟙 G = 0) (n : ℤ)
    (hF : ∀ j, n < j → IsZero (F.X j)) :
    (augmentation f zs H).f n = projectionTerm F n zs ≫ f.f n := by
  have := inclusion_isIso_at_top F zs n hF
  apply (cancel_epi ((inclusion F zs).f n)).mp
  rw [← Category.assoc, inclusion_projectionTerm, Category.id_comp]
  exact congrArg (fun f => f.f n) (inclusion_augmentation f zs H)



end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFlatVariables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise

open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace Lech.Koszul

variable {R : Type*} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]
variable {F G : CochainComplex C ℤ}

instance instAdditiveCochainComplexIntConeFunctor_1 (a : R) : (coneFunctor (C := C) a).Additive where
  map_add {F G} f g := by
    change mappingCone.map (a • 𝟙 F) (a • 𝟙 G) (f + g) (f + g)
        (by simp [Linear.smul_comp, Linear.comp_smul]) =
      mappingCone.map (a • 𝟙 F) (a • 𝟙 G) f f (by simp [Linear.smul_comp, Linear.comp_smul]) +
        mappingCone.map (a • 𝟙 F) (a • 𝟙 G) g g (by simp [Linear.smul_comp, Linear.comp_smul])
    ext i
    rw [HomologicalComplex.add_f_apply]
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map,
      HomologicalComplex.add_f_apply, Preadditive.add_comp, Preadditive.comp_add]



end Lech.Koszul

open scoped ENNReal ZeroObject

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex











open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian




end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulConeFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C]
  [CategoryTheory.Linear R C]

instance coneFunctor_linear (a : R) : Functor.Linear R (coneFunctor (C := C) a) where
  map_smul f r := by
    rename_i F G
    change mappingCone.map (a • 𝟙 F) (a • 𝟙 G) (r • f) (r • f)
        (by
          simp only [Linear.smul_comp, Linear.comp_smul, Category.comp_id, Category.id_comp]
          exact smul_comm r a f) =
      r • mappingCone.map (a • 𝟙 F) (a • 𝟙 G) f f
        (by simp [Linear.smul_comp, Linear.comp_smul])
    ext i
    rw [smul_f_apply]
    simp [mappingCone.ext_from_iff _ (i+1) i rfl, mappingCone.map,
      smul_f_apply,Linear.smul_comp,Linear.comp_smul]

end Lech.Koszul


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

noncomputable def coneTermEquiv (F : CochainComplex (ModuleCat.{u} R) ℤ) (a : R) (i : ℤ) :
    (mappingCone (a • 𝟙 F)).X i ≃ₗ[R] (F.X (i+1) × F.X i) :=
  (homotopyCofiber.XIsoBiprod (a • 𝟙 F) i (i+1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv

end Lech.Koszul


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]



structure IsFiniteHomologyComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  term_free : ∀ i, Module.Free R (F.X i)
  term_finite : ∀ i, Module.Finite R (F.X i)
  bounded : ∀ i, i < -(dimension R : ℤ) ∨ 0 < i → IsZero (F.X i)
  homology_finite_length : ∀ i, IsFiniteLength R (F.homology i)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealFilteredLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {M N : Type u}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (J K : Ideal R) (f : M →ₗ[R] N)

 
def restrictIdeal : ↥(K • (⊤ : Submodule R M)) →ₗ[R] ↥(K • (⊤ : Submodule R N)) :=
  (f.comp (K • (⊤ : Submodule R M)).subtype).codRestrict _
    (fun x => Submodule.smul_top_le_comap_smul_top K f x.property)

lemma restrictIdeal_range (hf : f.range=J • (⊤ : Submodule R N)) :
    (restrictIdeal K f).range=J • (⊤ : Submodule R ↥(K • (⊤ : Submodule R N))) := by
  apply Submodule.map_injective_of_injective (K • (⊤ : Submodule R N)).subtype_injective
  rw [←LinearMap.range_comp,Submodule.map_smul'',Submodule.map_top,Submodule.range_subtype]
  change (f.comp (K • (⊤ : Submodule R M)).subtype).range = J • (K • (⊤ : Submodule R N))
  rw [LinearMap.range_comp,Submodule.range_subtype,Submodule.map_smul'',Submodule.map_top,hf,
    ←Submodule.mul_smul,←Submodule.mul_smul,mul_comm]

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryTheory.Linear R C]

abbrev scalarCone (a : R) (F : CochainComplex C ℤ) := mappingCone (a • 𝟙 F)
noncomputable abbrev cInl (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    F.X (i+1) ⟶ (scalarCone a F).X i :=
  homotopyCofiber.inlX (a • 𝟙 F) (i+1) i rfl
noncomputable abbrev cInr (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    F.X i ⟶ (scalarCone a F).X i := homotopyCofiber.inrX (a • 𝟙 F) i
noncomputable abbrev cFst (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    (scalarCone a F).X i ⟶ F.X (i+1) :=
  homotopyCofiber.fstX (a • 𝟙 F) i (i+1) rfl
noncomputable abbrev cSnd (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    (scalarCone a F).X i ⟶ F.X i := homotopyCofiber.sndX (a • 𝟙 F) i

@[reassoc (attr := simp)] lemma cInl_fst (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl a F i ≫ cFst a F i = 𝟙 _ := homotopyCofiber.inlX_fstX _ _ _ _
@[reassoc (attr := simp)] lemma cInl_snd (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl a F i ≫ cSnd a F i = 0 := homotopyCofiber.inlX_sndX _ _ _ _
@[reassoc (attr := simp)] lemma cInr_fst (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr a F i ≫ cFst a F i = 0 := homotopyCofiber.inrX_fstX _ _ _ _
@[reassoc (attr := simp)] lemma cInr_snd (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr a F i ≫ cSnd a F i = 𝟙 _ := homotopyCofiber.inrX_sndX _ _

@[reassoc] lemma cInl_d (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl a F i ≫ (scalarCone a F).d i (i+1) =
    -(F.d (i+1) (i+1+1) ≫ cInl a F (i+1)) + a • cInr a F (i+1) := by
  change homotopyCofiber.inlX (a • 𝟙 F) (i+1) i rfl ≫
    homotopyCofiber.d (a • 𝟙 F) i (i+1) = _
  rw [homotopyCofiber.inlX_d (a • 𝟙 F) i (i+1) (i+1+1) rfl rfl]
  change -F.d (i+1) (i+1+1) ≫ cInl a F (i+1) +
    (a • 𝟙 F).f (i+1) ≫ cInr a F (i+1) = _
  simp only [HomologicalComplex.smul_f_apply,HomologicalComplex.id_f,
    Linear.smul_comp,Category.id_comp]
@[reassoc] lemma cInr_d (a : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr a F i ≫ (scalarCone a F).d i (i+1) =
      F.d i (i+1) ≫ cInr a F (i+1) :=
  homotopyCofiber.inrX_d _ _ _

noncomputable def coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    (scalarCone a (scalarCone b F)).X i ⟶ (scalarCone b (scalarCone a F)).X i :=
  -(cFst a (scalarCone b F) i ≫ cFst b F (i+1) ≫
    cInl a F (i+1) ≫ cInl b (scalarCone a F) i) +
  cFst a (scalarCone b F) i ≫ cSnd b F (i+1) ≫
    cInl a F i ≫ cInr b (scalarCone a F) i +
  cSnd a (scalarCone b F) i ≫ cFst b F i ≫
    cInr a F (i+1) ≫ cInl b (scalarCone a F) i +
  cSnd a (scalarCone b F) i ≫ cSnd b F i ≫
    cInr a F i ≫ cInr b (scalarCone a F) i

@[reassoc (attr := simp)] lemma inll_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ coneSwapX a b F i =
      -(cInl a F (i+1) ≫ cInl b (scalarCone a F) i) := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]
@[reassoc (attr := simp)] lemma inrl_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ coneSwapX a b F i =
      cInl a F i ≫ cInr b (scalarCone a F) i := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]
@[reassoc (attr := simp)] lemma inlr_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInl b F i ≫ cInr a (scalarCone b F) i ≫ coneSwapX a b F i =
      cInr a F (i+1) ≫ cInl b (scalarCone a F) i := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]
@[reassoc (attr := simp)] lemma inrr_coneSwapX (a b : R) (F : CochainComplex C ℤ) (i : ℤ) :
    cInr b F i ≫ cInr a (scalarCone b F) i ≫ coneSwapX a b F i =
      cInr a F i ≫ cInr b (scalarCone a F) i := by
  simp [coneSwapX,Preadditive.comp_add,Preadditive.comp_neg]

noncomputable def coneSwap (a b : R) (F : CochainComplex C ℤ) :
    scalarCone a (scalarCone b F) ⟶ scalarCone b (scalarCone a F) where
  f := coneSwapX a b F
  comm' := by
    intro i j hij
    obtain rfl : i+1=j := hij
    apply homotopyCofiber.ext_from_X (a • 𝟙 (scalarCone b F)) (i+1) i rfl
    · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1+1) (i+1) rfl
      · change cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
          cInl b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
        simp only [Category.assoc,cInl_d_assoc,cInl_d,
          Preadditive.comp_neg,Preadditive.comp_add,Preadditive.neg_comp,
          Preadditive.add_comp,Linear.comp_smul,Linear.smul_comp,
          inll_coneSwapX_assoc,inll_coneSwapX,inrl_coneSwapX,inlr_coneSwapX,
          neg_neg]
        abel
      · change cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _ =
          cInr b F (i+1) ≫ cInl a (scalarCone b F) i ≫ _
        simp only [Category.assoc,cInl_d_assoc,cInr_d_assoc,cInr_d,
          Preadditive.comp_neg,Preadditive.comp_add,Preadditive.neg_comp,
          Preadditive.add_comp,Linear.comp_smul,Linear.smul_comp,
          inrl_coneSwapX_assoc,inrl_coneSwapX,inrr_coneSwapX]
    · apply homotopyCofiber.ext_from_X (b • 𝟙 F) (i+1) i rfl
      · change cInl b F i ≫ cInr a (scalarCone b F) i ≫ _ =
          cInl b F i ≫ cInr a (scalarCone b F) i ≫ _
        simp only [Category.assoc,cInl_d_assoc,cInr_d_assoc,cInl_d,
          Preadditive.comp_neg,Preadditive.comp_add,Preadditive.neg_comp,
          Preadditive.add_comp,Linear.comp_smul,Linear.smul_comp,
          inlr_coneSwapX_assoc,inlr_coneSwapX,inrr_coneSwapX]
      · change cInr b F i ≫ cInr a (scalarCone b F) i ≫ _ =
          cInr b F i ≫ cInr a (scalarCone b F) i ≫ _
        simp only [cInr_d_assoc,cInr_d,inrr_coneSwapX_assoc,inrr_coneSwapX]

end Lech.Koszul

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_MinimalComplexReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

def IsMinimalComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop :=
  ∀ i : ℤ,(F.d i (i+1)).hom.range ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (F.X (i+1)))

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ModuleComplexQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ModuleComplexQuotient
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{u} R) c)
  (P : ∀ p,Submodule R (K.X p))
  (hP : ∀ p q,P p ≤ (P q).comap (K.d p q).hom)

 
def complex : HomologicalComplex (ModuleCat.{u} R) c where
  X p := ModuleCat.of R ((K.X p) ⧸ P p)
  d p q := ModuleCat.ofHom ((P p).mapQ (P q) (K.d p q).hom (hP p q))
  shape p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((K.d p q).hom x)=0
        rw [K.shape p q hpq]
        exact Submodule.Quotient.mk_zero _
  d_comp_d' p q r _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((K.d q r).hom ((K.d p q).hom x))=0
        have he := congrArg (fun f : K.X p ⟶ K.X r => f.hom x) (K.d_comp_d p q r)
        change (K.d q r).hom ((K.d p q).hom x)=0 at he
        rw [he]
        exact Submodule.Quotient.mk_zero _

variable {K} {P hP}
  {L : HomologicalComplex (ModuleCat.{u} R) c}
  {Q : ∀ p,Submodule R (L.X p)} {hQ : ∀ p q,Q p ≤ (Q q).comap (L.d p q).hom}
  (f : K ⟶ L) (hf : ∀ p,P p ≤ (Q p).comap (f.f p).hom)

def map : complex K P hP ⟶ complex L Q hQ where
  f p := ModuleCat.ofHom ((P p).mapQ (Q p) (f.f p).hom (hf p))
  comm' p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((L.d p q).hom ((f.f p).hom x))=
          Submodule.Quotient.mk ((f.f q).hom ((K.d p q).hom x))
        exact congrArg (fun g : K.X p ⟶ L.X q => Submodule.Quotient.mk (g.hom x)) (f.comm p q)

end Lech.ModuleComplexQuotient

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootUnfiltered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)

lemma zero_order_bound (p : ℤ) :
    (F.d p (p+1)).hom.range ≤ I^0 • (⊤ : Submodule R (F.X (p+1))) := by simp

end Lech.IdealFiltered

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SymmetricAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.IntegerWeights
open Function

 
def SeparatelyAffine {ι : Type*} [DecidableEq ι] (f : (ι → ℤ) → ℝ) : Prop :=
  ∀ (m : ι → ℤ) (i : ι) (a : ℤ),
    f (update m i a)=f (update m i 0)+(a:ℝ)*(f (update m i 1)-f (update m i 0))


end Lech.IntegerWeights

end

end OAI
end


