-- Prove2me | Definitions.Def_OAIQ031A072
-- name    : OAIQ031A072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:17:33.369664+00:00
-- url     : https://prove2.me/theorems/cd9522a9-3f95-44f3-af47-db64caea1ce6
-- title:
--   Definitions bundle OAIQ031A072 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 4 definitions, 2 instances and 9 theorems. The definitions and types are `OAI.ArExplicit.ConvertedAlgebra.semisimpleQuotientEquiv`, `OAI.ArExplicit.ExternalTensor.canonicalTensorIso`, `OAI.ArExplicit.ExternalTensor.complexIso`, `OAI.ArExplicit.Triangular.semisimpleQuotientEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Ext_ExternalComplexCubicNatural`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalComplexCubicNatural.lean), [`AuslanderReiten_Ext_ExternalComplexIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalComplexIso.lean), [`AuslanderReiten_Ext_ExternalCubicInclusion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalCubicInclusion.lean), [`AuslanderReiten_Tensor_ExternalEnveloping`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalEnveloping.lean), [`AuslanderReiten_Tensor_ExternalTensorScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalar.lean), [`AuslanderReiten_Tensor_ExternalTensorScalarPure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalarPure.lean), [`AuslanderReiten_Triangular_ConvertedStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/ConvertedStructure.lean), [`AuslanderReiten_Triangular_TriangularRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularRadical.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A046`, `OAIQ031A047`, `OAIQ031A048`, `OAIQ031A052`, `OAIQ031A055`, `OAIQ031A056` and `OAIQ031A057` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A085` and `OAIQ031A087`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A046
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A048
import Definitions.Def_OAIQ031A052
import Definitions.Def_OAIQ031A055
import Definitions.Def_OAIQ031A056
import Definitions.Def_OAIQ031A057

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalComplexIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P P' P'' : ChainComplex (ModuleCat.{u} A) ℕ}
  {Q Q' Q'' : ChainComplex (ModuleCat.{u} B) ℕ}

@[simp] theorem complexMap_id : complexMap k A B (𝟙 P) (𝟙 Q) = 𝟙 (complex k A B P Q) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply hom_ext k A B P Q
  intro i j h
  erw [inclusion_complexMap]
  simp only [HomologicalComplex.id_f, mapHom_id, Category.id_comp, Category.comp_id]

theorem complexMap_comp (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    complexMap k A B (f ≫ f') (g ≫ g') = complexMap k A B f g ≫ complexMap k A B f' g' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply hom_ext k A B P Q
  intro i j h
  erw [inclusion_complexMap k A B (f ≫ f') (g ≫ g') i j n h]
  change mapHom k A B ((f ≫ f').f i) ((g ≫ g').f j) ≫ _ =
    inclusion k A B P Q i j n h ≫ ((complexMap k A B f g).f n ≫ (complexMap k A B f' g').f n)
  erw [← Category.assoc, inclusion_complexMap k A B f g i j n h, Category.assoc,
    inclusion_complexMap k A B f' g' i j n h, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, mapHom_comp k A B (f.f i) (f'.f i) (g.f j) (g'.f j), Category.assoc]

def complexIso (e : P ≅ P') (f : Q ≅ Q') : complex k A B P Q ≅ complex k A B P' Q' where
  hom := complexMap k A B e.hom f.hom
  inv := complexMap k A B e.inv f.inv
  hom_inv_id := by rw [← complexMap_comp, e.hom_inv_id, f.hom_inv_id, complexMap_id]
  inv_hom_id := by rw [← complexMap_comp, e.inv_hom_id, f.inv_hom_id, complexMap_id]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalCubicInclusion
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (r : ∀ n, Q.X (n+3) ⟶ Q.X n)

theorem inclusion_firstCubic (i j n : ℕ) (h : i+j=n+3) :
    inclusion k A B P Q i j (n+3) h ≫ ModuleCat.ofHom (firstCubic k A B P Q p n) =
      ModuleCat.ofHom (firstCubicEntry k A B P Q p n ⟨(i,j),h⟩) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change firstCubic k A B P Q p n ((inclusion k A B P Q i j (n+3) h).hom x) = _
  rw [inclusion_eq_cubicInsert, firstCubic_insert]
  rfl

theorem inclusion_secondCubic (i j n : ℕ) (h : i+j=n+3) :
    inclusion k A B P Q i j (n+3) h ≫ ModuleCat.ofHom (secondCubic k A B P Q r n) =
      ModuleCat.ofHom (secondCubicEntry k A B P Q r n ⟨(i,j),h⟩) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change secondCubic k A B P Q r n ((inclusion k A B P Q i j (n+3) h).hom x) = _
  rw [inclusion_eq_cubicInsert, secondCubic_insert]
  rfl

@[simp] theorem firstCubicEntry_high (i j n : ℕ) (h : i+3+j=n+3) :
    ModuleCat.ofHom (firstCubicEntry k A B P Q p n ⟨(i+3,j),h⟩) =
      mapHom k A B (p i) (𝟙 (Q.X j)) ≫
        inclusion k A B P Q i j n (by omega) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change cubicInsert k A B P Q n ⟨(i,j),_⟩ (map k A B (p i).hom LinearMap.id x) = _
  rw [← inclusion_eq_cubicInsert]
  rfl

@[simp] theorem secondCubicEntry_high (i j n : ℕ) (h : i+(j+3)=n+3) :
    ModuleCat.ofHom (secondCubicEntry k A B P Q r n ⟨(i,j+3),h⟩) =
      mapHom k A B (𝟙 (P.X i)) (r j) ≫
        inclusion k A B P Q i j n (by omega) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change cubicInsert k A B P Q n ⟨(i,j),_⟩ (map k A B LinearMap.id (r j).hom x) = _
  rw [← inclusion_eq_cubicInsert]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalComplexCubicNatural
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P P' : ChainComplex (ModuleCat.{u} A) ℕ}
  {Q Q' : ChainComplex (ModuleCat.{u} B) ℕ}
variable (f : P ⟶ P') (g : Q ⟶ Q')
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (p' : ∀ n, P'.X (n+3) ⟶ P'.X n)
variable (r : ∀ n, Q.X (n+3) ⟶ Q.X n) (r' : ∀ n, Q'.X (n+3) ⟶ Q'.X n)

theorem firstCubic_complexMap
    (hp : ∀ n, p n ≫ f.f n = f.f (n+3) ≫ p' n) (n : ℕ) :
    ModuleCat.ofHom (firstCubic k A B P Q p n) ≫ (complexMap k A B f g).f n =
      (complexMap k A B f g).f (n+3) ≫ ModuleCat.ofHom (firstCubic k A B P' Q' p' n) := by
  apply hom_ext k A B P Q
  intro i j hij
  erw [← Category.assoc, inclusion_firstCubic k A B P Q p i j n hij,
    ← Category.assoc, inclusion_complexMap k A B f g i j (n+3) hij,
    Category.assoc, inclusion_firstCubic k A B P' Q' p' i j n hij]
  by_cases hi : i<3
  · have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;> change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals simp only [zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, i=a+3 := ⟨i-3, by omega⟩
    subst i
    erw [firstCubicEntry_high k A B P Q p a j n hij,
      firstCubicEntry_high k A B P' Q' p' a j n hij,
      Category.assoc, inclusion_complexMap k A B f g a j n (by omega),
      ← Category.assoc, ← Category.assoc,
      ← mapHom_comp k A B (p a) (f.f a) (𝟙 (Q.X j)) (g.f j),
      ← mapHom_comp k A B (f.f (a+3)) (p' a) (g.f j) (𝟙 (Q'.X j)),
      Category.id_comp]
    simpa only [Category.comp_id] using congrArg
      (fun z => mapHom k A B z (g.f j) ≫ inclusion k A B P' Q' a j n (by omega)) (hp a)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnveloping
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

instance envelopingBaseModule (M : ModuleCat.{u} (ProductEnveloping k A B)) [Module k M] :
    Module k (envelopingObject k A B M) := inferInstanceAs (Module k M)

instance envelopingFinite (M : ModuleCat.{u} (ProductEnveloping k A B)) [Module k M]
    [Module.Finite k M] : Module.Finite k (envelopingObject k A B M) :=
  inferInstanceAs (Module.Finite k M)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [mM : Module k M] [mN : Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

def canonicalTensorIso : canonicalTensorObject k A B M N ≅ moduleObject k A B M N :=
  eqToIso (canonicalTensorObject_eq k A B M N)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalarPure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [μ : Module k M] [ν : Module k N] [IsScalarTower k A M] [IsScalarTower k B N]

@[simp] theorem canonicalTensorIso_tmul (x : M) (y : N) :
    (canonicalTensorIso k A B M N).hom (canonicalTmul k A B M N x y) = x ⊗ₜ[k] y := by
  cases canonicalScalar_eq k A M (mM := μ)
  cases canonicalScalar_eq k B N (mM := ν)
  rfl

@[simp] theorem canonicalTensorIso_inv_tmul (x : M) (y : N) :
    (canonicalTensorIso k A B M N).inv (x ⊗ₜ[k] y) = canonicalTmul k A B M N x y := by
  cases canonicalScalar_eq k A M (mM := μ)
  cases canonicalScalar_eq k B N (mM := ν)
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Triangular

variable {R F : Type*} [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F] [SMulCommClass R Rᵐᵒᵖ F]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k R] [Module k F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass k Rᵐᵒᵖ F]

variable {S : Type*} [Ring S] [Algebra k S]

noncomputable def semisimpleQuotientEquiv (f : R →ₐ[k] S)
    (hsurj : Function.Surjective f) (hker : Ring.jacobson R = RingHom.ker f) :
    (Triangular R F ⧸ Ring.jacobson (Triangular R F)) ≃ₐ[k] S × S :=
  (Ideal.quotientEquivAlgOfEq k (radical_eq_ker_quotientMap k f hker)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (quotientMap_surjective k f hsurj))

end Scalars
end ArExplicit.Triangular

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_ConvertedStructure
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace ConvertedAlgebra

variable {k : Type*} [Field k] (q : k) (F : Type*) [AddCommGroup F]
variable [Module (A k q) F] [Module (A k q)ᵐᵒᵖ F]
variable [SMulCommClass (A k q) (A k q)ᵐᵒᵖ F]

variable [Module k F]
variable [IsScalarTower k (A k q) F] [IsScalarTower k (A k q)ᵐᵒᵖ F]
variable [SMulCommClass k (A k q) F] [SMulCommClass k (A k q)ᵐᵒᵖ F]

noncomputable def semisimpleQuotientEquiv :
    (ConvertedAlgebra k q F ⧸ Ring.jacobson (ConvertedAlgebra k q F)) ≃ₐ[k] (Fin 8 → k) :=
  (Triangular.semisimpleQuotientEquiv (F := F) k (A.diagonalAlg q)
    (A.diagonalAlg_surjective q) (A.radical_eq_ker_diagonal q)).trans (eightCoordinates k)

end ConvertedAlgebra
end ArExplicit

end OAI
end


