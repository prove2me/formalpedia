-- Prove2me | Definitions.Def_OAIQ031A087
-- name    : OAIQ031A087
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:26:28.777166+00:00
-- url     : https://prove2.me/theorems/be31fa76-01d5-4154-938a-4376eda83556
-- title:
--   Definitions bundle OAIQ031A087 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 3 definitions, 1 instance and 4 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.tensorCyclicCover`, `OAI.ArExplicit.ExternalTensor.transportComplex`, `OAI.ArExplicit.ExternalTensor.zeroEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ExternalBarCyclicCoordinate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarCyclicCoordinate.lean), [`AuslanderReiten_Ext_ExternalComplexCubicNatural`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalComplexCubicNatural.lean), [`AuslanderReiten_Tensor_BalancedFourAddExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedFourAddExt.lean), [`AuslanderReiten_Tensor_ExternalEnveloping`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalEnveloping.lean), [`AuslanderReiten_Tensor_ExternalTensorScalarIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalarIso.lean), [`AuslanderReiten_Tensor_ExternalTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorTransport.lean), [`AuslanderReiten_Tensor_ExternalTensorZeroEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorZeroEquiv.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A070`, `OAIQ031A072`, `OAIQ031A073` and `OAIQ031A074` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A099` and `OAIQ031A101`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A070
import Definitions.Def_OAIQ031A072
import Definitions.Def_OAIQ031A073
import Definitions.Def_OAIQ031A074

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarCyclicCoordinate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

def tensorCyclicCover : (A ⊗[k] B) →ₗ[A ⊗[k] B] moduleObject k A B M N where
  toFun a := a • (show moduleObject k A B M N from e.symm 1 ⊗ₜ[k] f.symm 1)
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalComplexCubicNatural
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem secondCubic_complexMap
    (hr : ∀ n, r n ≫ g.f n = g.f (n+3) ≫ r' n) (n : ℕ) :
    ModuleCat.ofHom (secondCubic k A B P Q r n) ≫ (complexMap k A B f g).f n =
      (complexMap k A B f g).f (n+3) ≫ ModuleCat.ofHom (secondCubic k A B P' Q' r' n) := by
  apply hom_ext k A B P Q
  intro i j hij
  erw [← Category.assoc, inclusion_secondCubic k A B P Q r i j n hij,
    ← Category.assoc, inclusion_complexMap k A B f g i j (n+3) hij,
    Category.assoc, inclusion_secondCubic k A B P' Q' r' i j n hij]
  by_cases hj : j<3
  · have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj with rfl | rfl | rfl <;> change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals simp only [zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, j=a+3 := ⟨j-3, by omega⟩
    subst j
    erw [secondCubicEntry_high k A B P Q r i a n hij,
      secondCubicEntry_high k A B P' Q' r' i a n hij,
      Category.assoc, inclusion_complexMap k A B f g i a n (by omega),
      ← Category.assoc, ← Category.assoc,
      ← mapHom_comp k A B (𝟙 (P.X i)) (f.f i) (r a) (g.f a),
      ← mapHom_comp k A B (f.f i) (𝟙 (P'.X i)) (g.f (a+3)) (r' a),
      Category.id_comp]
    simpa only [Category.comp_id] using congrArg
      (fun z => mapHom k A B (f.f i) z ≫ inclusion k A B P' Q' i a n (by omega)) (hr a)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedFourAddExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open scoped TensorProduct
universe u
variable {k A B E V F G X Y Z : Type u} [Field k] [Ring A] [Ring B]
  [Algebra k A] [Algebra k B]
  [AddCommGroup E] [AddCommGroup V] [AddCommGroup F] [AddCommGroup G]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module k E] [Module k V] [Module k F] [Module k G] [Module k X] [Module k Y]
  [Module (A ⊗[k] B)ᵐᵒᵖ E] [Module (A ⊗[k] B) V]
variable (e : E ≃ₗ[k] F ⊗[k] G) (v : V ≃ₗ[k] X ⊗[k] Y)

theorem fourfold_add_hom_ext (f g : BalancedTensor k (A ⊗[k] B) E V →+ Z)
    (h : ∀ a b x y, f (BalancedTensor.tmul (e.symm (a ⊗ₜ[k] b)) (v.symm (x ⊗ₜ[k] y))) =
      g (BalancedTensor.tmul (e.symm (a ⊗ₜ[k] b)) (v.symm (x ⊗ₜ[k] y)))) : f=g := by
  apply AddMonoidHom.ext
  intro z
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul z w =>
    obtain ⟨z, rfl⟩ := e.symm.surjective z
    obtain ⟨w, rfl⟩ := v.symm.surjective w
    induction z using OAI.tensorInductionOn with
    | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, hz, hz']
    | tmul a b =>
      induction w using OAI.tensorInductionOn with
      | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, hw, hw']
      | tmul x y => exact h a b x y

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnveloping
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

instance envelopingTower (M : ModuleCat.{u} (ProductEnveloping k A B)) [Module k M]
    [IsScalarTower k (ProductEnveloping k A B) M] :
    IsScalarTower k (EnvelopingProduct k A B) (envelopingObject k A B M) :=
  IsScalarTower.of_algebraMap_smul (A := EnvelopingProduct k A B) fun a x => by
    change (envelopingEquiv k A B).symm (algebraMap k (EnvelopingProduct k A B) a) •
      (show M from x) = a • (show M from x)
    rw [AlgEquiv.commutes, algebraMap_smul]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalarIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.freeFree _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [mM : Module k M] [mN : Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

theorem selfExtScalarEquiv_eq_iso (n : ℕ)
    (x : Ext (moduleObject k A B M N) (moduleObject k A B M N) n) :
    selfExtScalarEquiv k A B M N n x =
      selfExtIso (k := k) (canonicalTensorIso k A B M N).symm n x := by
  cases canonicalScalar_eq k A M (mM := mM)
  cases canonicalScalar_eq k B N (mM := mN)
  change x = ((Ext.mk₀ (𝟙 _)).comp x (zero_add n)).comp (Ext.mk₀ (𝟙 _)) (add_zero n)
  simp

theorem selfExtScalarEquiv_symm_eq_iso (n : ℕ)
    (x : Ext (canonicalTensorObject k A B M N) (canonicalTensorObject k A B M N) n) :
    (selfExtScalarEquiv k A B M N n).symm x =
      selfExtIso (k := k) (canonicalTensorIso k A B M N) n x := by
  apply (selfExtScalarEquiv k A B M N n).injective
  rw [LinearEquiv.apply_symm_apply, selfExtScalarEquiv_eq_iso]
  simp [selfExtIso_apply]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)

local notation "F" => tensorRestriction k A B h j

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (e : ∀ n, P.X n →ₗ[k] P.X n) (f : ∀ n, Q.X n →ₗ[k] Q.X n)
variable (he : ∀ n a x, e n (a • x) = h a • e n x)
variable (hf : ∀ n b x, f n (b • x) = j b • f n x)

variable (hdP : ∀ n x, (P.d (n+1) n).hom (e (n+1) x) = e n ((P.d (n+1) n).hom x))
variable (hdQ : ∀ n x, (Q.d (n+1) n).hom (f (n+1) x) = f n ((Q.d (n+1) n).hom x))

def transportComplex : complex k A B P Q ⟶
    ((F).mapHomologicalComplex (.down ℕ)).obj (complex k A B P Q) where
  f n := transportTerm k A B h j P Q e f he hf n
  comm' n m hnm := by
    have hn : m+1=n := hnm
    subst n
    apply hom_ext k A B P Q
    intro i j' hij
    change inclusion k A B P Q i j' (m+1) hij ≫
      (transportTerm k A B h j P Q e f he hf (m+1) ≫
        (F).map ((complex k A B P Q).d (m+1) m)) =
      inclusion k A B P Q i j' (m+1) hij ≫
        ((complex k A B P Q).d (m+1) m ≫ transportTerm k A B h j P Q e f he hf m)
    rw [← Category.assoc, inclusion_transportTerm, Category.assoc,
      ← Functor.map_comp, inclusion_d, Functor.map_add, Preadditive.comp_add,
      ← Category.assoc, inclusion_d, Preadditive.add_comp,
      horizontal_transport k A B h j P Q e f he hf hdP i j' m hij,
      vertical_transport k A B h j P Q e f he hf hdQ i j' m hij]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorZeroEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

def zeroEquiv : (complex k A B P Q).X 0 ≃ₗ[A ⊗[k] B]
    moduleObject k A B (P.X 0) (Q.X 0) where
  toLinearMap := bottomProjection k A B P Q 0
  invFun := cubicInsert k A B P Q 0 ⟨(0,0),rfl⟩
  left_inv := bottomInsert_projection_zero k A B P Q
  right_inv := bottomProjection_bottom k A B P Q 0

end ArExplicit.ExternalTensor

end

end OAI
end


