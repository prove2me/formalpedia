-- Prove2me | Definitions.Def_OAIQ031A111
-- name    : OAIQ031A111
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:46:51.411033+00:00
-- url     : https://prove2.me/theorems/ec33c02a-989d-405f-aa30-86f929625e44
-- title:
--   Definitions bundle OAIQ031A111 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 4 definitions and 8 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.totalEvaluationIso`, `OAI.ArExplicit.ExternalTensor.barCyclicCover`, `OAI.ArExplicit.ExternalTensor.homTensorMap`, `OAI.ArExplicit.TwoCone.topAttaching`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ExternalBarFreeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarFreeAugmentation.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Ext_ExtKunnethMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunnethMap.lean), [`AuslanderReiten_Ext_ExternalEvaluationCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationCubic.lean), [`AuslanderReiten_Ext_ExternalEvaluationCubicSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationCubicSquare.lean), [`AuslanderReiten_Ext_ExternalEvaluationDifferential`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationDifferential.lean), [`AuslanderReiten_Ext_ExternalEvaluationSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationSquare.lean), [`AuslanderReiten_Tensor_EnvelopingCoefficientComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingCoefficientComplex.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A095`, `OAIQ031A096`, `OAIQ031A098`, `OAIQ031A099` and `OAIQ031A100` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A122`, `OAIQ031A123` and `OAIQ031A124`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A095
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A098
import Definitions.Def_OAIQ031A099
import Definitions.Def_OAIQ031A100

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarFreeAugmentation
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

def barCyclicCover :
    ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) ⟶ canonicalTensorObject k A B M N :=
  (regularEquiv k A B).toModuleIso.inv ≫
    (canonicalTensorIso k A B A B).inv ≫
      mapHom k A B (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
        (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

def topAttaching (n : ℕ) : D.term (n + 5) →ₗ[R] skeletonTerm D n :=
  (0 : D.term (n + 5) →ₗ[R] D.term n).prod
    ((D.second (n + 2)).prod (-(D.first (n + 2))))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k : Type u) [Field k]

variable (R : Type u) [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (U : Type u) [AddCommGroup U] [Module R U] [Module k U] [IsScalarTower k R U]

variable (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [Module.Finite k A] [Module.Finite k B]
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (f : homCochain k A P.complex U ⟶ homCochain k A P.complex U)
variable (g : homCochain k B Q.complex V ⟶ homCochain k B Q.complex V)
local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)

def homTensorMap :
    homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex) (moduleObject k A B U V) ⟶
      homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex) (moduleObject k A B U V) :=
  (homCochainTotalIso k A B P.complex Q.complex U V).inv ≫
    mapBifunctorMap f g T (.up ℕ) ≫
      (homCochainTotalIso k A B P.complex Q.complex U V).hom

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationSquare
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q

theorem horizontal_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+1+j=n+1) :
    (E).map (ExternalTensor.mapHom k Ae Be (P.d (i+1) i) (𝟙 (Q.X j))) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i+1,j),h'⟩).hom ≫
      ExternalTensor.mapHom k A B ((PE).d (i+1) i) (𝟙 ((QE).X j)) := by
  have hs := shuffle_natural_fixed k A B X Y (P.d (i+1) i) (𝟙 (Q.X j))
  rw [(EnvelopingBimodule.evaluationFunctor k B Y).map_id] at hs
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl

theorem vertical_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+(j+1)=n+1) :
    (E).map (ExternalTensor.mapHom k Ae Be (𝟙 (P.X i)) (Q.d (j+1) j)) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i,j+1),h'⟩).hom ≫
      ExternalTensor.mapHom k A B (𝟙 ((PE).X i)) ((QE).d (j+1) j) := by
  have hs := shuffle_natural_fixed k A B X Y (𝟙 (P.X i)) (Q.d (j+1) j)
  rw [(EnvelopingBimodule.evaluationFunctor k A X).map_id] at hs
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationCubicSquare
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "QE" => factorEvaluation k Y Q

theorem firstCubic_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+3+j=n+3)
    (p : P.X (i+3) ⟶ P.X i) :
    (E).map (ExternalTensor.mapHom k Ae Be p (𝟙 (Q.X j))) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+3) ⟨(i+3,j),h'⟩).hom ≫
      ExternalTensor.mapHom k A B ((EnvelopingBimodule.evaluationFunctor k A X).map p)
        (𝟙 ((QE).X j)) := by
  have hs := shuffle_natural_fixed k A B X Y p (𝟙 (Q.X j))
  rw [(EnvelopingBimodule.evaluationFunctor k B Y).map_id] at hs
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationDifferential
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q

theorem horizontal_totalEvaluation (i j n : ℕ) (h : i+j=n+1) :
    (E).map (ExternalTensor.horizontal k Ae Be P Q i j n) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i,j),h⟩).hom ≫
      ExternalTensor.horizontal k A B PE QE i j n := by
  cases i with
  | zero => erw [ExternalTensor.horizontal_zero, Functor.map_zero,
      zero_comp, ExternalTensor.horizontal_zero k A B PE QE, comp_zero]
  | succ i =>
    have hij : i+j=n := by omega
    erw [ExternalTensor.horizontal_succ k Ae Be P Q i j n hij,
      (E).map_comp, Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q i j n hij]
    erw [ExternalTensor.horizontal_succ k A B PE QE i j n hij, ← Category.assoc]
    exact congrArg (fun f => f ≫ ExternalTensor.inclusion k A B PE QE i j n hij)
      (horizontal_summand_natural k A B X Y P Q i j n hij h)

theorem vertical_totalEvaluation (i j n : ℕ) (h : i+j=n+1) :
    (E).map (ExternalTensor.vertical k Ae Be P Q i j n) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (summandEvaluationIso k A B X Y P Q (n+1) ⟨(i,j),h⟩).hom ≫
      ExternalTensor.vertical k A B PE QE i j n := by
  cases j with
  | zero => erw [ExternalTensor.vertical_zero, Functor.map_zero,
      zero_comp, ExternalTensor.vertical_zero k A B PE QE, comp_zero]
  | succ j =>
    have hij : i+j=n := by omega
    erw [ExternalTensor.vertical_succ k Ae Be P Q i j n hij,
      (E).map_units_smul, Linear.units_smul_comp, (E).map_comp, Category.assoc,
      inclusion_totalEvaluationTermIso k A B X Y P Q i j n hij]
    erw [ExternalTensor.vertical_succ k A B PE QE i j n hij, Linear.comp_units_smul,
      ← Category.assoc]
    apply congrArg (fun f => ((-1 : ℤˣ)^i) • f)
    exact congrArg (fun f => f ≫ ExternalTensor.inclusion k A B PE QE i j n hij)
      (vertical_summand_natural k A B X Y P Q i j n hij h)

theorem totalEvaluationTermIso_d (m : ℕ) :
    (totalEvaluationTermIso k A B X Y P Q (m+1)).hom ≫
      (totalEvaluated k A B X Y P Q).d (m+1) m =
    (evaluatedTotal k A B X Y P Q).d (m+1) m ≫
      (totalEvaluationTermIso k A B X Y P Q m).hom := by
  apply evaluatedTotal_hom_ext k A B X Y P Q
  intro i j hij
  symm
  change (E).map (ExternalTensor.inclusion k Ae Be P Q i j (m+1) hij) ≫
    ((E).map ((ExternalTensor.complex k Ae Be P Q).d (m+1) m) ≫
      (totalEvaluationTermIso k A B X Y P Q m).hom) =
    (E).map (ExternalTensor.inclusion k Ae Be P Q i j (m+1) hij) ≫
      ((totalEvaluationTermIso k A B X Y P Q (m+1)).hom ≫
        (totalEvaluated k A B X Y P Q).d (m+1) m)
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_d, (E).map_add,
    Preadditive.add_comp, horizontal_totalEvaluation k A B X Y P Q i j m hij,
    vertical_totalEvaluation k A B X Y P Q i j m hij]
  erw [← Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q i j (m+1) hij,
    Category.assoc, ExternalTensor.inclusion_d, Preadditive.comp_add]

def totalEvaluationIso : evaluatedTotal k A B X Y P Q ≅ totalEvaluated k A B X Y P Q :=
  HomologicalComplex.Hom.isoOfComponents (totalEvaluationTermIso k A B X Y P Q)
    (fun n m h => by
      have hnm : m+1=n := h
      subst n
      exact totalEvaluationTermIso_d k A B X Y P Q m)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (r : ∀ n, Q.X (n+3) ⟶ Q.X n)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q

theorem firstCubic_totalEvaluation (n : ℕ) :
    (E).map (ModuleCat.ofHom (ExternalTensor.firstCubic k Ae Be P Q p n)) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (totalEvaluationTermIso k A B X Y P Q (n+3)).hom ≫
      ModuleCat.ofHom (ExternalTensor.firstCubic k A B PE QE
        (evaluatedFirstComparison k A X P p) n) := by
  apply evaluatedTotal_hom_ext k A B X Y P Q
  intro i j hij
  have hpost := post_natural (inclusion_totalEvaluationTermIso k A B X Y P Q i j (n+3) hij)
    (ModuleCat.ofHom (ExternalTensor.firstCubic k A B PE QE (evaluatedFirstComparison k A X P p) n))
  erw [hpost, ExternalTensor.inclusion_firstCubic k A B PE QE (evaluatedFirstComparison k A X P p) i j n hij]
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_firstCubic k Ae Be P Q p i j n hij]
  by_cases hi : i < 3
  · have hi : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hi with rfl | rfl | rfl <;>
      change (E).map (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals erw [Functor.map_zero, zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, i=a+3 := ⟨i-3, by omega⟩
    subst i
    erw [ExternalTensor.firstCubicEntry_high k Ae Be P Q p a j n hij,
      ExternalTensor.firstCubicEntry_high k A B PE QE (evaluatedFirstComparison k A X P p) a j n hij,
      (E).map_comp, Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q a j n (by omega)]
    erw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun z => z ≫ ExternalTensor.inclusion k A B PE QE a j n (by omega))
      (firstCubic_summand_natural k A B X Y P Q a j n (by omega) hij (p a))

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingCoefficientComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable {X Y : ModuleCat.{u} R}
variable [Module k X] [IsScalarTower k R X] [Module k Y] [IsScalarTower k R Y]
variable (e : X ≅ Y) (P : ChainComplex (ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) ℕ)

theorem coefficientComplexIso_comparison (m n : ℕ) (f : P.X m ⟶ P.X n) :
    (evaluationFunctor k R X).map f ≫ (coefficientComplexIso k R e P).hom.f n =
      (coefficientComplexIso k R e P).hom.f m ≫ (evaluationFunctor k R Y).map f :=
  (evaluationCoefficientIso k R e).hom.naturality f

end ArExplicit.EnvelopingBimodule

end

end OAI
end


