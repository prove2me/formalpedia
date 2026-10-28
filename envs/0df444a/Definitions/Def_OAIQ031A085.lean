-- Prove2me | Definitions.Def_OAIQ031A085
-- name    : OAIQ031A085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:27:48.636535+00:00
-- url     : https://prove2.me/theorems/34cad004-6d2a-473e-a843-46dde49dc7b1
-- title:
--   Definitions bundle OAIQ031A085 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 14 definitions and 9 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.balancedMap`, `OAI.ArExplicit.ExternalBalanced.evaluatedFirstComparison`, `OAI.ArExplicit.ExternalBalanced.evaluatedTotal`, `OAI.ArExplicit.ExternalBalanced.exteriorMap`, `OAI.ArExplicit.ExternalBalanced.factorEvaluation`, `OAI.ArExplicit.ExternalBalanced.productEvaluation`, `OAI.ArExplicit.ExternalBalanced.scalarShuffle`, `OAI.ArExplicit.ExternalBalanced.shuffle`, `OAI.ArExplicit.ExternalBalanced.summandEvaluationIso`, `OAI.ArExplicit.ExternalBalanced.totalEvaluated`, `OAI.ArExplicit.ExternalBalanced.totalEvaluationTermIso`, `OAI.ArExplicit.ModuleBar.canonicalCoefficientComplex`, `OAI.ArExplicit.ModuleBar.coefficientScalarIso`, `OAI.ArExplicit.ModuleBar.freeCoordinate`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarFreeCoordinate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarFreeCoordinate.lean), [`AuslanderReiten_Bar_ModuleBarScalarTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarScalarTransport.lean), [`AuslanderReiten_Ext_ExternalEvaluationCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationCubic.lean), [`AuslanderReiten_Ext_ExternalEvaluationTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationTerms.lean), [`AuslanderReiten_Tensor_ExternalBalancedNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedNaturality.lean), [`AuslanderReiten_Tensor_ExternalBalancedShuffle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalBalancedShuffle.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A065`, `OAIQ031A070`, `OAIQ031A071` and `OAIQ031A072` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A097`, `OAIQ031A099`, `OAIQ031A100` and `OAIQ031A101`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A065
import Definitions.Def_OAIQ031A070
import Definitions.Def_OAIQ031A071
import Definitions.Def_OAIQ031A072

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarFreeCoordinate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (e : M ≃ₗ[k] k)

def freeCoordinate : moduleObject k R M 1 ≃ₗ[R] R where
  __ := (freeCoordinateScalar k R M e).toAddEquiv
  map_smul' a x := by
    change freeCoordinateScalar k R M e (left k R M 1 a x) =
      a * freeCoordinateScalar k R M e x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul b m =>
      rw [left_tmul, freeCoordinateScalar_tmul, freeCoordinateScalar_tmul]
      simpa only [Algebra.smul_def, mul_assoc] using
        congrArg (fun z : R => z * b) (Algebra.commutes (e m) a)

@[simp] theorem freeCoordinate_tmul (a : R) (m : M) :
    freeCoordinate k R M e (a ⊗ₜ[k] m) = e m • a :=
  freeCoordinateScalar_tmul k R M e a m

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarScalarTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [AddCommGroup M] [Module R M] [μ : Module k M] [IsScalarTower k R M]

def canonicalCoefficientComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := R) (ModuleCat.of R M)
  letI : IsScalarTower k R M := moduleCatBaseTower (k := k) (R := R) (ModuleCat.of R M)
  complex k R M

theorem canonicalCoefficientComplex_eq : canonicalCoefficientComplex k R M = complex k R M := by
  cases ExternalTensor.canonicalScalar_eq k R M (mM := μ)
  rfl

def coefficientScalarIso : canonicalCoefficientComplex k R M ≅ complex k R M :=
  eqToIso (canonicalCoefficientComplex_eq k R M)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedShuffle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
  (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
local notation "FM" => EnvelopingBimodule k A M
local notation "FN" => EnvelopingBimodule k B N
local notation "BM" => BalancedTensor k A FM X
local notation "BN" => BalancedTensor k B FN Y
local notation "Src" => BalancedTensor k (A ⊗[k] B) (exteriorBimodule k A B M N)
  (ExternalTensor.moduleObject k A B X Y)
local notation "Tgt" => ExternalTensor.moduleObject k A B BM BN

def scalarShuffle : Src ≃ₗ[k] BM ⊗[k] BN :=
  equiv (bimoduleCoordinates k A B M N) (ExternalTensor.moduleScalarCoordinates k A B X Y)
    (bimoduleCoordinates_right k A B M N) (fun _ _ _ _ => rfl)

@[simp] theorem scalarShuffle_pure (m : FM) (n : FN) (x : X) (y : Y) :
    scalarShuffle k A B M N X Y
      (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      BalancedTensor.tmul (R := A) m x ⊗ₜ[k] BalancedTensor.tmul (R := B) n y :=
  equiv_pure _ _ _ _ m n x y

theorem scalarShuffle_smul (r : A ⊗[k] B) (z : Src) :
    scalarShuffle k A B M N X Y (r • z) =
      ExternalTensor.representation k A B BM BN r (scalarShuffle k A B M N X Y z) := by
  induction r using OAI.tensorInductionOn with
  | add r s hr hs => simp only [add_smul, map_add, LinearMap.add_apply, hr, hs]
  | tmul a b =>
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add z w hz hw => simp only [smul_add, map_add, hz, hw]
    | tmul z w =>
      obtain ⟨z, rfl⟩ := (bimoduleCoordinates k A B M N).symm.surjective z
      obtain ⟨w, rfl⟩ := (ExternalTensor.moduleScalarCoordinates k A B X Y).symm.surjective w
      induction z using OAI.tensorInductionOn with
      | add z z' hz hz' => simp only [map_add, BalancedTensor.add_tmul, smul_add, hz, hz']
      | tmul m n =>
        induction w using OAI.tensorInductionOn with
        | add w w' hw hw' => simp only [map_add, BalancedTensor.tmul_add, smul_add, hw, hw']
        | tmul x y =>
          rw [BalancedTensor.smul_tmul, bimoduleCoordinates_left, scalarShuffle_pure,
            scalarShuffle_pure]
          rfl

def shuffle : Src ≃ₗ[A ⊗[k] B] Tgt where
  __ := (scalarShuffle k A B M N X Y).toAddEquiv
  map_smul' := scalarShuffle_smul k A B M N X Y

@[simp] theorem shuffle_pure (m : FM) (n : FN) (x : X) (y : Y) :
    shuffle k A B M N X Y
      (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      (BalancedTensor.tmul (R := A) m x ⊗ₜ[k] BalancedTensor.tmul (R := B) n y : Tgt) :=
  scalarShuffle_pure k A B M N X Y m n x y

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalBalancedNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable {k A B : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def balancedMap {R : Type u} [Ring R] [Algebra k R]
    {M M' : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)} {X X' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : X ⟶ X') :
    BalancedTensor k R (EnvelopingBimodule k R M) X →ₗ[R]
      BalancedTensor k R (EnvelopingBimodule k R M') X' :=
  (BalancedTensor.mapRight (k := k) (S := R) g.hom).comp
    (EnvelopingBimodule.tensorMap X f)

@[simp] theorem balancedMap_tmul {R : Type u} [Ring R] [Algebra k R]
    {M M' : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)} {X X' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : X ⟶ X') (m : EnvelopingBimodule k R M) (x : X) :
    balancedMap f g (BalancedTensor.tmul m x) =
      BalancedTensor.tmul (EnvelopingBimodule.map f m) (g.hom x) := rfl

variable {M M' : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)}
  {N N' : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)} {X X' : ModuleCat.{u} A} {Y Y' : ModuleCat.{u} B}
  (f : M ⟶ M') (g : N ⟶ N') (h : X ⟶ X') (j : Y ⟶ Y')

def exteriorMap :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N) ⟶
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M' N') :=
  (ExternalTensor.envelopingFunctor k A B).map
    (ExternalTensor.mapHom k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) f g)

@[simp] theorem coordinates_map (m : EnvelopingBimodule k A M) (n : EnvelopingBimodule k B N) :
    EnvelopingBimodule.map (exteriorMap f g)
      ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n)) =
    (bimoduleCoordinates k A B M' N').symm
      ((EnvelopingBimodule.map f m) ⊗ₜ[k] (EnvelopingBimodule.map g n)) := by
  apply EnvelopingBimodule.ext
  rfl

@[simp] theorem scalarCoordinates_map (x : X) (y : Y) :
    (ExternalTensor.mapHom k A B h j).hom
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)) =
    (ExternalTensor.moduleScalarCoordinates k A B X' Y').symm
      ((h.hom x) ⊗ₜ[k] (j.hom y)) := rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationTerms
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

abbrev productEvaluation := ExternalTensor.envelopingFunctor k A B ⋙
  EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B) (ExternalTensor.moduleObject k A B X Y)

abbrev factorEvaluation {S : Type u} [Ring S] [Algebra k S] (Z : ModuleCat.{u} S)
    (P : ChainComplex (ModuleCat.{u} (S ⊗[k] Sᵐᵒᵖ)) ℕ) :=
  ((EnvelopingBimodule.evaluationFunctor k S Z).mapHomologicalComplex (ComplexShape.down ℕ)).obj P

variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ

abbrev evaluatedTotal := ((productEvaluation k A B X Y).mapHomologicalComplex
  (ComplexShape.down ℕ)).obj (ExternalTensor.complex k Ae Be P Q)

abbrev totalEvaluated := ExternalTensor.complex k A B
  (factorEvaluation k X P) (factorEvaluation k Y Q)

def summandEvaluationIso (n : ℕ) (ij : ExternalTensor.Diagonal n) :
    (productEvaluation k A B X Y).obj (ExternalTensor.summands k Ae Be P Q n ij) ≅
      ExternalTensor.summands k A B (factorEvaluation k X P) (factorEvaluation k Y Q) n ij :=
  (shuffle k A B (P.X ij.val.1) (Q.X ij.val.2) X Y).toModuleIso

def totalEvaluationTermIso (n : ℕ) : (evaluatedTotal k A B X Y P Q).X n ≅
    (totalEvaluated k A B X Y P Q).X n :=
  (PreservesCoproduct.iso (productEvaluation k A B X Y)
    (ExternalTensor.summands k Ae Be P Q n)) ≪≫
      Sigma.mapIso (summandEvaluationIso k A B X Y P Q n)

@[reassoc] theorem inclusion_totalEvaluationTermIso (i j n : ℕ) (h : i+j=n) :
    (productEvaluation k A B X Y).map (ExternalTensor.inclusion k Ae Be P Q i j n h) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom ≫
      ExternalTensor.inclusion k A B (factorEvaluation k X P) (factorEvaluation k Y Q) i j n h := by
  dsimp only [totalEvaluationTermIso]
  have hι := map_coproduct_inclusion (productEvaluation k A B X Y)
    (ExternalTensor.summands k Ae Be P Q n) ⟨(i,j),h⟩
  erw [Iso.trans_hom, ← Category.assoc, hι, Sigma.ι_mapIso_hom]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
local notation "PE" => factorEvaluation k X P

def evaluatedFirstComparison (n : ℕ) : (PE).X (n+3) ⟶ (PE).X n :=
  (EnvelopingBimodule.evaluationFunctor k A X).map (p n)

end ArExplicit.ExternalBalanced

end

end OAI
end


