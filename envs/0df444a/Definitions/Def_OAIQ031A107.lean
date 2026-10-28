-- Prove2me | Definitions.Def_OAIQ031A107
-- name    : OAIQ031A107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:44:57.829888+00:00
-- url     : https://prove2.me/theorems/c2bad80f-e024-45a4-9bce-930cd8a92c20
-- title:
--   Definitions bundle OAIQ031A107 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 6 definitions, 1 instance and 10 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.cochainTailMap`, `OAI.ArExplicit.CompleteComparison.restrictedCocycle`, `OAI.ArExplicit.CompleteComparison.restrictedEndExt`, `OAI.ArExplicit.ExternalTensor.homCochainCycleClass`, `OAI.ArExplicit.ExternalTensor.homCochainQuotientEquiv`, `OAI.ArExplicit.TwoCone.skeletonD`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_TwistedBar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TwistedBar.lean), [`AuslanderReiten_Cocycles_CocycleDetector`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleDetector.lean), [`AuslanderReiten_Cocycles_CocycleExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleExt.lean), [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_HomComplex_FullCochainProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullCochainProducts.lean), [`AuslanderReiten_HomComplex_FullCochainTail`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullCochainTail.lean), [`AuslanderReiten_HomComplex_HomCochainExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainExt.lean), [`AuslanderReiten_HomComplex_HomCochainExtClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainExtClass.lean), [`AuslanderReiten_HomComplex_PositiveFullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/PositiveFullHomProducts.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A093`, `OAIQ031A094`, `OAIQ031A095`, `OAIQ031A096`, `OAIQ031A098` and `OAIQ031A100` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A120`, `OAIQ031A129`, `OAIQ031A134` and `OAIQ031A135`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A094
import Definitions.Def_OAIQ031A095
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A098
import Definitions.Def_OAIQ031A100

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

instance twistedModuleTower (h : R ≃ₐ[k] R) (n : ℕ) :
    IsScalarTower k (Enveloping k R) (twistedObject k R h n) :=
  IsScalarTower.of_algebraMap_smul (A := Enveloping k R) fun a x => by
    change ((representation k R n).comp (twistEnveloping k R h).toAlgHom)
      (algebraMap k (Enveloping k R) a) x = a • x
    rw [AlgHom.commutes]
    rfl

theorem twistedFinite [Module.Finite k R] (h : R ≃ₐ[k] R) (n : ℕ) :
    Module.Finite (Enveloping k R) (twistedObject k R h (n + 1)) := by
  let : Module.Finite k (twistedObject k R h (n + 1)) := finiteBase k R (n + 1)
  exact Module.Finite.of_restrictScalars_finite k (Enveloping k R) _

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleDetector
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q
local notation "S" => Resolution.Simple q

variable [CharP k 2]

theorem detector_boundary (hq1 : 1 + q ≠ 0)
    (g : ModuleBar.moduleObject k R S 3 →ₗ[R] ModuleBar.moduleObject k R S 0) :
    g (ModuleBar.differential k R S 3 (detector q)) = 0 := by
  let gk : ModuleBar.object k R S 3 →ₗ[k] S := g.restrictScalars k
  have hJ : T.vector q (true, .j) • simpleGenerator q = 0 := by
    rw [vector_smul_simple q hq1]
    simp
  change gk (ModuleBar.boundary k R S 3 (detector q)) = 0
  simp only [detector, map_add, map_smul]
  simp only [ModuleBar.boundary_succ_tmul k R S 2, ModuleBar.boundary_succ_tmul k R S 1,
    ModuleBar.boundary_succ_tmul k R S 0, ModuleBar.boundary_zero_tmul k R S,
    ModuleBar.left_tmul k R S 2, ModuleBar.left_tmul k R S 1, ModuleBar.left_tmul k R S 0,
    one_mul, tx_product, ty_product, xJ_product, yJ_product,
    hJ, TensorProduct.tmul_zero, TensorProduct.tmul_add,
    TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_add, map_smul, add_zero]
  have ht (x : ModuleBar.object k R S 2) : gk (T.vector q (false, .t) ⊗ₜ[k] x) = 0 :=
    hom_tmul_t q hq1 g x
  rw [ht, ht]
  simp only [zero_add, smul_add]
  exact SparseParity.module_add_self_eq_zero (k := k) _

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleExt
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.cResolution_finite_terms _root_.OAI.ArExplicit.Resolution.complex_scalarTower _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.Resolution.tInducedCochain_kprojective _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.Resolution.homETower _root_.OAI.ArExplicit.Resolution.homFTower _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] [CharP k 2] (q : k)

theorem simpleExtClass_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    simpleExtClass q ≠ 0 :=
  ModuleBar.extClass3_ne_zero_of_detector k (T k q) (Resolution.Simple q)
    (p q) (p_isCocycle3 q) (detector q) (detector_evaluation_ne_zero q hq hq1)
    (detector_boundary q hq1)

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def skeletonD (n : ℕ) : skeletonTerm D (n + 1) →ₗ[R] skeletonTerm D n :=
  coneBlock (D.d n) (middleD D n) (attachingRow D n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullCochainTail
attribute [-instance] _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)

theorem tailTerm_d (i j : ℕ) (h : j+1=i) :
    (nonnegativeTail (chainOfCochain K)).d i j =
      (tailTermIso K i).hom ≫ K.d (-(i : ℤ)) (-(j : ℤ)) ≫ (tailTermIso K j).inv := by
  subst i
  rw [nonnegativeTail_d]
  exact K.extend_d_eq negIndexEmbedding
    (show negIndexEmbedding.f (-((j+1 : ℕ) : ℤ))=((j+1 : ℕ) : ℤ) by
      change -(-((j+1 : ℕ) : ℤ))=((j+1 : ℕ) : ℤ); omega)
    (show negIndexEmbedding.f (-(j : ℤ))=(j : ℤ) by change -(-(j : ℤ))=(j : ℤ); omega)

def cochainTailMap (r : ℕ) (x : Cochain K L (r : ℤ)) (n : ℕ) :
    (nonnegativeTail (chainOfCochain K)).X (r+n) ⟶
      (nonnegativeTail (chainOfCochain L)).X n :=
  (tailTermIso K (r+n)).hom ≫ x.v (-((r+n : ℕ) : ℤ)) (-(n : ℤ)) (by omega) ≫
    (tailTermIso L n).inv

include k in
theorem cochainTailMap_comm (r : ℕ) (x : Cocycle K L (r : ℤ)) (n : ℕ) :
    cochainTailMap K L r x.val (n+1) ≫ (nonnegativeTail (chainOfCochain L)).d (n+1) n =
      (nonnegativeTail (chainOfCochain K)).d (r+(n+1)) (r+n) ≫ cochainTailMap K L r x.val n := by
  let i : ℤ := -((r+(n+1) : ℕ) : ℤ)
  let j : ℤ := -(n : ℤ)
  have hx := congrArg (fun z : Cochain K L ((r : ℤ)+1) => z.v i j (by dsimp [i,j]; omega))
    (show δ (r : ℤ) ((r : ℤ)+1) x.val=0 by simp)
  rw [δ_v _ _ rfl _ _ _ (by dsimp [i,j]; omega)
    (-((n+1 : ℕ) : ℤ)) (-((r+n : ℕ) : ℤ)) (by dsimp [i,j]; omega) (by dsimp [i,j]; omega),
    ResolutionProducts.intUnit_smul_charTwo (k := k), Cochain.zero_v] at hx
  let a := x.val.v i (-((n+1 : ℕ) : ℤ)) (by dsimp [i]; omega) ≫
    L.d (-((n+1 : ℕ) : ℤ)) j
  let b := K.d i (-((r+n : ℕ) : ℤ)) ≫
    x.val.v (-((r+n : ℕ) : ℤ)) j (by dsimp [j]; omega)
  have hab : a=b := by
    have hb : b+b=0 := by
      rw [← two_smul k b, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
    exact (eq_neg_of_add_eq_zero_left hx).trans (eq_neg_iff_add_eq_zero.mpr hb).symm
  rw [tailTerm_d L _ _ rfl, tailTerm_d K _ _ (by omega)]
  simp only [cochainTailMap, Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun z => (tailTermIso K (r+(n+1))).hom ≫ z ≫ (tailTermIso L n).inv) hab

variable (hK : TotallyAcyclicComplex (chainOfCochain K))
variable (hL : ExactProjectiveComplex (chainOfCochain L))

def restrictedCocycle (r : ℕ) (x : Cocycle K L (r : ℤ)) :
    Cocycle (completeExtResolution hK).cochainComplex
      (completeCokernelResolution (chainOfCochain L) hL.projective hL.exactAt).cochainComplex (r : ℤ) :=
  ResolutionProducts.natComparisonCocycle (k := k) (completeExtResolution hK)
    (completeCokernelResolution (chainOfCochain L) hL.projective hL.exactAt) r
    (cochainTailMap K L r x.val) (cochainTailMap_comm (k := k) K L r x)

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullCochainProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

theorem tailPrefix_congr {r : ℤ} (x : Cochain K K r) (p q : ℤ)
    (a b : ℕ) (hab : a=b) (ha : -(a : ℤ)=p) (hb : -(b : ℤ)=p)
    (hxa : -(a : ℤ)+r=q) (hxb : -(b : ℤ)+r=q) :
    ((completeExtResolution hK).cochainComplexXIso p a ha).hom ≫
      (tailTermIso K a).hom ≫ x.v (-(a : ℤ)) q hxa =
    ((completeExtResolution hK).cochainComplexXIso p b hb).hom ≫
      (tailTermIso K b).hom ≫ x.v (-(b : ℤ)) q hxb := by
  subst b
  rfl

theorem restrictedCocycle_product {r s : ℕ}
    (x : Cocycle K K (r : ℤ)) (y : Cocycle K K (s : ℤ)) :
    restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex (r+s)
      (ResolutionProducts.natCocycleProduct x y) =
      ResolutionProducts.natCocycleProduct
        (restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex r x)
        (restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex s y) := by
  change ↥(cocycle K K (r : ℤ)) at x
  change ↥(cocycle K K (s : ℤ)) at y
  apply Subtype.ext
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hq
    change (ResolutionProducts.natComparisonCochain _ _ (r+s) _).v _ _ _ = _
    erw [ResolutionProducts.natComparisonCochain_v_of_eq]
    erw [Cochain.comp_v _ _ _ _ (-((s+n : ℕ) : ℤ)) _ (by omega) (by omega)]
    change _ =
      (ResolutionProducts.natComparisonCochain _ _ r _).v _ _ _ ≫
        (ResolutionProducts.natComparisonCochain _ _ s _).v _ _ _
    erw [ResolutionProducts.natComparisonCochain_v_of_eq,
      ResolutionProducts.natComparisonCochain_v_of_eq]
    simp only [cochainTailMap, ResolutionProducts.natCocycleProduct,
      Cocycle.mk]
    try simp only [Nat.add_assoc]
    erw [Cochain.comp_v _ _ _ _ (-((s+n : ℕ) : ℤ)) _ (by omega) (by omega)]
    all_goals try omega
    let P := completeExtResolution hK
    let a := P.cochainComplexXIso p (r+(s+n)) (by omega)
    let b : P.complex.X (r+(s+n)) ≅ K.X (-((r+(s+n) : ℕ) : ℤ)) := tailTermIso K (r+(s+n))
    let c : P.complex.X (s+n) ≅ K.X (-((s+n : ℕ) : ℤ)) := tailTermIso K (s+n)
    let d := P.cochainComplexXIso (-((s+n : ℕ) : ℤ)) (s+n) rfl
    let e : P.complex.X n ≅ K.X (-(n : ℤ)) := tailTermIso K n
    let f := P.cochainComplexXIso (-(n : ℤ)) n rfl
    let xv := x.val.v (-((r+(s+n) : ℕ) : ℤ)) (-((s+n : ℕ) : ℤ)) (by omega)
    let yv := y.val.v (-((s+n : ℕ) : ℤ)) (-(n : ℤ)) (by omega)
    have hh : a.hom ≫ (b.hom ≫ xv ≫ yv ≫ e.inv) ≫ f.inv =
        a.hom ≫ ((b.hom ≫ xv ≫ c.inv) ≫ d.inv) ≫ d.hom ≫
          (c.hom ≫ yv ≫ e.inv) ≫ f.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [a, b, c, d, e, f, xv, yv, P]
    have he := tailPrefix_congr K hK x.val p (-((s+n : ℕ) : ℤ))
      (r+s+n) (r+(s+n)) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hh' := congrArg (fun z => (z ≫ yv ≫ e.inv) ≫ f.inv) he
    exact hh'

  · exact ((completeExtResolution hK).cochainComplex.isZero_of_isStrictlyLE 0 q
      (by omega)).eq_of_tgt _ _

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

theorem homShort_incoming_succ (n : ℕ) :
    (homShort k R (Y := Y) P (n+1)).f =
      ModuleCat.ofHom (LinearMap.lcomp k Y (P.complex.d (n+1) n).hom) := by
  exact homCochain_d k R P.complex Y n

theorem homShort_incoming_zero : (homShort k R (Y := Y) P 0).f = 0 := by
  exact (homCochain k R P.complex Y).shape 0 0 (by simp)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainExtClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

def homCochainQuotientEquiv (n : ℕ) :
    (homCochain k R P.complex Y).homology n ≃ₗ[k]
      (LinearMap.ker (homShort k R (Y := Y) P n).g.hom ⧸
        LinearMap.range (homShort k R (Y := Y) P n).moduleCatToCycles) :=
  ((homCochain k R P.complex Y).homologyIsoSc' (n-1) n (n+1)
    (by cases n <;> simp) (by simp)).toLinearEquiv.trans
      (homShort k R (Y := Y) P n).moduleCatHomologyIso.toLinearEquiv

def homCochainCycleClass (n : ℕ)
    (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    (homCochain k R P.complex Y).homology n :=
  (homCochainQuotientEquiv k R P n).symm (Submodule.Quotient.mk f)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_PositiveFullHomProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))

def restrictedEndExt (r : ℕ) (x : Cocycle K K (r : ℤ)) :
    Ext (ModuleCat.of R (Cokernel (chainOfCochain K) 0))
      (ModuleCat.of R (Cokernel (chainOfCochain K) 0)) r :=
  ResolutionProducts.endExt (completeExtResolution hK)
    (restrictedCocycle (k := k) K K hK hK.toExactProjectiveComplex r x)

theorem restrictedEndExt_product {r s : ℕ}
    (x : Cocycle K K (r : ℤ)) (y : Cocycle K K (s : ℤ)) :
    (restrictedEndExt (k := k) K hK r x).comp (restrictedEndExt (k := k) K hK s y) rfl =
      restrictedEndExt (k := k) K hK (r+s) (ResolutionProducts.natCocycleProduct x y) := by
  unfold restrictedEndExt
  rw [ResolutionProducts.endExt_product, restrictedCocycle_product]

end ArExplicit.CompleteComparison

end

end OAI
end


