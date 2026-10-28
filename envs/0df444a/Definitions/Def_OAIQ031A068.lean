-- Prove2me | Definitions.Def_OAIQ031A068
-- name    : OAIQ031A068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:15:49.990881+00:00
-- url     : https://prove2.me/theorems/9267a846-d13d-4dc7-940e-3ae4e6318e48
-- title:
--   Definitions bundle OAIQ031A068 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 2 definitions and 16 theorems. The definitions and types are `OAI.ArExplicit.AEnvelopingFrobeniusTrace`, `OAI.ArExplicit.AOppositeFrobeniusTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_FrobeniusOpposite`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/FrobeniusOpposite.lean), [`AuslanderReiten_Algebras_TensorStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorStructure.lean), [`AuslanderReiten_Bar_BarProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarProjective.lean), [`AuslanderReiten_Ext_CubicExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/CubicExtAction.lean), [`AuslanderReiten_Ext_CubicExtCommute`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/CubicExtCommute.lean), [`AuslanderReiten_Ext_NatCubicExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/NatCubicExt.lean), [`AuslanderReiten_Ext_TTensorActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorActions.lean), [`AuslanderReiten_Resolutions_BinaryKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszul.lean), [`AuslanderReiten_Resolutions_ResolutionExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtAction.lean), [`AuslanderReiten_Tensor_BalancedTensorExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorExact.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A038`, `OAIQ031A045`, `OAIQ031A047`, `OAIQ031A049`, `OAIQ031A050`, `OAIQ031A051`, `OAIQ031A052` and `OAIQ031A055` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A083`, `OAIQ031A086`, `OAIQ031A088`, `OAIQ031A089` and `OAIQ031A108`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A038
import Definitions.Def_OAIQ031A045
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A050
import Definitions.Def_OAIQ031A051
import Definitions.Def_OAIQ031A052
import Definitions.Def_OAIQ031A055

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

theorem radicalU_mem : radicalU q ∈ Ring.jacobson (A k q) := by
  apply left_radical_mem
  rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
  exact ⟨by simp [T.lower, TrivialExtension.inl], by simp [T.lower, TrivialExtension.inl]⟩

theorem radicalT_mem : radicalT q ∈ Ring.jacobson (A k q) := by
  apply left_radical_mem
  rw [TrivialExtension.mem_jacobson_iff, BaseAlgebra.mem_jacobson_iff]
  exact ⟨by simp [T.lower, TrivialExtension.inl], by simp [T.lower, TrivialExtension.inl]⟩

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_FrobeniusOpposite
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

variable (k : Type*) [Field k] (q : k)

def AOppositeFrobeniusTrace : FrobeniusTrace k (A k q)ᵐᵒᵖ :=
  (AFrobeniusTrace k q).opposite (A_trace_symmetric k q)

open scoped TensorProduct

def AEnvelopingFrobeniusTrace : FrobeniusTrace k (A k q ⊗[k] (A k q)ᵐᵒᵖ) :=
  (AFrobeniusTrace k q).tensor (AOppositeFrobeniusTrace k q)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

theorem finiteBase [Module.Finite k R] (n : ℕ) : Module.Finite k (object k R n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let := ih
    change Module.Finite k (R ⊗[k] object k R n)
    infer_instance

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_NatCubicExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f : ∀ n : ℕ, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (n+4) (n+3) ≫ f n)
include hf

variable [HasDerivedCategory (ModuleCat.{u} R)]

include k in

theorem natCubic_endExt_eq :
    endExt P (natCubicCocycle (k := k) P f hf) =
      P.extMk (f 0 ≫ P.π.f 0) 4 rfl (natCubic_augmented_cycle P f hf) := by
  rw [endExt_eq_augmented]
  unfold ProjectiveResolution.extMk
  apply congrArg P.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show (-3 : ℤ)+3=0 by omega)).injective
  change (((natCubicCocycle (k := k) P f hf).val.comp (Cochain.ofHom P.π')
    (add_zero 3)).v (-3) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom) =
    (Cochain.toSingleMk ((P.cochainComplexXIso (-3) 3 rfl).hom ≫ f 0 ≫ P.π.f 0)
      (by omega : (-3 : ℤ)+3=0)).v (-3) 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
  rw [Cochain.toSingleMk_v]
  rw [Cochain.comp_v _ _ _ (-3) 0 0 (by omega) (by omega)]
  change ((natCubicCochain P f).v (-3) 0 (by omega) ≫ P.π'.f 0) ≫ _ = _
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  let e₃ := P.cochainComplexXIso (-3) 3 rfl
  let e₀ := P.cochainComplexXIso 0 0 rfl
  change ((natCubicCochain P f).v (-3) 0 (by omega) ≫ P.π'.f 0) ≫ s.hom =
    ((e₃.hom ≫ f 0 ≫ P.π.f 0) ≫ s.inv) ≫ s.hom
  refine (congrArg (fun v => (v ≫ P.π'.f 0) ≫ s.hom)
    (natCubicCochain_v P f 0)).trans ?_
  refine (congrArg (fun v => ((e₃.hom ≫ f 0 ≫ e₀.inv) ≫ v) ≫ s.hom)
    P.π'_f_zero).trans ?_
  simp only [e₀, e₃, s, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

variable [HasExt.{v} C]

theorem endExt_comp_extOfCocycle {X Y : C} (P : ProjectiveResolution X) {n m r : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ))
    (y : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (m : ℤ))
    (z : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (r : ℤ))
    (h : n+m=r) (hz : z.val=x.val.comp y.val (by omega)) :
    (endExt P x).comp (extOfCocycle P y) h = extOfCocycle P z := by
  apply Ext.homEquiv.injective
  change ((endExt P x).comp (extOfCocycle P y) h).hom = (extOfCocycle P z).hom
  rw [Ext.comp_hom, endExt_hom, extOfCocycle_hom, extOfCocycle_hom,
    cocycleHom_comp (by omega) x y z hz, ShiftedHom.map_comp]
  exact (conjugateTo_comp (resolutionIso P) (resolutionIso P)
    ((DerivedCategory.singleFunctorIsoCompQ C 0).symm.app Y) _ _ _).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_CubicExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
include hp

include k in

theorem cubic_endExt_comp_extMk {n : ℕ} (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n+1) n ≫ f=0) :
    (endExt P (natCubicCocycle (k := k) P p hp)).comp (P.extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
      P.extMk (p n ≫ f) (n+4) rfl (cubicPrecomp_closed P p hp f hf) := by
  exact endExt_comp_extOfCocycle P (n := 3) (m := n) (r := n+3) (natCubicCocycle (k := k) P p hp)
    (closedCochain P f hf)
    (closedCochain P (p n ≫ f) (cubicPrecomp_closed P p hp f hf)) (by omega)
    (cubicPrecomp_cochain (k := k) P p hp f hf)

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_CubicExtCommute
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (f g : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ f n)
variable (hg : ∀ n, g (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ g n)

theorem cubic_endExt_commute (hfg : f 3 ≫ g 0 = g 3 ≫ f 0) :
    (endExt P (natCubicCocycle (k := k) P f hf)).comp
      (endExt P (natCubicCocycle (k := k) P g hg)) rfl =
    (endExt P (natCubicCocycle (k := k) P g hg)).comp
      (endExt P (natCubicCocycle (k := k) P f hf)) rfl := by
  have h₁ := (congrArg (fun y =>
      (endExt P (natCubicCocycle (k := k) P f hf)).comp y (show 3+3=6 from rfl))
    (natCubic_endExt_eq (k := k) P g hg)).trans
      (cubic_endExt_comp_extMk (k := k) P f hf (g 0 ≫ P.π.f 0)
        (natCubic_augmented_cycle P g hg))
  have h₂ := (congrArg (fun y =>
      (endExt P (natCubicCocycle (k := k) P g hg)).comp y (show 3+3=6 from rfl))
    (natCubic_endExt_eq (k := k) P f hf)).trans
      (cubic_endExt_comp_extMk (k := k) P g hg (f 0 ≫ P.π.f 0)
        (natCubic_augmented_cycle P f hf))
  refine h₁.trans ((extMk_eq_of_map_eq P _ _ _ _ ?_).trans h₂.symm)
  change f 3 ≫ (g 0 ≫ P.π.f 0) = g 3 ≫ (f 0 ≫ P.π.f 0)
  rw [← Category.assoc, hfg, Category.assoc]

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [SMulCommClass k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L] [SMulCommClass k R L]
variable {n : ℕ}

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem freeRecombine_rightCoefficients
    (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F)
    (h : p.comp s = LinearMap.id) (z : BalancedTensor k R F M) :
    freeRecombine p (rightCoefficients s z) = z := by
  induction z using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f m =>
    rw [freeRecombine_apply]
    calc
      (∑ i, tmul (p (Pi.single i 1)) (rightCoefficients s (tmul f m) i)) =
          ∑ i, tmul (p (Pi.single i (s f i))) m := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [rightCoefficients_tmul, ← balance]
        congr 1
        rw [MulOpposite.op_unop, ← p.map_smul]
        congr 1
        ext j
        by_cases hij : j = i
        · subst j; simp
        · simp [hij]
      _ = tmul (p (∑ i, Pi.single i (s f i))) m := by
        simp only [map_sum]
        exact (map_sum ((mk (k := k) (R := R)).flip m) _ _).symm
      _ = tmul f m := by
        rw [Finset.univ_sum_single]
        exact congrArg (fun f => tmul (k := k) (R := R) f m) (DFunLike.congr_fun h f)

variable {S : Type*} [Ring S] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem rightCoefficients_natural (s : F →ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) (b : M →ₗ[R] N)
    (z : BalancedTensor k R F M) :
    rightCoefficients s (mapRight (S := S) b z) = fun i => b (rightCoefficients s z i) := by
  induction z using induction_on with
  | zero => ext i; simp
  | tmul f m => ext i; simp
  | add x y hx hy =>
    ext i
    simp only [map_add, Pi.add_apply, hx, hy]

omit [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
  [SMulCommClass k R M] [SMulCommClass k R N] in
theorem freeRecombine_natural (p : (Fin n → Rᵐᵒᵖ) →ₗ[Rᵐᵒᵖ] F) (b : M →ₗ[R] N)
    (z : Fin n → M) :
    mapRight (S := S) b (freeRecombine p z) = freeRecombine (k := k) p (fun i => b (z i)) := by
  simp only [freeRecombine_apply, map_sum, mapRight_tmul]

omit [SMulCommClass k Rᵐᵒᵖ F] [SMulCommClass k R M] in
theorem mapRight_exact [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
    (e : M →ₗ[R] N) (d : N →ₗ[R] L) (hex : Function.Exact e d) :
    Function.Exact (mapRight (k := k) (F := F) (S := S) e) (mapRight (S := S) d) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' Rᵐᵒᵖ F
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : F →ₗ[Rᵐᵒᵖ] F) hp
  intro z
  constructor
  · intro hz
    have hcoords : ∀ i, d (rightCoefficients s z i) = 0 := by
      have hnat := rightCoefficients_natural (S := S) s d z
      rw [hz, map_zero] at hnat
      intro i
      exact (congrFun hnat i).symm
    choose w hw using fun i => (hex (rightCoefficients s z i)).mp (hcoords i)
    refine ⟨freeRecombine p w, ?_⟩
    rw [freeRecombine_natural]
    convert freeRecombine_rightCoefficients s p hs z using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg (freeRecombine (k := k) p) (funext hw)
  · rintro ⟨w, rfl⟩
    have hde : d.comp e = 0 := by ext m; exact (hex (e m)).mpr ⟨m, rfl⟩
    change ((mapRight (S := S) d).comp (mapRight (S := S) e)) w = 0
    rw [← mapRight_comp, hde, mapRight_zero, LinearMap.zero_apply]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

theorem range_column_eq_ker_row (n : ℕ) :
    LinearMap.range (column k n) = LinearMap.ker (row k (n + 1)) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (row_column k n)
  · rintro ⟨u, v⟩ h
    exact kernel_row k n u v h

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorActions
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (X U : ModuleCat.{u} A) (Y V : ModuleCat.{u} B)

theorem coefficientFirst_apply (a : Ext X X 3) (n : ℕ) (d : Diagonal n)
    (z : extCoefficients k A B X U Y V n) :
    coefficientFirst k A B X U Y V a n z (diagonalFirst n d) =
      TensorProduct.map (Ext.bilinearCompOfLinear k X X U 3 d.val.1 (d.val.1+3) (by omega) a)
        LinearMap.id (z d) := by
  classical
  simp only [coefficientFirst, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  rw [Finset.sum_eq_single d]
  · exact Pi.single_eq_same _ _
  · intro e he hne
    apply Pi.single_eq_of_ne
    intro h
    exact hne ((diagonalFirst_injective n) h.symm)
  · simp

theorem coefficientSecond_apply (b : Ext Y Y 3) (n : ℕ) (d : Diagonal n)
    (z : extCoefficients k A B X U Y V n) :
    coefficientSecond k A B X U Y V b n z (diagonalSecond n d) =
      TensorProduct.map LinearMap.id
        (Ext.bilinearCompOfLinear k Y Y V 3 d.val.2 (d.val.2+3) (by omega) b) (z d) := by
  classical
  simp only [coefficientSecond, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  rw [Finset.sum_eq_single d]
  · exact Pi.single_eq_same _ _
  · intro e he hne
    apply Pi.single_eq_of_ne
    intro h
    exact hne ((diagonalSecond_injective n) h.symm)
  · simp

theorem coefficientFirst_zero (a : Ext X X 3) (n : ℕ) (d : Diagonal (n+3))
    (hd : d.val.1 < 3) (z : extCoefficients k A B X U Y V n) :
    coefficientFirst k A B X U Y V a n z d = 0 := by
  classical
  simp only [coefficientFirst, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  apply Finset.sum_eq_zero
  intro e he
  apply Pi.single_eq_of_ne
  intro h
  have hh := congrArg (fun x : Diagonal (n+3) => x.val.1) h
  dsimp at hh
  omega

theorem coefficientSecond_zero (b : Ext Y Y 3) (n : ℕ) (d : Diagonal (n+3))
    (hd : d.val.2 < 3) (z : extCoefficients k A B X U Y V n) :
    coefficientSecond k A B X U Y V b n z d = 0 := by
  classical
  simp only [coefficientSecond, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Finset.sum_apply, LinearMap.single_apply]
  apply Finset.sum_eq_zero
  intro e he
  apply Pi.single_eq_of_ne
  intro h
  have hh := congrArg (fun x : Diagonal (n+3) => x.val.2) h
  dsimp at hh
  omega

end ArExplicit.ExternalTensor

end

end OAI
end


