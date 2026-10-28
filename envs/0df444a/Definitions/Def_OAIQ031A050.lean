-- Prove2me | Definitions.Def_OAIQ031A050
-- name    : OAIQ031A050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:05:18.384762+00:00
-- url     : https://prove2.me/theorems/c56092d6-ada4-40be-a4fd-978e6690effe
-- title:
--   Definitions bundle OAIQ031A050 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 5 definitions, 17 instances and 16 theorems. The definitions and types are `OAI.ArExplicit.Induction.extendFormula`, `OAI.ArExplicit.InductionBimodule.leftEquiv`, `OAI.ArExplicit.InductionBimodule.scalarEquiv`, `OAI.ArExplicit.TateKoszul.negativeAt`, `OAI.ArExplicit.TrivialInduction.inflate`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_SimpleDual`, `AuslanderReiten_Cocycles_SparseCocycle`, `AuslanderReiten_Complete_TateKoszul`, `AuslanderReiten_Ext_NatComparisonExt`, `AuslanderReiten_Ext_TTensorActions`, `AuslanderReiten_HomComplex_FullHomProductLinear`, `AuslanderReiten_Modules_CoinducedBimodule`, `AuslanderReiten_Modules_InductionAdjunction`, `AuslanderReiten_Modules_InductionBimodule`, `AuslanderReiten_Modules_TrivialInduction`, `AuslanderReiten_Resolutions_CProjectiveResolution`, `AuslanderReiten_Resolutions_Resolution`, `AuslanderReiten_Resolutions_ResolutionProductCompatibility`, `AuslanderReiten_Resolutions_TrivialInductionQuotient`, `AuslanderReiten_Tensor_BalancedTensorMap`.
--
--   **Imports.** It imports the bundles `OAIQ031A026`, `OAIQ031A030`, `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A034` and `OAIQ031A035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A066`, `OAIQ031A067`, `OAIQ031A068`, `OAIQ031A070`, `OAIQ031A071` and `OAIQ031A074`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A026
import Definitions.Def_OAIQ031A030
import Definitions.Def_OAIQ031A032
import Definitions.Def_OAIQ031A033
import Definitions.Def_OAIQ031A034
import Definitions.Def_OAIQ031A035

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_Resolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem projective_fixedRight (p : C) (hp : p * p = p) :
    Module.Projective C (fixedRight q p) := by
  apply Module.Projective.of_split (fixedRight q p).subtype (projection q p hp)
  apply LinearMap.ext
  intro a
  exact Subtype.ext a.property

instance instProjectiveBaseAlgebraSubtypeMemSubmoduleE : Module.Projective C (E q) :=
  projective_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q e e)
instance instProjectiveBaseAlgebraSubtypeMemSubmoduleF : Module.Projective C (F q) :=
  projective_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q f f)

end ArExplicit.Resolution

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CProjectiveResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

variable {k : Type*} [Field k] [CharP k 2] (q : k)

instance complex_projective (n : ℕ) : CategoryTheory.Projective ((complex q).X n) := by
  cases n <;> dsimp [complex, objects] <;> infer_instance

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_CoinducedBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Coinduced
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

instance instIsScalarTowerMulOpposite : IsScalarTower k Rᵐᵒᵖ (Coinduced k R) where
  smul_assoc a r x := by ext s; simp

end ArExplicit.Coinduced

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open ArExplicit.Letter ArExplicit.BaseAlgebra
variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

instance simpleRightModule : Module Cᵐᵒᵖ (Simple q) where
  one_smul s := by
    change (1 : k) • s = s
    exact one_smul k s
  mul_smul c d s := by
    change (d.unop * c.unop).coeff f • s = c.unop.coeff f • d.unop.coeff f • s
    rw [← mul_smul, mul_comm]
    rfl
  smul_zero c := by
    change c.unop.coeff f • (0 : Simple q) = 0
    exact smul_zero _
  smul_add c s t := by
    change c.unop.coeff f • (s + t) = c.unop.coeff f • s + c.unop.coeff f • t
    exact smul_add _ _ _
  zero_smul s := by
    change (0 : k) • s = 0
    exact zero_smul k s
  add_smul c d s := by
    change (c.unop.coeff f + d.unop.coeff f) • s = _
    exact add_smul _ _ _

instance instIsScalarTowerMulOppositeBaseAlgebraSimple : IsScalarTower k Cᵐᵒᵖ (Simple q) where
  smul_assoc a c s := mul_smul a (c.unop.coeff f) s

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseCocycle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

theorem basis_evaluation (a b c : TIndex) :
    p q (T.vector q a) (T.vector q b) (T.vector q c) =
      ((cochain.filter fun t => decide (t.first = a ∧ t.second = b ∧ t.third = c)).map
        fun t => q ^ t.degree • T.vector q t.output).sum := by
  rw [p_apply]
  generalize cochain = l
  induction l with
  | nil => rfl
  | cons t l ih =>
    by_cases h1 : t.first = a <;> by_cases h2 : t.second = b <;> by_cases h3 : t.third = c <;>
      simp [evalTriple, h1, h2, h3, ih]

theorem p_txJ : p q (T.vector q (false, .t)) (T.vector q (false, .x))
    (T.vector q (true, .j)) = 0 := by
  rw [basis_evaluation]
  have h : (cochain.filter fun p => decide (p.first = (false, .t) ∧
      p.second = (false, .x) ∧ p.third = (true, .j))) = [] := by decide +kernel
  rw [h]
  rfl

theorem p_tyJ : p q (T.vector q (false, .t)) (T.vector q (false, .y))
    (T.vector q (true, .j)) = q ^ 3 • T.vector q (false, .f) := by
  rw [basis_evaluation]
  have h : (cochain.filter fun p => decide (p.first = (false, .t) ∧
      p.second = (false, .y) ∧ p.third = (true, .j))) =
        [⟨(false, .t), (false, .y), (true, .j), (false, .f), 3⟩] := by decide +kernel
  rw [h]
  simp

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TateKoszul

universe u
variable {k : Type u} [Field k]
variable (H : ℤ → Type u) [∀ a, AddCommGroup (H a)] [∀ a, Module k (H a)]

variable {H}

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)} (M : Model x y)

def negativeAt (a : ℤ) (n : ℕ) (ha : a = -1 - 3 * (n : ℤ)) :
    H a ≃ₗ[k] BinaryKoszul.DualPiece k n :=
  (degreeEquiv H ha).trans (M.negative n)

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionProductCompatibility
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem conjugate_comp_of_eq {X Y : DerivedCategory C} (e : X ≅ Y)
    {n m r : ℤ} (f : ShiftedHom X X n) (g : ShiftedHom X X m) (h : m+n=r) :
    conjugate e (f.comp g h) = (conjugate e f).comp (conjugate e g) h := by
  obtain rfl : r=n+m := by omega
  exact conjugate_comp e f g

variable [HasExt.{v} C]

theorem endExt_eq_augmented {X : C} (P : ProjectiveResolution X) {n : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ)) :
    endExt P x = P.extEquivCohomologyClass.symm
      (CohomologyClass.mk (x.postcomp P.π')) := by
  apply Ext.homEquiv.injective
  change (endExt P x).hom = (P.extEquivCohomologyClass.symm (CohomologyClass.mk (x.postcomp P.π'))).hom
  rw [endExt_hom, P.extEquivCohomologyClass_symm_mk_hom]
  rw [Cocycle.equivHomShift_symm_postcomp]
  rw [← ShiftedHom.comp_mk₀ _ 0 rfl, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [conjugate, resolutionIso, Iso.trans_inv, Iso.trans_hom,
    asIso_inv, asIso_hom, Functor.map_comp, Category.assoc]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_NatComparisonExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (r : ℕ) (f : ∀ n : ℕ, P.complex.X (r+n) ⟶ P.complex.X n)
variable (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n =
  P.complex.d (r+(n+1)) (r+n) ≫ f n)

include hf

include k in

theorem natComparison_endExt_eq :
    endExt P (natComparisonCocycle (k := k) P P r f hf) =
      P.extMk (natComparisonAugmentation P r f) (r+1) rfl (natComparison_augmented_cycle P r f hf) := by
  rw [endExt_eq_augmented]
  unfold ProjectiveResolution.extMk
  apply congrArg P.extEquivCohomologyClass.symm
  apply congrArg CohomologyClass.mk
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show -(r : ℤ)+(r : ℤ)=0 by omega)).injective
  change (((natComparisonCocycle (k := k) P P r f hf).val.comp (Cochain.ofHom P.π')
    (add_zero (r : ℤ))).v (-(r : ℤ)) 0 (by omega) ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom) =
    (Cochain.toSingleMk ((P.cochainComplexXIso (-(r : ℤ)) r rfl).hom ≫ natComparisonAugmentation P r f)
      (by omega : -(r : ℤ)+(r : ℤ)=0)).v (-(r : ℤ)) 0 (by omega) ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom
  rw [Cochain.toSingleMk_v]
  rw [Cochain.comp_v _ _ _ (-(r : ℤ)) 0 0 (by omega) (by omega)]
  change ((natComparisonCochain P P r f).v (-(r : ℤ)) 0 (by omega) ≫ P.π'.f 0) ≫ _ = _
  let s := HomologicalComplex.singleObjXSelf (.up ℤ) 0 X
  let eᵣ := P.cochainComplexXIso (-(r : ℤ)) r (by omega)
  let e₀ := P.cochainComplexXIso 0 0 rfl
  change ((natComparisonCochain P P r f).v (-(r : ℤ)) 0 (by omega) ≫ P.π'.f 0) ≫ s.hom =
    (((P.cochainComplexXIso (-(r : ℤ)) r rfl).hom ≫ natComparisonAugmentation P r f) ≫ s.inv) ≫ s.hom
  refine (congrArg (fun v => (v ≫ P.π'.f 0) ≫ s.hom)
    (natComparisonCochain_v P P r f 0)).trans ?_
  refine (congrArg (fun v => ((eᵣ.hom ≫ f 0 ≫ e₀.inv) ≫ v) ≫ s.hom)
    P.π'_f_zero).trans ?_
  simp only [e₀, eᵣ, s, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BalancedTensor

open TensorProduct

variable {k R F M N : Type*} [CommRing k] [Ring R]
variable [AddCommGroup F] [AddCommGroup M] [Module k F] [Module k M]
variable [Module Rᵐᵒᵖ F] [Module R M]

variable {F' M' : Type*} [AddCommGroup F'] [AddCommGroup M']
variable [Module k F'] [Module k M'] [Module Rᵐᵒᵖ F'] [Module R M']

theorem map_surjective (a : F →ₗ[k] F') (b : M →ₗ[k] M')
    (ha : ∀ (r : Rᵐᵒᵖ) f, a (r • f) = r • a f)
    (hb : ∀ (r : R) m, b (r • m) = r • b m)
    (asurj : Function.Surjective a) (bsurj : Function.Surjective b) :
    Function.Surjective (map a b ha hb) := by
  intro z
  induction z using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul f m =>
    obtain ⟨f, rfl⟩ := asurj f
    obtain ⟨m, rfl⟩ := bsurj m
    exact ⟨tmul f m, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ x y⟩

end ArExplicit.BalancedTensor

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

namespace InductionBimodule
variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (ι : R →ₐ[k] S)

instance instSMulCommClassMulOpposite : SMulCommClass S Rᵐᵒᵖ (InductionBimodule ι) where
  smul_comm s r x := by ext; exact (mul_assoc _ _ _).symm
instance instSMulCommClass : SMulCommClass k S (InductionBimodule ι) where
  smul_comm a s x := by ext; exact (mul_smul_comm a s x.value).symm
instance instIsScalarTowerMulOpposite : IsScalarTower k Rᵐᵒᵖ (InductionBimodule ι) where
  smul_assoc a r x := by
    ext
    change x.value * ι (a • r.unop) = a • (x.value * ι r.unop)
    rw [map_smul, mul_smul_comm]

def leftEquiv : InductionBimodule ι ≃ₗ[S] S := (coordinates ι).addEquiv.linearEquiv S
def scalarEquiv : InductionBimodule ι ≃ₗ[k] S := (coordinates ι).addEquiv.linearEquiv k

instance instFree : Module.Free S (InductionBimodule ι) := Module.Free.of_equiv (leftEquiv ι).symm
instance instProjective : Module.Projective S (InductionBimodule ι) := Module.Projective.of_free

end InductionBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionAdjunction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
namespace Induction

variable {k R S V W : Type*} [CommRing k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S] (ι : R →ₐ[k] S)
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [Module S W]
  [IsScalarTower k R W] [IsScalarTower k S W]

def extendFormula (g : V →ₗ[R] W) : InductionBimodule ι →ₗ[k] V →ₗ[k] W :=
  ((BalancedTensor.leftAction (k := k) (R := S) (M := W)).compl₂
    (g.restrictScalars k)).comp (InductionBimodule.scalarEquiv ι).toLinearMap

end Induction
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TrivialInduction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TrivialInduction

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

local notation "T" => TrivialExtension k R

instance instSMulCommClassTrivialExtensionCoinduced : SMulCommClass k T (Coinduced k R) where
  smul_comm a t φ := smul_comm a t.base φ
instance instSMulCommClassTrivialExtensionMulOppositeCoinduced : SMulCommClass T Rᵐᵒᵖ (Coinduced k R) where
  smul_comm t r φ := smul_comm t.base r φ

instance instSMulCommClassTrivialExtensionQuotient : SMulCommClass k T (Quotient (k := k) (R := R)) where
  smul_comm a t r := smul_comm a t.base r
instance instSMulCommClassTrivialExtensionMulOppositeQuotient : SMulCommClass T Rᵐᵒᵖ (Quotient (k := k) (R := R)) where
  smul_comm t r s := smul_comm t.base r s

theorem inclusion_left (t : T) (φ : Coinduced k R) :
    inclusion (t • φ) = t • inclusion φ := by
  apply InductionBimodule.ext
  apply TrivialExtension.ext
  · exact (mul_zero _).symm
  · ext x
    change φ.functional (x * t.base) = φ.functional (x * t.base) + t.dual (0 * x)
    rw [zero_mul, map_zero, add_zero]

theorem projection_left (t : T) (x : Middle (k := k) (R := R)) :
    projection (t • x) = t • projection x := rfl

theorem projection_inclusion :
    (projection (k := k) (R := R)).comp inclusion = 0 := rfl

theorem inclusion_injective : Function.Injective (inclusion (k := k) (R := R)) := by
  intro φ ψ h
  exact Coinduced.ext (congrArg (fun x : Middle (k := k) (R := R) => x.value.dual) h)

theorem projection_surjective : Function.Surjective (projection (k := k) (R := R)) := by
  intro r
  exact ⟨⟨TrivialExtension.inl r.value⟩, rfl⟩

theorem inclusion_projection_exact :
    Function.Exact (inclusion (k := k) (R := R)) projection := by
  intro t
  constructor
  · intro ht
    refine ⟨⟨t.value.dual⟩, ?_⟩
    apply InductionBimodule.ext
    apply TrivialExtension.ext
    · exact (congrArg InductionBimodule.value ht).symm
    · rfl
  · rintro ⟨φ, rfl⟩
    rfl

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionQuotient
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

def inflate : ModuleCat.{u} R ⥤ ModuleCat.{u} T :=
  ModuleCat.restrictScalars TrivialExtension.projection.toRingHom

instance instAdditiveModuleCatTrivialExtensionInflate : (inflate (k := k) (R := R)).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars (TrivialExtension.projection (k := k) (A := R)).toRingHom).Additive

instance instPreservesHomologyModuleCatTrivialExtensionInflate : (inflate (k := k) (R := R)).PreservesHomology :=
  ModuleRestriction.preservesHomology _

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorActions
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem diagonalSecond_injective (n : ℕ) : Function.Injective (diagonalSecond n) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : Diagonal (n+3) => x.val.1) h
  · have hh := congrArg (fun x : Diagonal (n+3) => x.val.2) h
    dsimp at hh
    omega

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProductLinear
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category* C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem fullHomProduct_smul_right (c : k) (x : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomProduct x (c • y) = c • fullHomProduct x y := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [← fullHom_mk_smul, fullHomProduct_mk, fullHomProduct_mk, ← fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.comp_smul x.val c y.val rfl

end ArExplicit.CompleteComparison

end OAI
end


