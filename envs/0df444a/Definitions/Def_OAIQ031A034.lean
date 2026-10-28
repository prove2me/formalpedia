-- Prove2me | Definitions.Def_OAIQ031A034
-- name    : OAIQ031A034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:59:27.819366+00:00
-- url     : https://prove2.me/theorems/65924791-07cc-4700-b57e-89e34b002efc
-- title:
--   Definitions bundle OAIQ031A034 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 8 definitions, 1 instance and 12 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.diagonalFirst`, `OAI.ArExplicit.ExternalTensor.diagonalSecond`, `OAI.ArExplicit.ExternalTensor.extCoefficients`, `OAI.ArExplicit.FrobeniusTrace.dualFromRegular`, `OAI.ArExplicit.ResolutionProducts.natComparisonCocycle`, `OAI.ArExplicit.VectorCochain.tensorSplitting`, `OAI.ArExplicit.VectorCochain.totalZeroHomologyIso`, `OAI.ArExplicit.supportedPiEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_TensorRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorRadical.lean), [`AuslanderReiten_Duality_SymmetricStableDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/SymmetricStableDuality.lean), [`AuslanderReiten_Ext_ExtIsoCongr`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtIsoCongr.lean), [`AuslanderReiten_Ext_TTensorActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorActions.lean), [`AuslanderReiten_Ext_TensorExtCoefficients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TensorExtCoefficients.lean), [`AuslanderReiten_Homology_VectorCochainKunneth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunneth.lean), [`AuslanderReiten_Modules_SupportedPi`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/SupportedPi.lean), [`AuslanderReiten_Resolutions_NatResolutionCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/NatResolutionCochain.lean), [`AuslanderReiten_Resolutions_ResolutionExtIdentity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtIdentity.lean), [`AuslanderReiten_Resolutions_ResolutionProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionProducts.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A003`, `OAIQ031A004`, `OAIQ031A005`, `OAIQ031A006`, `OAIQ031A007`, `OAIQ031A008`, `OAIQ031A009` and `OAIQ031A011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A050`, `OAIQ031A051` and `OAIQ031A052`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A004
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A006
import Definitions.Def_OAIQ031A007
import Definitions.Def_OAIQ031A008
import Definitions.Def_OAIQ031A009
import Definitions.Def_OAIQ031A011

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

theorem mem_leftTensorIdeal_iff (I : Ideal R) (x : R ⊗[k] S) :
    x ∈ leftTensorIdeal (S := S) I ↔
      ∃ z : (I.restrictScalars k) ⊗[k] S,
        LinearMap.rTensor S (I.restrictScalars k).subtype z = x := by
  change x ∈ (leftTensorIdeal I).restrictScalars k ↔ _
  rw [leftTensorIdeal, Ideal.map_includeLeft_eq]
  rfl

theorem tmul_mem_leftTensorIdeal (I : Ideal R) {r : R} (hr : r ∈ I) (s : S) :
    r ⊗ₜ[k] s ∈ leftTensorIdeal (S := S) I := by
  apply (mem_leftTensorIdeal_iff I _).mpr
  exact ⟨⟨r, hr⟩ ⊗ₜ[k] s, rfl⟩

theorem leftTensorIdeal_mul_le (I J : Ideal R) :
    leftTensorIdeal (k := k) (S := S) I * leftTensorIdeal J ≤ leftTensorIdeal (I * J) := by
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨x, rfl⟩ := (mem_leftTensorIdeal_iff I x).mp hx
  obtain ⟨y, rfl⟩ := (mem_leftTensorIdeal_iff J y).mp hy
  clear hx hy
  induction x with
  | zero => simp
  | add x x' hx hx' => simpa only [map_add, add_mul] using
      (leftTensorIdeal (I * J)).add_mem hx hx'
  | tmul x s =>
      induction y with
      | zero => simp
      | add y y' hy hy' => simpa only [map_add, mul_add] using
          (leftTensorIdeal (I * J)).add_mem hy hy'
      | tmul y s' =>
          simpa only [LinearMap.rTensor_tmul, Submodule.coe_subtype,
            Algebra.TensorProduct.tmul_mul_tmul] using
            tmul_mem_leftTensorIdeal (I * J) (Ideal.mul_mem_mul x.property y.property) (s * s')

theorem leftTensorIdeal_pow_le (I : Ideal R) (n : ℕ) :
    (leftTensorIdeal (k := k) (S := S) I) ^ n ≤ leftTensorIdeal (I ^ n) := by
  induction n with
  | zero =>
      simp only [Submodule.pow_zero, Ideal.one_eq_top, leftTensorIdeal, Ideal.map_top]
      exact le_rfl
  | succ n hn =>
      rw [Submodule.pow_succ, Submodule.pow_succ]
      exact (Ideal.mul_mono_left hn).trans (leftTensorIdeal_mul_le (I ^ n) I)

theorem leftTensorIdeal_isNilpotent (I : Ideal R) (hI : IsNilpotent I) :
    IsNilpotent (leftTensorIdeal (k := k) (S := S) I) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  apply le_antisymm _ bot_le
  have h := leftTensorIdeal_pow_le (k := k) (S := S) I n
  simpa only [hn, Ideal.zero_eq_bot, leftTensorIdeal, Ideal.map_bot] using h

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_SymmetricStableDuality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.FrobeniusTrace

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N : Type u} [AddCommGroup M] [Module R M] [Module k M]
variable [IsScalarTower k R M] [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N]

def dualFromRegular (f : M →ₗ[R] R) : Module.Dual k M :=
  τ.trace.comp (f.restrictScalars k)

end ArExplicit.FrobeniusTrace

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtIsoCongr
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable {X X' Y Y' : C}

theorem selfExtIso_comp (e : X ≅ Y) {i j n : ℕ}
    (x : Ext X X i) (y : Ext X X j) (h : i+j=n) :
    selfExtIso (k := k) e n (x.comp y h) =
      (selfExtIso (k := k) e i x).comp (selfExtIso (k := k) e j y) h := by
  simp only [selfExtIso_apply]
  rw [Ext.comp_assoc_of_second_deg_zero]
  rw [← Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ e.hom)
    ((Ext.mk₀ e.inv).comp y (zero_add j)) (Ext.mk₀ e.hom) (zero_add j)]
  rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  rw [← Ext.comp_assoc_of_third_deg_zero]
  rw [Ext.comp_assoc (Ext.mk₀ e.inv) x y (zero_add i) h (by omega)]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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

theorem conjugate_comp {X Y : DerivedCategory C} (e : X ≅ Y) {n m : ℤ}
    (f : ShiftedHom X X n) (g : ShiftedHom X X m) :
    conjugate e (f.comp g (add_comm m n)) =
      (conjugate e f).comp (conjugate e g) (add_comm m n) := by
  simp only [conjugate, ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((CategoryTheory.shiftFunctor (DerivedCategory C) n).map e.hom),
    ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun h => e.inv ≫ f ≫
    (CategoryTheory.shiftFunctor (DerivedCategory C) n).map g ≫ h)
      ((CategoryTheory.shiftFunctorAdd' (DerivedCategory C) m n (n+m) (add_comm m n)).inv.naturality e.hom).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtIdentity
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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
variable {C : Type u} [Category.{v} C] [Abelian C]

theorem cocycleHom_ofHom {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom f) = ShiftedHom.mk₀ 0 rfl f := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [CompleteComparison.cocycleHom_component, Cocycle.ofHom_coe]
  simp only [ShiftedHom.mk₀, HomologicalComplex.comp_f, CategoryTheory.shiftFunctorZero',
    eqToIso_refl, Iso.trans_inv, Iso.refl_inv,
    CochainComplex.shiftFunctorZero_inv_app_f, Category.comp_id]
  change (Cochain.ofHom f).v i (i+0) rfl =
    f.f i ≫ (L.XIsoOfEq (show i=i+0 by omega)).hom
  simpa only [Cochain.ofHom_v] using
    (Cochain.v_comp_XIsoOfEq_hom (Cochain.ofHom f) i i (i+0) (add_zero i) (by omega)).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunneth
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.VectorCochain

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

instance hasMapBifunctor (P Q : CochainComplex (ModuleCat.{u} k) ℕ) :
    HasMapBifunctor P Q F (ComplexShape.up ℕ) := fun _ => inferInstance

theorem total_zero_differential (X Y : ℕ → ModuleCat.{u} k) (n m : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ)).d n m = 0 := by
  rw [mapBifunctor.d_eq]
  have h₁ : mapBifunctor.D₁ (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ) n m = 0 := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [comp_zero, mapBifunctor.ι_D₁]
    rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl)]
    simp [zeroDifferential]
  have h₂ : mapBifunctor.D₂ (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ) n m = 0 := by
    apply mapBifunctor.hom_ext
    intro i j h
    rw [comp_zero, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₂_eq' _ _ _ _ i (show (ComplexShape.up ℕ).Rel j (j+1) from rfl)]
    simp [zeroDifferential]
  rw [h₁, h₂, add_zero]

def totalZeroHomologyIso (X Y : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ)).homology n ≅
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F
      (ComplexShape.up ℕ)).X n :=
  let K := mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (ComplexShape.up ℕ)
  (K.isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl
    (total_zero_differential k F X Y _ _)).symm ≪≫
  K.iCyclesIso n ((ComplexShape.up ℕ).next n) rfl (total_zero_differential k F X Y _ _)

variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

def tensorSplitting :
    HomotopyEquiv
      (mapBifunctor (gradedHomology k P) (gradedHomology k Q) F (ComplexShape.up ℕ))
      (mapBifunctor P Q F (ComplexShape.up ℕ)) :=
  totalHomotopyEquiv F (splitting k P) (splitting k Q)

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TensorExtCoefficients
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
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

abbrev extCoefficients (n : ℕ) :=
  ∀ d : Diagonal n, Ext X U d.val.1 ⊗[k] Ext Y V d.val.2

abbrev diagonalFirst (n : ℕ) (d : Diagonal n) : Diagonal (n+3) :=
  ⟨(d.val.1+3,d.val.2), by have := d.property; omega⟩

abbrev diagonalSecond (n : ℕ) (d : Diagonal n) : Diagonal (n+3) :=
  ⟨(d.val.1,d.val.2+3), by have := d.property; omega⟩

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_SupportedPi
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w z
variable {k : Type u} [Field k] {ι : Type v} {κ : Type w}
variable (M : κ → Type z) [∀ j, AddCommGroup (M j)] [∀ j, Module k (M j)]
variable (f : ι → κ)

theorem supportedRestriction_bijective (hf : Function.Injective f)
    (hz : ∀ j, (¬ ∃ i, f i = j) → ∀ x : M j, x = 0) :
    Function.Bijective (supportedRestriction (k := k) M f) := by
  constructor
  · intro x y hxy
    funext j
    by_cases hj : ∃ i, f i = j
    · obtain ⟨i, rfl⟩ := hj
      exact congrFun hxy i
    · exact (hz j hj (x j)).trans (hz j hj (y j)).symm
  · intro y
    classical
    let x : ∀ j, M j := fun j => if hj : ∃ i, f i = j then
      hj.choose_spec ▸ y hj.choose else 0
    refine ⟨x, ?_⟩
    funext i
    change x (f i) = y i
    have hi : ∃ a, f a = f i := ⟨i, rfl⟩
    simp only [x, dite_eq_left hi]
    have hs (a : ι) (ha : f a = f i) : ha ▸ y a = y i := by
      have hai : a = i := hf ha
      subst a
      rfl
    exact hs _ _

def supportedPiEquiv (hf : Function.Injective f)
    (hz : ∀ j, (¬ ∃ i, f i = j) → ∀ x : M j, x = 0) :
    (∀ j, M j) ≃ₗ[k] (∀ i, M (f i)) :=
  LinearEquiv.ofBijective (supportedRestriction M f)
    (supportedRestriction_bijective M f hf hz)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorActions
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
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

theorem diagonalFirst_injective (n : ℕ) : Function.Injective (diagonalFirst n) := by
  intro d e h
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrArg (fun x : Diagonal (n+3) => x.val.1) h
    dsimp at hh
    omega
  · exact congrArg (fun x : Diagonal (n+3) => x.val.2) h

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_NatResolutionCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable (r : ℕ) (f : ∀ n : ℕ, P.complex.X (r+n) ⟶ Q.complex.X n)

variable [CharP k 2]
variable (hf : ∀ n, f (n+1) ≫ Q.complex.d (n+1) n =
  P.complex.d (r+(n+1)) (r+n) ≫ f n)
include hf k

theorem natComparisonCochain_closed :
    δ (r : ℤ) ((r : ℤ)+1) (natComparisonCochain P Q r f) = 0 := by
  apply Cochain.ext
  intro p q hpq
  by_cases hq : q ≤ 0
  · obtain ⟨m,rfl⟩ := Int.exists_eq_neg_ofNat hq
    have hp : p = -((r+(m+1) : ℕ) : ℤ) := by omega
    subst p
    rw [δ_v _ _ rfl _ _ _ hpq (-((m+1 : ℕ) : ℤ)) (-((r+m : ℕ) : ℤ))
      (by omega) (by omega)]
    rw [natComparisonCochain_v P Q r f (m+1), natComparisonCochain_v P Q r f m]
    rw [Q.cochainComplex_d _ _ (m+1) m rfl rfl,
      P.cochainComplex_d _ _ (r+(m+1)) (r+m) rfl rfl]
    rw [intUnit_smul_charTwo (k := k)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Cochain.zero_v]
    rw [← Category.assoc (f (m+1)), hf m]
    let z := (P.cochainComplexXIso (-((r+(m+1) : ℕ) : ℤ)) (r+(m+1)) rfl).hom ≫
      P.complex.d (r+(m+1)) (r+m) ≫ f m ≫
        (Q.cochainComplexXIso (-(m : ℤ)) m rfl).inv
    change z+z=0
    rw [← two_smul k z, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
  · exact (Q.cochainComplex.isZero_of_isStrictlyLE 0 q (by omega)).eq_of_tgt _ _

def natComparisonCocycle : Cocycle P.cochainComplex Q.cochainComplex (r : ℤ) :=
  Cocycle.mk (natComparisonCochain P Q r f) _ rfl
    (natComparisonCochain_closed (k := k) P Q r f hf)

end ArExplicit.ResolutionProducts

end

end OAI
end


