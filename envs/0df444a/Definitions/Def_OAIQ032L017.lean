-- Prove2me | Definitions.Def_OAIQ032L017
-- name    : OAIQ032L017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:56:07.71392+00:00
-- url     : https://prove2.me/theorems/4ddccb39-e638-4390-be29-40fb9d371155
-- title:
--   Definitions bundle OAIQ032L017 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 12 definitions, 2 instances and 13 theorems. The definitions and types are `OAI.Lech.TensorIdeal.quotientTensorEquiv`, `OAI.Lech.TensorIdeal.quotientUnitTensorEquiv`, `OAI.Lech.TensorPushout.equiv`, `OAI.Lech.TensorTotal.Right.degreeSequenceIso`, `OAI.Lech.TensorTwist.algebraExtendEquiv`, `OAI.Lech.TensorTwist.extendEquiv`, `OAI.Lech.TorsionLength.DirectSumZero`, `OAI.Lech.TorsionLength.finiteClass`, `OAI.Lech.TorsionLength.zeroClass`, `OAI.Lech.TotalGhost.Shifted`, `OAI.Lech.TotalGhost.correction`, `OAI.Lech.TotalGhost.imageRowLift`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_BicomplexImageLift`, `Multiplicity_FibreSquare`, `Multiplicity_FilteredCechAugmented`, `Multiplicity_FiniteComplexTopInclusion`, `Multiplicity_LechMapCochain`, `Multiplicity_TensorCoefficientFibre`, `Multiplicity_TensorPushout`, `Multiplicity_TensorReduction`, `Multiplicity_TensorRingTwist`, `Multiplicity_TorsionZeroStability`, `Multiplicity_TotalGhostRowHom`.
--
--   **Imports.** It imports the bundles `OAIQ032L000`, `OAIQ032L002`, `OAIQ032L003`, `OAIQ032L008` and `OAIQ032L009` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ032L023`; the statements `OAI.Lech.FiniteModuleCech.tensorEuler_copies`, `OAI.Lech.FiniteModuleCech.tensor_euler_rank_zero`, `OAI.Lech.ReesRoot.scalarEuler_value`, `OAI.Lech.ReesRoot.scalarHomology_value`, `OAI.Lech.ReesRoot.sum_estimate`, `OAI.Lech.SourceGraded.finiteThickening_homology_zeroClass` and `OAI.Lech.TensorIdeal.fibreMap_kernel_zero`; the proofs of `OAI.Lech.CharP.dutta_limit_from_perfection`, `OAI.Lech.PrimeFiltration.Factors.euler_self`, `OAI.Lech.SourceGraded.acyclicity_finite_torsion`, `OAI.Lech.SourceGraded.exists_uniform_geometric_stableImage`, `OAI.Lech.complex_estimate_allModule` and `OAI.Lech.short_rank_euler_zero`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L003
import Definitions.Def_OAIQ032L008
import Definitions.Def_OAIQ032L009

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section

section
universe u
variable {R : Type u} [CommRing R]


lemma powerTorsion_zero (I : Ideal R) {M : ModuleCat.{u} R} (hM : IsZero M) :
    powerTorsion I M := by
  have := ModuleCat.isZero_iff_subsingleton.mp hM
  exact ⟨0, by simp [Module.annihilator_eq_top_iff.mpr ‹Subsingleton M›]⟩

lemma powerTorsion_mono (I : Ideal R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Mono f] (hN : powerTorsion I N) : powerTorsion I M := by
  obtain ⟨n, hn⟩ := hN
  exact ⟨n, hn.trans (f.hom.annihilator_le_of_injective
    ((ModuleCat.mono_iff_injective f).mp inferInstance))⟩

lemma powerTorsion_epi (I : Ideal R) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Epi f] (hM : powerTorsion I M) : powerTorsion I N := by
  obtain ⟨n, hn⟩ := hM
  exact ⟨n, hn.trans (f.hom.annihilator_le_of_surjective
    ((ModuleCat.epi_iff_surjective f).mp inferInstance))⟩

lemma powerTorsion_extension (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.Exact) (h₁ : powerTorsion I S.X₁) (h₃ : powerTorsion I S.X₃) :
    powerTorsion I S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨a + b, ?_⟩
  rw [pow_add, Ideal.mul_le]
  intro r hr s hs
  rw [Module.mem_annihilator]
  intro x
  have hx : S.g (s • x) = 0 := by
    rw [map_smul]
    exact Module.mem_annihilator.mp (hb hs) _
  obtain ⟨y, hy⟩ := (S.moduleCat_exact_iff.mp hS) _ hx
  rw [mul_smul, ← hy, ← map_smul, Module.mem_annihilator.mp (ha hr) y, map_zero]

namespace TorsionLength
variable {I : Ideal R} (ℓ : TorsionLength I)

lemma le_of_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f]
    (hN : powerTorsion I N) : ℓ.value M ≤ ℓ.value N := by
  have hS : (ShortComplex.cokernelSequence f).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f
      mono_f := (inferInstance : Mono f) }
  have h := ℓ.additive hS hN
  exact h.symm ▸ le_add_right le_rfl

lemma le_of_epi {M N : ModuleCat.{u} R} (f : M ⟶ N) [Epi f]
    (hM : powerTorsion I M) : ℓ.value N ≤ ℓ.value M := by
  have hS : (ShortComplex.kernelSequence f).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      epi_g := (inferInstance : Epi f) }
  have h := ℓ.additive hS hM
  exact h.symm ▸ le_add_left le_rfl

def zeroClass : ObjectProperty (ModuleCat.{u} R) :=
  fun M => powerTorsion I M ∧ ℓ.value M = 0

def finiteClass : ObjectProperty (ModuleCat.{u} R) :=
  fun M => powerTorsion I M ∧ ℓ.value M ≠ ⊤

instance zeroClass_serre : ℓ.zeroClass.IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, powerTorsion_zero I (isZero_zero _),
    ℓ.zero (isZero_zero _)⟩
  prop_of_mono f _ h := ⟨powerTorsion_mono I f h.1,
    le_antisymm ((ℓ.le_of_mono f h.1).trans_eq h.2) bot_le⟩
  prop_of_epi f _ h := ⟨powerTorsion_epi I f h.1,
    le_antisymm ((ℓ.le_of_epi f h.1).trans_eq h.2) bot_le⟩
  prop_X₂_of_shortExact h h₁ h₃ := by
    have h₂ := powerTorsion_extension I h.exact h₁.1 h₃.1
    exact ⟨h₂, by rw [ℓ.additive h h₂, h₁.2, h₃.2, zero_add]⟩

instance finiteClass_serre : ℓ.finiteClass.IsSerreClass where
  exists_zero := ⟨0, isZero_zero _, powerTorsion_zero I (isZero_zero _),
    by rw [ℓ.zero (isZero_zero _)]; exact ENNReal.zero_ne_top⟩
  prop_of_mono f _ h := ⟨powerTorsion_mono I f h.1,
    ne_top_of_le_ne_top h.2 (ℓ.le_of_mono f h.1)⟩
  prop_of_epi f _ h := ⟨powerTorsion_epi I f h.1,
    ne_top_of_le_ne_top h.2 (ℓ.le_of_epi f h.1)⟩
  prop_X₂_of_shortExact h h₁ h₃ := by
    have h₂ := powerTorsion_extension I h.exact h₁.1 h₃.1
    exact ⟨h₂, by rw [ℓ.additive h h₂]; exact ENNReal.add_ne_top.mpr ⟨h₁.2, h₃.2⟩⟩

end TorsionLength
end


universe u v
end


universe u
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmented
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {K L M : Bic (R := R)}



def correction {f : K ⟶ L} (h : RowHomotopy f) : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ) :=
  total.map f (ComplexShape.up ℤ) - Homotopy.nullHomotopicMap' (homotopyTerm h)

end Lech.TotalGhost
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {K L M : Bic (R := R)}

 

def Shifted (n : ℕ) (f : K.total (ComplexShape.up ℤ) ⟶ L.total (ComplexShape.up ℤ)) : Prop :=
  ∀ p q i : ℤ, ∀ hpq : p+q=i,
    ∃ p' q' : ℤ, p'+(n:ℤ)=p ∧ q'=q+(n:ℤ) ∧
      ∃ hp'q' : p'+q'=i, ∃ a : (K.X p).X q ⟶ (L.X p').X q',
        K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ f.f i =
          a ≫ L.ιTotal (ComplexShape.up ℤ) p' q' i hp'q'

end Lech.TotalGhost


open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechMapCochain
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)


def degreeSequenceIso (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ) :
    ((Lech.discreteShortComplex (degreeSequenceFamily K S i)).map
      (colim (C:=ModuleCat.{u} R))) ≅
    ((S.map (functor K)).map (eval (ModuleCat.{u} R) (.up ℤ) i)) := by
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ ((functor K).map S.f).f i =
      colim.map (Lech.discreteShortComplex (degreeSequenceFamily K S i)).f ≫ 𝟙 _
    refine (Category.id_comp _).trans (Eq.trans ?_ (Category.comp_id _).symm)
    refine mapBifunctor.hom_ext (K₁ := K) (K₂ := S.X₁)
      (F := curriedTensor (ModuleCat.{u} R)) (c := .up ℤ) (fun p q hpq => ?_)
    symm
    change colimit.ι (Lech.discreteShortComplex (degreeSequenceFamily K S i)).X₁
      ⟨⟨(p,q),hpq⟩⟩ ≫ colim.map _ = _
    rw [colimit.ι_map]
    symm
    change ιMapBifunctor K S.X₁ (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
      ((functor K).map S.f).f i = _
    rw [map_f,ι_degreeMap]
    rfl
  · change 𝟙 _ ≫ ((functor K).map S.g).f i =
      colim.map (Lech.discreteShortComplex (degreeSequenceFamily K S i)).g ≫ 𝟙 _
    refine (Category.id_comp _).trans (Eq.trans ?_ (Category.comp_id _).symm)
    refine mapBifunctor.hom_ext (K₁ := K) (K₂ := S.X₂)
      (F := curriedTensor (ModuleCat.{u} R)) (c := .up ℤ) (fun p q hpq => ?_)
    symm
    change colimit.ι (Lech.discreteShortComplex (degreeSequenceFamily K S i)).X₂
      ⟨⟨(p,q),hpq⟩⟩ ≫ colim.map _ = _
    rw [colimit.ι_map]
    symm
    change ιMapBifunctor K S.X₂ (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q i hpq ≫
      ((functor K).map S.g).f i = _
    rw [map_f,ι_degreeMap]
    rfl



end Lech.TensorTotal.Right
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_BicomplexImageLift
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {M N T : ModuleCat.{u} R}
  (f : M ⟶ N) (hf : Function.Injective f.hom) (g : T ⟶ N) (hr : g.hom.range≤f.hom.range)
include hf hr in
lemma imageLift_comp : imageLift f hf g hr ≫ f=g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f.hom ((LinearEquiv.ofInjective f.hom hf).symm _) = g.hom x
  exact congrArg Subtype.val ((LinearEquiv.ofInjective f.hom hf).apply_symm_apply _)
end Lech.TensorIdeal

namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {K L M : Bic (R:=R)}
  (f : K ⟶ L) (hf : ∀ p q,Function.Injective ((f.f p).f q).hom) (g : M ⟶ L)
  (hr : ∀ p q,((g.f p).f q).hom.range≤((f.f p).f q).hom.range)
def imageRowLift (p : ℤ) : M.X p ⟶ K.X p := by
  letI : ∀ q, Mono ((f.f p).f q) := fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q)
  exact ComplexLift.factor (f.f p) (g.f p)
    (fun q => TensorIdeal.imageLift ((f.f p).f q) (hf p q) ((g.f p).f q) (hr p q))
    (fun q => TensorIdeal.imageLift_comp ((f.f p).f q) (hf p q) ((g.f p).f q) (hr p q))
include hf hr in
lemma imageRowLift_comp (p : ℤ) : imageRowLift f hf g hr p ≫ f.f p=g.f p := by
  let : ∀ q, Mono ((f.f p).f q) := fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q)
  exact ComplexLift.factor_comp _ _ _ _
end Lech.TotalGhost

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorReduction
attribute [-instance] _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open scoped TensorProduct
universe u
variable {R A M N : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
  (I : Ideal R) (f : M →ₗ[A] N) (hf : Function.Surjective f)
  (hker : (f.restrictScalars R).ker = I • (⊤ : Submodule R M))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

include hf hker in
lemma kernel_rTensor : ((f.rTensor V).restrictScalars R).ker =
    I • (⊤ : Submodule R (M ⊗[A] V)) := by
  have hex := _root_.rTensor_exact V f.exact_subtype_ker_map hf
  apply le_antisymm
  · intro x hx
    obtain ⟨y,rfl⟩ := hex x |>.mp hx
    clear hx
    induction y using OAI.tensorInductionOn with
    | tmul m v =>
        change m.val ⊗ₜ[A] v ∈ _
        have hm : m.val ∈ I • (⊤ : Submodule R M) := hker ▸ m.property
        refine Submodule.smul_induction_on hm (fun r hr m _ => ?_) (fun m m' hm hm' => ?_)
        · rw [←TensorProduct.smul_tmul']
          exact Submodule.smul_mem_smul hr Submodule.mem_top
        · rw [TensorProduct.add_tmul]
          exact Submodule.add_mem _ hm hm'
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro r hr x _
    induction x using OAI.tensorInductionOn with
    | tmul m v =>
        rw [TensorProduct.smul_tmul']
        change f (r • m) ⊗ₜ[A] v=0
        have hm : r • m ∈ (f.restrictScalars R).ker :=
          hker ▸ Submodule.smul_mem_smul hr Submodule.mem_top
        have hfm : f (r • m)=0 := LinearMap.mem_ker.mp hm
        rw [hfm,TensorProduct.zero_tmul]
    | add x y hx hy => rw [smul_add]; exact Submodule.add_mem _ (hx Submodule.mem_top) (hy Submodule.mem_top)

 
def quotientTensorEquiv :
    ((M ⊗[A] V) ⧸ (I • (⊤ : Submodule R (M ⊗[A] V)))) ≃ₗ[R] (N ⊗[A] V) :=
  (Submodule.quotEquivOfEq _ _ (kernel_rTensor I f hf hker V).symm).trans
    (LinearMap.quotKerEquivOfSurjective ((f.rTensor V).restrictScalars R)
      (LinearMap.rTensor_surjective V hf))

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCoefficientFibre
attribute [-instance] _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open scoped TensorProduct
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  (I : Ideal R) (q : A →ₗ[A] M) (hq : Function.Surjective q)
  (hker : (q.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]



def quotientUnitTensorEquiv :
    (V ⧸ (I • (⊤ : Submodule R V))) ≃ₗ[R] (M ⊗[A] V) :=
  (Submodule.Quotient.equiv _ _ ((TensorProduct.lid A V).symm.restrictScalars R)
    (map_ideal_smul_top I _)).trans (quotientTensorEquiv I q hq hker V)

lemma quotientUnitTensorEquiv_mk (v : V) :
    quotientUnitTensorEquiv I q hq hker V (Submodule.Quotient.mk v) = q 1 ⊗ₜ[A] v := by
  change (((q.rTensor V).restrictScalars R).quotKerEquivOfSurjective
    (LinearMap.rTensor_surjective V hq))
      ((Submodule.quotEquivOfEq _ _ (kernel_rTensor I q hq hker V).symm)
        (Submodule.Quotient.mk (1 ⊗ₜ[A] v))) = _
  rw [Submodule.quotEquivOfEq_mk]
  rfl

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionZeroStability
attribute [-instance] _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

 
def TorsionLength.DirectSumZero (ell : TorsionLength I) : Prop :=
  ∀ {ι : Type u} (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (a : ℕ), (∀ i, I^a ≤ Module.annihilator R (M i)) →
      (∀ i, ell.value (ModuleCat.of R (M i))=0) → ell.value (ModuleCat.of R (⨁ i, M i))=0

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FibreSquare
attribute [-instance] _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u
section Quotient
variable {R M N : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (I : Ideal R)

lemma idealQuotientMap_mk (f : M →ₗ[R] N) (x : M) :
    idealQuotientMap I f (Submodule.Quotient.mk x)=Submodule.Quotient.mk (f x) := rfl

lemma quotientTensorEquiv_mk {A P Q : Type u} [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]
    (f : P →ₗ[A] Q) (hf : Function.Surjective f)
    (hker : (f.restrictScalars R).ker = I • (⊤ : Submodule R P))
    (V : Type u) [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
    (p : P) (v : V) :
    quotientTensorEquiv I f hf hker V (Submodule.Quotient.mk (p ⊗ₜ[A] v))=f p ⊗ₜ[A] v := by
  change (((f.rTensor V).restrictScalars R).quotKerEquivOfSurjective
    (LinearMap.rTensor_surjective V hf))
      ((Submodule.quotEquivOfEq _ _ (kernel_rTensor I f hf hker V).symm)
        (Submodule.Quotient.mk (p ⊗ₜ[A] v))) = _
  rw [Submodule.quotEquivOfEq_mk]
  rfl

end Quotient

end Lech.TensorIdeal

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorPushout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open TensorProduct
namespace Lech.TensorPushout
variable (A P E N : Type*) [CommRing A] [CommRing P] [CommRing E]
  [Algebra A P] [Algebra A E] [AddCommGroup N]
  [Module A N] [Module E N] [IsScalarTower A E N]

attribute [local instance] OAI.Lech.TensorPushout.instAlgebraTensorProduct_solutions
def equiv : (P ⊗[A] E) ⊗[E] N ≃ₗ[P] P ⊗[A] N where
  __ := (aux A P E N).toAddEquiv
  map_smul' p x := by
    change aux A P E N (p • x) = p • aux A P E N x
    induction x using OAI.tensorInductionOn with
    | tmul b n =>
      induction b using OAI.tensorInductionOn with
      | tmul a e =>
        change aux A P E N (p • ((a ⊗ₜ[A] e) ⊗ₜ[E] n)) = _
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', aux_tmul, aux_tmul,
          TensorProduct.smul_tmul']
      | add b c hb hc =>
        change aux A P E N (p • ((b+c) ⊗ₜ[E] n)) = _
        simpa only [TensorProduct.add_tmul, smul_add, map_add] using congrArg₂ (·+·) hb hc
    | add x y hx hy =>
      change aux A P E N (p • (x+y)) = _
      simpa only [smul_add, map_add] using congrArg₂ (·+·) hx hy

@[simp] lemma equiv_tmul (p : P) (e : E) (n : N) :
    equiv A P E N ((p ⊗ₜ[A] e) ⊗ₜ[E] n) = p ⊗ₜ[A] (e • n) := rfl
end Lech.TensorPushout

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorRingTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ChangeOfRings
namespace Lech.TensorTwist
open CategoryTheory
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u
variable {D C C' : Type u} [CommRing D] [CommRing C] [CommRing C']

def extendEquiv (f : D →+* C) (e : C ≃+* C') (M : ModuleCat.{u} D) :
    LinearEquiv (σ' := (e.symm : C' →+* C)) (e : C →+* C')
      ((ModuleCat.extendScalars f).obj M) ((ModuleCat.extendScalars ((e : C →+* C').comp f)).obj M) where
  __ := (TensorProduct.congr (scalarEquiv f e) (LinearEquiv.refl D M)).toAddEquiv
  map_smul' c t := by
    induction t using OAI.tensorInductionOn with
    | tmul x m =>
      exact congrArg (fun (v : C') => v ⊗ₜ[D, (e : C →+* C').comp f] m)
        (e.map_mul c x)
    | add x y hx hy =>
      let F : ((ModuleCat.extendScalars f).obj M) →+
          ((ModuleCat.extendScalars ((e : C →+* C').comp f)).obj M) :=
        (TensorProduct.congr (scalarEquiv f e) (LinearEquiv.refl D M)).toAddEquiv.toAddMonoidHom
      have hs : c • (show (ModuleCat.extendScalars f).obj M from x + y) =
          c • (show (ModuleCat.extendScalars f).obj M from x) +
            c • (show (ModuleCat.extendScalars f).obj M from y) :=
        smul_add c (show (ModuleCat.extendScalars f).obj M from x)
          (show (ModuleCat.extendScalars f).obj M from y)
      exact (congrArg F hs).trans ((F.map_add _ _).trans
        ((congrArg₂ (·+·) hx hy).trans ((smul_add (e c) (F x) (F y)).symm.trans
          (congrArg (fun z => e c • z) (F.map_add x y).symm))))

def algebraExtendEquiv {P : Type u} [CommRing P] [Algebra P C] [Algebra P C']
    (f : D →+* C) (e : C ≃ₐ[P] C') (M : ModuleCat.{u} D) :
    (ModuleCat.restrictScalars (algebraMap P C)).obj ((ModuleCat.extendScalars f).obj M) ≃ₗ[P]
      (ModuleCat.restrictScalars (algebraMap P C')).obj
        ((ModuleCat.extendScalars (e.toRingHom.comp f)).obj M) where
  __ := (extendEquiv f e.toRingEquiv M).toAddEquiv
  map_smul' r x := by
    have h := (extendEquiv f e.toRingEquiv M).map_smulₛₗ (algebraMap P C r)
      (show (ModuleCat.extendScalars f).obj M from x)
    exact h.trans (congrArg
      (fun c : C' => c • extendEquiv f e.toRingEquiv M x) (e.commutes r))

end Lech.TensorTwist

end

end OAI
end


