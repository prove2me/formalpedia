-- Prove2me | Definitions.Def_OAIQ031A057
-- name    : OAIQ031A057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:09:01.179799+00:00
-- url     : https://prove2.me/theorems/e6d9909f-aadf-4aa4-888a-c495eb0e417c
-- title:
--   Definitions bundle OAIQ031A057 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 2 definitions, 2 instances and 13 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.canonicalTmul`, `OAI.ArExplicit.rawConeQuotient`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Cones_CokernelProduct`, `AuslanderReiten_Cones_ConeConnectingCoordinates`, `AuslanderReiten_Cones_MappingConeCokernel`, `AuslanderReiten_Cones_TwoCone`, `AuslanderReiten_Ext_ExtBridge`, `AuslanderReiten_HomComplex_FullHomShiftedProducts`, `AuslanderReiten_Homology_ShortExactConnecting`, `AuslanderReiten_Homology_TriangleGradedSequence`, `AuslanderReiten_Modules_InductionBimodule`, `AuslanderReiten_Resolutions_MapResolutionExtConjugate`, `AuslanderReiten_Tensor_ExternalTensorScalarPure`, `AuslanderReiten_Tensor_ExternalTensorTransport`, `AuslanderReiten_Tensor_TwistedTensor`.
--
--   **Imports.** It imports the bundles `OAIQ031A028`, `OAIQ031A029`, `OAIQ031A031`, `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A035`, `OAIQ031A036`, `OAIQ031A038`, `OAIQ031A039` and `OAIQ031A040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A072`, `OAIQ031A073`, `OAIQ031A074`, `OAIQ031A075` and `OAIQ031A076`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A028
import Definitions.Def_OAIQ031A029
import Definitions.Def_OAIQ031A031
import Definitions.Def_OAIQ031A032
import Definitions.Def_OAIQ031A033
import Definitions.Def_OAIQ031A035
import Definitions.Def_OAIQ031A036
import Definitions.Def_OAIQ031A038
import Definitions.Def_OAIQ031A039
import Definitions.Def_OAIQ031A040

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CokernelProduct
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

variable {R M N P Q : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

@[simp]
theorem cokernelProductEquiv_mk (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (n : N) (q : Q) :
    cokernelProductEquiv f g (Submodule.Quotient.mk (n, q)) =
      (Submodule.Quotient.mk n, Submodule.Quotient.mk q) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit

open CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

variable {L : Type u} [AddCommGroup L] [Module R L]
variable (p : CochainCokernel G →ₗ[R] L)
variable (hex : Function.Exact (cochainCokernelMap φ) p)

def rawConeQuotient : CochainCokernel (mappingCone φ) →ₗ[R] L :=
  (ConeQuotientMap.quotientMap (F.d (-1) 0).hom (F.d 0 1).hom
    (G.d (-1) 0).hom (φ.f 0).hom (cochainCokernelMap φ) p
    (rawCokernelMap_comm φ) hex).comp (rawConeBlockEquiv φ).toLinearMap

theorem rawConeQuotient_inr :
    (rawConeQuotient φ p hex).comp (cochainCokernelMap (mappingCone.inr φ)) = p := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range (G.d (-1) 0).hom).mkQ_surjective z
  change p (Submodule.Quotient.mk
    ((coneTermEquiv φ 0 (((mappingCone.inr φ).f 0).hom x)).1)) = p (Submodule.Quotient.mk x)
  congr 2
  change (((mappingCone.inr φ).f 0 ≫ (mappingCone.snd φ).v 0 0 (add_zero 0)).hom x) = x
  simp

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeConnectingCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable (H : CochainComplex (ModuleCat.{u} R) ℤ)

variable {H} {F G : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (κ : H ⟶ mappingCone φ)

variable (hi : Function.Injective (cochainCokernelMap φ))

variable (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)

theorem coneLiftMiddle_square :
    p.comp (coneLiftMiddle φ κ) =
      ((rawConeQuotient φ p he).comp (cochainCokernelMap κ)).comp
        (LinearMap.range (H.d (-1) 0).hom).mkQ := by
  ext z
  rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
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

variable {R : Type u} [Ring R]

variable (D : Data R)

theorem firstD_square (n : ℕ) : (firstD D n).comp (firstD D (n+1)) = 0 :=
  coneBlock_comp_zero _ _ _ _ _ _ (D.square n) (D.square (n+2)) (D.first_comm n)

theorem secondOnFirst_comm (n : ℕ) :
    (firstD D n).comp (secondOnFirst D (n+1)) =
      (secondOnFirst D n).comp (firstD D (n+3)) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  apply Prod.ext
  · change D.d n (D.second (n+1) x) + D.first n (D.second (n+3) y) =
      D.second n (D.d (n+3) x + D.first (n+3) y)
    rw [map_add, show D.d n (D.second (n+1) x) =
      D.second n (D.d (n+3) x) from DFunLike.congr_fun (D.second_comm n) x,
      show D.first n (D.second (n+3) y) =
      D.second n (D.first (n+3) y) from DFunLike.congr_fun (D.comparisons_comm n) y]
  · change -D.d (n+2) (D.second (n+3) y) =
      D.second (n+2) (-D.d (n+5) y)
    rw [map_neg]
    exact congrArg Neg.neg (DFunLike.congr_fun (D.second_comm (n+2)) y)

theorem firstD_exact (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    Function.Exact (firstD D (n+1)) (firstD D n) :=
  coneBlock_exact _ _ _ _ _ _ (hex n) (hex (n+2)) (D.first_comm n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtBridge
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable (R : Type u) [Ring R]
  (M N : Type u) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem positiveExtVanish_of_completeResolution
    (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n))
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom)
    (hdual : ∀ (n : ℤ) (f : P.X n →ₗ[R] N),
      f.comp (P.d (n + 1) n).hom = 0 →
      ∃ g : P.X (n - 1) →ₗ[R] N, f = g.comp (P.d n (n - 1)).hom)
    (e : M ≃ₗ[R] CompleteCokernel P) : PositiveExtVanish R M N := by
  let Q := transportProjectiveResolution (completeCokernelResolution P hproj hex)
    e.symm.toModuleIso
  apply (positiveExtVanish_iff_resolution R M N Q).2
  intro n f hf
  change (nonnegativeTail P).d (n + 1 + 1) (n + 1) ≫ f = 0 at hf
  rw [nonnegativeTail_d] at hf
  have aux (i j l : ℤ) (hi : i = j + 1) (hl : l = j - 1)
      (f : P.X j →ₗ[R] N) (hf : f.comp (P.d i j).hom = 0) :
      ∃ g : P.X l →ₗ[R] N, f = g.comp (P.d j l).hom := by
    subst i
    subst l
    exact hdual j f hf
  obtain ⟨g, hg⟩ := aux ((n + 1 + 1 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ) (n : ℤ)
    (by omega) (by omega) f.hom (congrArg ModuleCat.Hom.hom hf)
  refine ⟨ModuleCat.ofHom g, ?_⟩
  change (nonnegativeTail P).d (n + 1) n ≫ ModuleCat.ofHom g = f
  rw [nonnegativeTail_d]
  exact ModuleCat.hom_ext hg.symm

theorem GorensteinProjective.positiveExt_regular
    (h : GorensteinProjective R M) : PositiveExtVanish R M R := by
  obtain ⟨P, hp, he, hd, ⟨e⟩⟩ := h
  exact positiveExtVanish_of_completeResolution R M R P (fun n => (hp n).2) he hd e

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomShiftedProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u v w

variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem fullHomShiftedHomotopyEquiv_product (x : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomShiftedHomotopyEquiv k K M (n+m) (CompleteComparison.fullHomProduct x y) =
      fullHomShiftedHomotopyEquiv k K L n x ≫
        (fullHomShiftedHomotopyEquiv k L M m y)⟦n⟧' ≫
          (CategoryTheory.shiftFunctorAdd' (HomotopyCategory C (ComplexShape.up ℤ)) m n
            (n+m) (add_comm m n)).inv.app ((HomotopyCategory.quotient C _).obj M) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective y
  rw [CompleteComparison.fullHomProduct_mk, fullHomShiftedHomotopyEquiv_mk,
    fullHomShiftedHomotopyEquiv_mk, fullHomShiftedHomotopyEquiv_mk,
    CompleteComparison.cocycleHom_product]
  exact map_shifted_composition (HomotopyCategory.quotient C _)
    (Cocycle.equivHomShift.symm x) (Cocycle.equivHomShift.symm y)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactConnecting
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)
variable (κ : H ⟶ mappingCone φ)

omit [Module.Injective R R] in
theorem coneProjectionCocycle_hom :
    Cocycle.equivHomShift.symm (cocycleProduct (Cocycle.ofHom κ) (mappingCone.fst φ)) =
      κ ≫ Cocycle.equivHomShift.symm (mappingCone.fst φ) := by
  apply HomologicalComplex.Hom.ext
  funext i
  rw [cocycleHom_component]
  change ((Cochain.ofHom κ).comp (mappingCone.fst φ).val rfl).v i (i+1) rfl = _
  rw [Cochain.comp_v _ _ rfl i i (i+1) (by omega) rfl, Cochain.ofHom_v]
  simp only [HomologicalComplex.comp_f, cocycleHom_component] <;> rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleGradedSequence
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit.TriangleGradedSequence

universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (X : C)

variable (hT : T ∈ distTriang C)
include hT

theorem exact_top (n : ℤ) :
    LinearMap.range (second k T X n) = LinearMap.ker (connecting k T X n) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ (T⟦n⟧).mor₂) ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁) = 0
    erw [Category.assoc, ← Category.assoc (T⟦n⟧).mor₂, comp_distTriang_mor_zero₂₃ _ (T.shift_distinguished hT n)]
    erw [Limits.zero_comp, Limits.comp_zero]
  · intro hf
    have hz : f ≫ (T⟦n⟧).mor₃ = 0 := by
      apply (cancel_mono (nextIso T n).inv.hom₁).mp
      change f ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁) = 0 at hf
      erw [Category.assoc, Limits.zero_comp]
      exact hf
    obtain ⟨g, hg⟩ := (T⟦n⟧).coyoneda_exact₃ (T.shift_distinguished hT n) f hz
    exact ⟨g, hg.symm⟩

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

instance instSMulCommClassMulOpposite_1 : SMulCommClass k Rᵐᵒᵖ (InductionBimodule ι) where
  smul_comm a r x := by ext; exact (smul_mul_assoc a x.value (ι r.unop)).symm

end InductionBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_MapResolutionExtConjugate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

theorem map_extMk_conjugate (a : X ⟶ F.obj X) (b : F.obj Y ⟶ Y)
    (φ : ProjectiveResolution.Hom P (mapResolution F P) a)
    (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n+1) n ≫ f = 0)
    (g : P.complex.X n ⟶ Y) (hg : P.complex.d (n+1) n ≫ g = 0)
    (hgf : g = (φ.hom.f n ≫ F.map f) ≫ b) :
    ((Ext.mk₀ a).comp ((P.extMk f (n+1) rfl hf).mapExactFunctor F) (zero_add n)).comp
      (Ext.mk₀ b) (add_zero n) =
        P.extMk g (n+1) rfl hg := by
  subst g
  erw [map_extMk, ProjectiveResolution.mk₀_comp_extMk _ _ _ _ φ,
    ProjectiveResolution.extMk_comp_mk₀]

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalarPure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def canonicalTmul (x : M) (y : N) : canonicalTensorObject k A B M N :=
  letI : Module k M := moduleCatBaseModule (k := k) (R := A) (ModuleCat.of A M)
  letI : Module k N := moduleCatBaseModule (k := k) (R := B) (ModuleCat.of B N)
  x ⊗ₜ[k] y

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

section Naturality
variable {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
variable (e : M →ₗ[k] M) (e' : M' →ₗ[k] M')
variable (f : N →ₗ[k] N) (f' : N' →ₗ[k] N')
variable (he : ∀ a x, e (a • x) = h a • e x)
variable (he' : ∀ a x, e' (a • x) = h a • e' x)
variable (hf : ∀ b x, f (b • x) = j b • f x)
variable (hf' : ∀ b x, f' (b • x) = j b • f' x)
variable (a : M ⟶ M') (b : N ⟶ N')
variable (ha : ∀ x, a.hom (e x) = e' (a.hom x))
variable (hb : ∀ x, b.hom (f x) = f' (b.hom x))

include ha hb in
theorem tensorSemilinear_natural :
    ModuleCat.ofHom (X := moduleObject k A B M N) (Y := (F).obj (moduleObject k A B M N))
      (tensorSemilinear k A B h j e f he hf) ≫
      (F).map
        (mapHom k A B a b) =
    mapHom k A B a b ≫ ModuleCat.ofHom
      (X := moduleObject k A B M' N') (Y := (F).obj (moduleObject k A B M' N'))
      (tensorSemilinear k A B h j e' f' he' hf') := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let w : M ⊗[k] N := z
  change TensorProduct.map (a.hom.restrictScalars k) (b.hom.restrictScalars k)
      (TensorProduct.map e f w) =
    TensorProduct.map e' f' (TensorProduct.map (a.hom.restrictScalars k) (b.hom.restrictScalars k) w)
  induction w using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.restrictScalars_apply]
    exact congrArg₂ (fun s t => s ⊗ₜ[k] t) (ha x) (hb y)
end Naturality

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedLeftModule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

instance instSMulCommClass : SMulCommClass k R (TwistedLeftModule k R σ M) where
  smul_comm a r x := by ext; exact smul_comm a (σ.symm r) x.value

end TwistedLeftModule

end ArExplicit

end OAI
end


