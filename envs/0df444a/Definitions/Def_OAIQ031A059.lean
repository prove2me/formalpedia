-- Prove2me | Definitions.Def_OAIQ031A059
-- name    : OAIQ031A059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:10:29.329774+00:00
-- url     : https://prove2.me/theorems/b0dfc236-c1d3-4ab0-bf6d-083c8bf93567
-- title:
--   Definitions bundle OAIQ031A059 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 1 instance and 10 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConeCohomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCohomology.lean), [`AuslanderReiten_Coordinates_GradedConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/GradedConjugate.lean), [`AuslanderReiten_Coordinates_GradedRowCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/GradedRowCoordinates.lean), [`AuslanderReiten_Coordinates_ShiftedConjugateAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ShiftedConjugateAction.lean), [`AuslanderReiten_Ext_ExtBridge`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtBridge.lean), [`AuslanderReiten_Fibers_FiberProjectionProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProjectionProfile.lean), [`AuslanderReiten_HomComplex_FullHomHomotopyMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomHomotopyMaps.lean), [`AuslanderReiten_HomComplex_FullHomShiftedMaps`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomShiftedMaps.lean), [`AuslanderReiten_HomComplex_FullHomZeroProjection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomZeroProjection.lean), [`AuslanderReiten_Homology_TriangleConnectingProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleConnectingProduct.lean), [`AuslanderReiten_Tensor_TwistedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A031`, `OAIQ031A035`, `OAIQ031A040`, `OAIQ031A041` and `OAIQ031A042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A075` and `OAIQ031A076`; the proof of `OAI.ArExplicit.PositiveExtVanish.scalarExtension`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A031
import Definitions.Def_OAIQ031A035
import Definitions.Def_OAIQ031A040
import Definitions.Def_OAIQ031A041
import Definitions.Def_OAIQ031A042

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCohomology
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

variable [HasHomotopyCofiber φ]

theorem coneEnd_nontrivial_of_kernel
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (w : CohomologyClass G G n × CohomologyClass F F n)
    (hw : w ≠ 0) (hcomp : coneComparison φ n w = 0) :
    Nontrivial (CohomologyClass (mappingCone φ) (mappingCone φ) n) := by
  obtain ⟨a, b⟩ := w
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective b
  rw [coneComparison_mk, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)] at hcomp
  obtain ⟨c, hc⟩ := hcomp
  have hz : δ n (n + 1) (coneEnd φ a.1 b.1 (-c)) = 0 := by
    apply (coneEnd_closed_iff φ a.1 b.1 (-c)).mpr
    refine ⟨Cocycle.δ_eq_zero a _, Cocycle.δ_eq_zero b _, ?_⟩
    rw [δ_neg, hc]
    change -(b.1.comp (Cochain.ofHom φ) (add_zero n) +
      (n + 1).negOnePow • (Cochain.ofHom φ).comp a.1 (zero_add n)) + _ + _ = 0
    abel
  let z := Cocycle.mk (coneEnd φ a.1 b.1 (-c)) (n + 1) rfl hz
  have hne : CohomologyClass.mk z ≠ 0 := by
    intro heq
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at heq
    obtain ⟨y, hy⟩ := heq
    have hrecon := coneEnd_all_reconstruct φ hzero y
    rw [← hrecon] at hy
    change δ (n - 1) n (coneEnd φ (coneEndA φ y) (coneEndB φ y) (coneEndC φ y)) =
      CochainComplex.mappingCone.descCochain φ
        (CochainComplex.mappingCone.liftCochain φ b.1 (-c) (by omega))
        (CochainComplex.mappingCone.liftCochain φ 0 a.1 rfl) (by omega) at hy
    obtain ⟨ha, hb, _⟩ := (coneEnd_boundary_iff φ (n - 1) (by omega)
      (coneEndA φ y) (coneEndB φ y) (coneEndC φ y) a.1 b.1 (-c)).mp hy
    apply hw
    apply Prod.ext
    · apply (CohomologyClass.mk_eq_zero_iff a).mpr
      exact (mem_coboundaries_iff a (n - 1) (by omega)).mpr ⟨coneEndA φ y, ha⟩
    · apply (CohomologyClass.mk_eq_zero_iff b).mpr
      apply (mem_coboundaries_iff b (n - 1) (by omega)).mpr
      exact ⟨-(coneEndB φ y), by rw [δ_neg]; exact hb⟩
  exact ⟨⟨CohomologyClass.mk z, 0, hne⟩⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ShiftedConjugateAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n m : ℤ) (e : X ≅ Y⟦n⟧) (f : X ≅ Z⟦m⟧) (c : Z ⟶ Y)

theorem shiftedConjugate_action (a : ℤ) (v : S ⟶ Z⟦a⟧) :
    ShiftedHom.comp (v ≫ c⟦a⟧') (negativeShiftIso n e).hom (by omega : -n+a=a-n) =
      ShiftedHom.comp
        (ShiftedHom.comp v (negativeShiftIso m f).hom (by omega : -m+a=a-m))
        (shiftedConjugate n m e f c) (by omega : (m-n)+(a-m)=a-n) := by
  unfold shiftedConjugate
  rw [ShiftedHom.comp_assoc v (negativeShiftIso m f).hom
    (ShiftedHom.comp f.hom
      (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
        (by omega : -n+0 = -n)) (by omega : -n+m=m-n))
    (by omega : -m+a=a-m) (by omega : (m-n)+ -m = -n)
    (by omega : (m-n)+ -m+a=a-n)]
  rw [← ShiftedHom.comp_assoc (negativeShiftIso m f).hom f.hom
    (ShiftedHom.comp (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
      (by omega : -n+0 = -n))
    (by omega : m+ -m=0) (by omega : -n+m=m-n) (by omega : -n+m+ -m= -n)]
  rw [negativeShiftIso_comp_hom, ShiftedHom.mk₀_id_comp]
  have h := ShiftedHom.comp_assoc v (ShiftedHom.mk₀ (0:ℤ) rfl c) (negativeShiftIso n e).hom
    (by omega : 0+a=a) (by omega : -n+0= -n) (by omega : -n+0+a=a-n)
  simpa only [ShiftedHom.comp_mk₀] using h

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_GradedConjugate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable {X Y Z S : C} (n m d : ℤ) (h : -n+m=d)
variable (e : X ≅ Y⟦n⟧) (f : X ≅ Z⟦m⟧) (c : Z ⟶ Y)

theorem gradedConjugate_action (a : ℤ) (v : S ⟶ Z⟦a⟧) :
    ShiftedHom.comp (v ≫ c⟦a⟧') (negativeShiftIso n e).hom (by omega : -n+a=a-n) =
      ShiftedHom.comp
        (ShiftedHom.comp v (negativeShiftIso m f).hom (by omega : -m+a=a-m))
        (gradedConjugate n m d h e f c) (by omega : d+(a-m)=a-n) := by
  have hd : d=m-n := by omega
  revert h
  rw [hd]
  intro h
  exact shiftedConjugate_action n m e f c a v

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleConnectingProduct
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace ArExplicit.TriangleGradedSequence
universe u v w
variable (k : Type u) [CommRing k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
variable (T : Triangle C) (X : C)

theorem connecting_eq_product (n : ℤ) (v : Top T X n) :
    connecting k T X n v = ShiftedHom.comp v T.mor₃ (add_comm 1 n) := by
  change v ≫ ((n.negOnePow • T.mor₃⟦n⟧' ≫
    (CategoryTheory.shiftFunctorComm C 1 n).hom.app T.obj₁) ≫
      (nextIso T n).inv.hom₁) = _
  rw [integerUnit_smul k, nextIso_inv_first]
  simp only [ShiftedHom.comp,
    CategoryTheory.shiftFunctorComm_eq C 1 n (n+1) (add_comm 1 n),
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  erw [Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]
  rfl

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_GradedRowCoordinates
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w

theorem connectingRow {k : Type u} [CommRing k] [CharP k 2]
    {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
    [Limits.HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (X V W : C) (a : ℤ) (v : X ⟶ T.obj₃⟦a⟧)
    (p r : T.obj₃ ⟶ V) (s : V ⟶ W⟦(1 : ℤ)⟧) (c d : W ⟶ T.obj₁)
    (h : T.mor₃ = (p ≫ s) ≫ c⟦(1 : ℤ)⟧' + (r ≫ s) ≫ d⟦(1 : ℤ)⟧') :
    TriangleGradedSequence.connecting k T X a v =
      ShiftedHom.comp (v ≫ p⟦a⟧') s (add_comm 1 a) ≫ c⟦a+1⟧' +
      ShiftedHom.comp (v ≫ r⟦a⟧') s (add_comm 1 a) ≫ d⟦a+1⟧' := by
  erw [TriangleGradedSequence.connecting_eq_product, h, shiftedComp_row]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtBridge
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem positiveExtVanish_iff_completeResolution
    (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n))
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom)
    (e : M ≃ₗ[R] CompleteCokernel P) :
    PositiveExtVanish R M N ↔
      ∀ (n : ℕ) (f : P.X ((n + 1 : ℕ) : ℤ) →ₗ[R] N),
        f.comp (P.d ((n + 2 : ℕ) : ℤ) ((n + 1 : ℕ) : ℤ)).hom = 0 →
        ∃ g : P.X (n : ℤ) →ₗ[R] N,
          f = g.comp (P.d ((n + 1 : ℕ) : ℤ) (n : ℤ)).hom := by
  let Q := transportProjectiveResolution (completeCokernelResolution P hproj hex)
    e.symm.toModuleIso
  refine (positiveExtVanish_iff_resolution R M N Q).trans ⟨?_, ?_⟩
  · intro h n f hf
    have hfc : Q.complex.d (n + 2) (n + 1) ≫ ModuleCat.ofHom f = 0 := by
      change (nonnegativeTail P).d (n + 1 + 1) (n + 1) ≫ ModuleCat.ofHom f = 0
      rw [nonnegativeTail_d]
      exact ModuleCat.hom_ext hf
    obtain ⟨g, hg⟩ := h n (ModuleCat.ofHom f) hfc
    refine ⟨g.hom, ?_⟩
    change (nonnegativeTail P).d (n + 1) n ≫ g = ModuleCat.ofHom f at hg
    rw [nonnegativeTail_d] at hg
    exact (congrArg ModuleCat.Hom.hom hg).symm
  · intro h n f hf
    change (nonnegativeTail P).d (n + 1 + 1) (n + 1) ≫ f = 0 at hf
    rw [nonnegativeTail_d] at hf
    obtain ⟨g, hg⟩ := h n f.hom (congrArg ModuleCat.Hom.hom hf)
    refine ⟨ModuleCat.ofHom g, ?_⟩
    change (nonnegativeTail P).d (n + 1) n ≫ ModuleCat.ofHom g = f
    rw [nonnegativeTail_d]
    exact ModuleCat.hom_ext hg.symm

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProjectionProfile
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
include hT

theorem first_surjective_of_top_subsingleton (n : ℤ) [Subsingleton (Top T X n)] :
    Function.Surjective (first k T X n) := by
  rw [← LinearMap.range_eq_top, exact_middle k T X hT n]
  apply top_unique
  intro x _
  exact Subsingleton.elim _ _

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomShiftedMaps
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {K L M : CochainComplex C ℤ} (n : ℤ)

theorem fullHomShiftedHomotopyEquiv_precomp (f : K ⟶ L) (x : CohomologyClass L M n) :
    fullHomShiftedHomotopyEquiv k K M n (fullHomPrecomp f n x) =
      (HomotopyCategory.quotient C _).map f ≫ fullHomShiftedHomotopyEquiv k L M n x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPrecomp_mk, fullHomShiftedHomotopyEquiv_mk,
    fullHomShiftedHomotopyEquiv_mk, Cocycle.equivHomShift_symm_precomp,
    Functor.map_comp, Category.assoc]
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomHomotopyMaps
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} (n : ℤ)
include k

theorem fullHomPrecomp_congr {f g : K ⟶ L}
    (h : (HomotopyCategory.quotient C _).map f = (HomotopyCategory.quotient C _).map g)
    (x : CohomologyClass L M n) : fullHomPrecomp f n x = fullHomPrecomp g n x := by
  apply (fullHomShiftedHomotopyEquiv k K M n).injective
  rw [fullHomShiftedHomotopyEquiv_precomp, fullHomShiftedHomotopyEquiv_precomp, h]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomZeroProjection
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {K L M : CochainComplex C ℤ}

theorem fullHomPostcomp_ofHom (f : K ⟶ L) (g : L ⟶ M) :
    fullHomPostcomp g 0 (CohomologyClass.mk (Cocycle.ofHom f)) =
      CohomologyClass.mk (Cocycle.ofHom (f ≫ g)) := by
  rw [← fullHomPostcomp_identity f, fullHomPostcomp_comp, fullHomPostcomp_identity]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

instance instIsScalarTower : IsScalarTower k R (TwistedLeftModule k R σ M) where
  smul_assoc a r x := by ext; simp [smul_assoc]

end TwistedLeftModule

end ArExplicit

end OAI
end


