-- Prove2me | Definitions.Def_OAIQ031A020
-- name    : OAIQ031A020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:57:19.52328+00:00
-- url     : https://prove2.me/theorems/eaa07bd0-602d-47c4-ad81-608eb922c9fa
-- title:
--   Definitions bundle OAIQ031A020 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 6 definitions, 1 inductive type or structure and 26 theorems. The definitions and types are `OAI.ArExplicit.TriangleGradedSequence.Middle`, `OAI.ArExplicit.TriangleGradedSequence.Top`, `OAI.ArExplicit.TriangleGradedSequence.nextIso`, `OAI.ArExplicit.TriangleGradedSequence.second`, `OAI.ArExplicit.TwoConeFiltration`, `OAI.ArExplicit.TwoConeFiltration.topProjectionEquiv`, `OAI.ArExplicit.sourceObject`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Complete_TateKoszul`, `AuslanderReiten_Cones_TwoConeFiltration`, `AuslanderReiten_Coordinates_IteratedShiftNaturality`, `AuslanderReiten_Evaluation_ConcreteBetaTransfer`, `AuslanderReiten_Evaluation_ConcreteBranchBeta`, `AuslanderReiten_Evaluation_ConcreteFreeCoefficient`, `AuslanderReiten_Evaluation_ConcreteFreeExtension`, `AuslanderReiten_Evaluation_EvaluatedAdjacentComponents`, `AuslanderReiten_Evaluation_EvaluatedTopConnecting`, `AuslanderReiten_Homology_DimensionOneDetector`, `AuslanderReiten_Homology_TriangleGradedSequence`, `AuslanderReiten_Homology_TriangleHomExact`, `AuslanderReiten_Resolutions_ConcreteNativeResolution`, `AuslanderReiten_Resolutions_CoverStepFullHom`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A040`, `OAIQ031A041` and `OAIQ031A043`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
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

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)}

section Transport

variable {U V W U' V' W' : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W] [AddCommGroup U'] [Module k U']
variable [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

theorem surjective_of_chart (f : U →ₗ[k] V) (f' : U' →ₗ[k] V')
    (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V')
    (h : ∀ u, b (f u) = f' (a u)) (hf : Function.Surjective f') :
    Function.Surjective f := by
  intro v
  obtain ⟨u, hu⟩ := hf (b v)
  refine ⟨a.symm u, b.injective ?_⟩
  rw [h, a.apply_symm_apply, hu]

theorem injective_of_chart (f : U →ₗ[k] V) (f' : U' →ₗ[k] V')
    (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V')
    (h : ∀ u, b (f u) = f' (a u)) (hf : Function.Injective f') :
    Function.Injective f := by
  intro u v huv
  apply a.injective
  apply hf
  rw [← h, ← h, huv]

theorem exact_of_charts (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (f' : U' →ₗ[k] V') (g' : V' →ₗ[k] W')
    (a : U ≃ₗ[k] U') (b : V ≃ₗ[k] V') (c : W ≃ₗ[k] W')
    (hf : ∀ u, b (f u) = f' (a u)) (hg : ∀ v, c (g v) = g' (b v))
    (he : LinearMap.range f' = LinearMap.ker g') :
    LinearMap.range f = LinearMap.ker g := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    change g (f u) = 0
    apply c.injective
    rw [hg, hf, map_zero]
    have hu : f' (a u) ∈ LinearMap.range f' := ⟨a u, rfl⟩
    rw [he] at hu
    exact hu
  · intro hv
    have hv' : b v ∈ LinearMap.ker g' := by
      change g' (b v) = 0
      rw [← hg, show g v = 0 from hv, map_zero]
    rw [← he] at hv'
    obtain ⟨u, hu⟩ := hv'
    refine ⟨a.symm u, b.injective ?_⟩
    rw [hf, a.apply_symm_apply, hu]

end Transport

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {k : Type u} [Field k]
variable (B D E K W : ℤ → Type u)
variable [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
variable [∀ n, AddCommGroup (E n)] [∀ n, Module k (E n)]
variable [∀ n, AddCommGroup (K n)] [∀ n, Module k (K n)]
variable [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]

structure TwoConeFiltration where
  row : ∀ n, D n →ₗ[k] B (n + 1)
  column : ∀ n, E n →ₗ[k] D (n + 1)
  bottom : ∀ n, B n →ₗ[k] K n
  middle : ∀ n, K n →ₗ[k] D n
  attach : ∀ n, E n →ₗ[k] K (n + 1)
  inclusion : ∀ n, K n →ₗ[k] W n
  projection : ∀ n, W n →ₗ[k] E n
  row_bottom : ∀ n, LinearMap.range (row n) = LinearMap.ker (bottom (n + 1))
  bottom_middle : ∀ n, LinearMap.range (bottom n) = LinearMap.ker (middle n)
  middle_row : ∀ n, LinearMap.range (middle n) = LinearMap.ker (row n)
  attach_inclusion : ∀ n, LinearMap.range (attach n) = LinearMap.ker (inclusion (n + 1))
  inclusion_projection : ∀ n, LinearMap.range (inclusion n) = LinearMap.ker (projection n)
  projection_attach : ∀ n, LinearMap.range (projection n) = LinearMap.ker (attach n)
  adjacent : ∀ n, (middle (n + 1)).comp (attach n) = column n

namespace TwoConeFiltration

variable {B D E K W}
variable (F : TwoConeFiltration (k := k) B D E K W)

theorem middle_injective (n : ℤ) (hrow : Function.Surjective (F.row n)) :
    Function.Injective (F.middle (n + 1)) := by
  have hb : F.bottom (n + 1) = 0 := by
    apply LinearMap.ext
    intro x
    have hx : x ∈ LinearMap.range (F.row n) := hrow x
    rw [F.row_bottom] at hx
    exact hx
  rw [← LinearMap.ker_eq_bot, ← F.bottom_middle, hb, LinearMap.range_zero]

theorem attach_surjective (n : ℤ) (hrow : Function.Surjective (F.row n))
    (hKoszul : LinearMap.range (F.column n) = LinearMap.ker (F.row (n + 1))) :
    Function.Surjective (F.attach n) := by
  intro x
  have hx : F.middle (n + 1) x ∈ LinearMap.ker (F.row (n + 1)) := by
    rw [← F.middle_row]
    exact LinearMap.mem_range_self _ x
  rw [← hKoszul] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, F.middle_injective n hrow ?_⟩
  change (F.middle (n + 1)).comp (F.attach n) z = _
  rw [F.adjacent, hz]

theorem inclusion_zero_next (n : ℤ) (h : Function.Surjective (F.attach n)) :
    F.inclusion (n + 1) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ LinearMap.range (F.attach n) := h x
  rw [F.attach_inclusion] at hx
  exact hx

variable (hrow : ∀ n : ℤ, n ≠ -1 → Function.Surjective (F.row n))
variable (hcolumn : ∀ n : ℤ, n ≠ 3 → Function.Injective (F.column n))
variable (hKoszul : ∀ n : ℤ,
  LinearMap.range (F.column n) = LinearMap.ker (F.row (n + 1)))

include hrow hKoszul in

theorem inclusion_zero (n : ℤ) (hn : n ≠ 0) : F.inclusion n = 0 := by
  have hp : n - 1 ≠ -1 := by omega
  have h := F.inclusion_zero_next (n - 1)
    (F.attach_surjective (n - 1) (hrow _ hp) (hKoszul _))
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at h
  exact h

include hrow in

theorem first_degree_four_subsingleton [Subsingleton (D 4)] : Subsingleton (K 4) := by
  have h : Function.Injective (F.middle 4) := by
    convert F.middle_injective 3 (hrow 3 (by decide)) using 1 <;> norm_num
  exact h.subsingleton

include hrow hKoszul in

theorem top_projection_bijective [Subsingleton (D 4)] :
    Function.Bijective (F.projection 3) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, ← F.inclusion_projection,
      F.inclusion_zero hrow hKoszul 3 (by decide), LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, F.projection_attach]
    let := F.first_degree_four_subsingleton hrow
    apply top_unique
    intro x _
    have hz : (3 : ℤ) + 1 = 4 := by decide
    have : Subsingleton (K (3 + 1)) := hz.symm ▸ F.first_degree_four_subsingleton hrow
    exact Subsingleton.elim _ _

include hrow hKoszul in

noncomputable def topProjectionEquiv [Subsingleton (D 4)] : W 3 ≃ₗ[k] E 3 :=
  LinearEquiv.ofBijective (F.projection 3) (F.top_projection_bijective hrow hKoszul)

end TwoConeFiltration
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_IteratedShiftNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit

universe v u
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n + 1))⟦(1 : ℤ)⟧)

omit [HasShift C ℤ] in
theorem compose_squares
    {A A' B B' D D' : C} {f : A ⟶ A'} {g : B ⟶ B'} {h : D ⟶ D'}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : B ⟶ D} {b' : B' ⟶ D'}
    (h₁ : f ≫ a' = a ≫ g) (h₂ : g ≫ b' = b ≫ h) :
    f ≫ (a' ≫ b') = (a ≫ b) ≫ h := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleHomExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit

universe u v w

section Triangle

variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)

include hT

theorem triangleHom_middle_exact :
    LinearMap.range (Linear.rightComp k X T.mor₁) =
      LinearMap.ker (Linear.rightComp k X T.mor₂) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ T.mor₁) ≫ T.mor₂ = 0
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, Limits.comp_zero]
  · intro h
    obtain ⟨g, hg⟩ := T.coyoneda_exact₂ hT f h
    exact ⟨g, hg.symm⟩

theorem shiftedTriangleHom_middle_exact (n : ℤ) :
    LinearMap.range (Linear.rightComp k X (T⟦n⟧).mor₁) =
      LinearMap.ker (Linear.rightComp k X (T⟦n⟧).mor₂) :=
  triangleHom_middle_exact k _ (T.shift_distinguished hT n) X

end Triangle
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleGradedSequence
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

abbrev Middle (n : ℤ) := X ⟶ (T⟦n⟧).obj₂
abbrev Top (n : ℤ) := X ⟶ (T⟦n⟧).obj₃

def nextIso (n : ℤ) : T⟦n + 1⟧ ≅ (T⟦n⟧)⟦(1 : ℤ)⟧ :=
  (CategoryTheory.shiftFunctorAdd' (Triangle C) n 1 (n + 1) rfl).app T

def second (n : ℤ) : Middle T X n →ₗ[k] Top T X n :=
  Linear.rightComp k X (T⟦n⟧).mor₂

variable (hT : T ∈ distTriang C)
include hT

omit hT [Limits.HasZeroObject C] [Pretriangulated C] in
theorem next_first (n : ℤ) :
    ((T⟦n⟧)⟦(1 : ℤ)⟧).mor₁ = -((T⟦n⟧).mor₁⟦(1 : ℤ)⟧') := by
  simp [Triangle.shiftFunctor, Triangle.shiftFunctor_eq]
  rfl

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ConcreteNativeResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
theorem augmentation_compose {C : Type*} [Category C]
    {P Q R S U V W : C} (a : P ⟶ Q) (b : Q ⟶ R) (p : R ⟶ S)
    (f : Q ⟶ U) (g : U ⟶ S) (u : P ⟶ V) (v : V ⟶ U)
    (z : P ⟶ W) (w : W ⟶ S)
    (hb : b ≫ p = f ≫ g) (ha : a ≫ f = u ≫ v) (hc : u ≫ (v ≫ g) = z ≫ w) :
    (a ≫ b) ≫ p = z ≫ w := by
  rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, hc]

universe u

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteBetaTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
theorem precompose_factor {C : Type*} [Category C]
    {P Q R S T : C} {f : P ⟶ Q} {g : Q ⟶ R} {h : R ⟶ S}
    {p : Q ⟶ T} {e : T ⟶ S} {j : P ⟶ T}
    (h₁ : g ≫ h = p ≫ e) (h₂ : f ≫ p = j) :
    (f ≫ g) ≫ h = j ≫ e := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂]

universe u

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteBranchBeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

theorem compositeValue {C : Type*} [Category C]
    {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {a : W ⟶ Y} {b : W ⟶ Z} (ha : f ≫ g = a) (hb : a ≫ h = b) :
    f ≫ g ≫ h = b := by
  rw [← Category.assoc, ha, hb]

universe u

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteFreeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
theorem threeValue {R : Type*} [Ring R] {U V W Z : ModuleCat R}
    {a : U ⟶ V} {b : V ⟶ W} {c : W ⟶ Z} {f : U ⟶ Z}
    {x : U} {y : V} {z : W} (hf : f = a ≫ b ≫ c)
    (ha : a x = y) (hb : b y = z) : f x = c z := by
  rw [hf, ModuleCat.comp_apply, ha, ModuleCat.comp_apply, hb]

theorem identityValue {R : Type*} [Ring R] {U : ModuleCat R}
    {a : U ⟶ U} (h : a = 𝟙 U) (x : U) : a x = x := by
  rw [h, ModuleCat.id_apply]

theorem comp_hom_apply {R : Type*} [Ring R] {U V W : ModuleCat R}
    (f : U ⟶ V) (g : V ⟶ W) (x : U) : (g.hom.comp f.hom) x = g (f x) := rfl

theorem transferFunctionValue {U V : Type*} {f g : U → V}
    (hf : ∀ x, f x = g x) {x : U} {y : V} (h : g x = y) : f x = y :=
  (hf x).trans h

universe u

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_ConcreteFreeExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.T

theorem fourTensor_ext {k R V W : Type*} [Field k]
    [AddCommGroup R] [Module k R] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] ((R ⊗[k] R) ⊗[k] (R ⊗[k] R))) (f g : V →ₗ[k] W)
    (h : ∀ a b c d : R,
      f (e.symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) =
        g (e.symm ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d)))) : f = g := by
  have hh : f.comp e.symm.toLinearMap = g.comp e.symm.toLinearMap := by
    ext a b c d
    exact h a b c d
  ext v
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
    LinearMap.congr_fun hh (e v)

universe u

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedTopConnecting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u v
theorem postBoundary {C : Type u} [Category.{v} C] (F : C ⥤ C)
    {U V W Z : C} (delta : U ⟶ F.obj W) (s : U ⟶ F.obj V)
    (t : V ⟶ W) (p : W ⟶ Z) (c : V ⟶ Z)
    (hd : delta = s ≫ F.map t) (hc : t ≫ p = c) :
    delta ≫ F.map p = s ≫ F.map c := by
  rw [hd, Category.assoc, ← F.map_comp, hc]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_EvaluatedAdjacentComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
theorem charTwoNeg (k : Type u) [Field k] [CharP k 2]
    {M : Type*} [AddCommGroup M] [Module k M] (x : M) : -x=x := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← two_smul k, show (2:k)=0 from CharP.cast_eq_zero k 2, zero_smul]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_DimensionOneDetector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v w
variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W]

theorem scalarChart_eq_smul (e : V ≃ₗ[k] k) (x : V) : x = e x • e.symm 1 := by
  apply e.injective
  rw [map_smul, e.apply_symm_apply]
  exact (mul_one _).symm

theorem scalarDetector_injective (e : V ≃ₗ[k] k) (d : V →ₗ[k] W)
    (x : V) (hx : d x ≠ 0) : Function.Injective d := by
  have hg : d (e.symm 1) ≠ 0 := by
    intro hz
    apply hx
    rw [scalarChart_eq_smul e x, map_smul, hz, smul_zero]
  apply (injective_iff_map_eq_zero d).mpr
  intro z hz
  have hs : e z = 0 := by
    have h := hz
    rw [scalarChart_eq_smul e z, map_smul] at h
    by_contra he
    apply hg
    calc
      d (e.symm 1) = (e z)⁻¹ • (e z • d (e.symm 1)) := by
        rw [← mul_smul, inv_mul_cancel₀ he, one_smul]
      _ = 0 := by rw [h, smul_zero]
  exact e.injective (hs.trans (map_zero e).symm)

theorem scalarDetector_common (e : V ≃ₗ[k] k) (d : V →ₗ[k] W)
    (x y : V) (b : W) (hb : b ≠ 0) (hx : d x = b) (hy : d y = b) :
    x = y ∧ x ≠ 0 := by
  have hdx : d x ≠ 0 := hx ▸ hb
  refine ⟨scalarDetector_injective e d x hdx (hx.trans hy.symm), ?_⟩
  intro hz
  exact hdx (hz ▸ map_zero d)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CoverStepFullHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K : CochainComplex C ℤ}
abbrev sourceObject (K : CochainComplex C ℤ) :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K

end ArExplicit

end

end OAI
end


