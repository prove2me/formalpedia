-- Prove2me | Definitions.Def_OAIQ031A040
-- name    : OAIQ031A040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:01:25.495056+00:00
-- url     : https://prove2.me/theorems/d0b02b41-74f3-4d20-ac02-8d0993597e49
-- title:
--   Definitions bundle OAIQ031A040 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 10 definitions, 6 instances and 13 theorems. The definitions and types are `OAI.ArExplicit.H₁`, `OAI.ArExplicit.H₂`, `OAI.ArExplicit.ResolutionProducts.mapResolutionNatHom`, `OAI.ArExplicit.TriangleGradedSequence.connecting`, `OAI.ArExplicit.TriangleGradedSequence.first`, `OAI.ArExplicit.TwistedBimodule.untwistBilinear`, `OAI.ArExplicit.TwistedLeftModule.scalarEquiv`, `OAI.ArExplicit.basedIteration`, `OAI.ArExplicit.coverCubic`, `OAI.ArExplicit.resolutionCokernelEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_TSimpleTwist`, `AuslanderReiten_Bar_ModuleBarTwistCocycle`, `AuslanderReiten_Cones_TwoCone`, `AuslanderReiten_Coordinates_CubicShiftNaturality`, `AuslanderReiten_Coordinates_IteratedCubicCoordinates`, `AuslanderReiten_Duality_RightDual`, `AuslanderReiten_Ext_ExactFunctorExtNaturality`, `AuslanderReiten_Homology_TriangleGradedSequence`, `AuslanderReiten_Modules_TwistedBimodule`, `AuslanderReiten_Parameters`, `AuslanderReiten_Resolutions_ResolutionCokernel`, `AuslanderReiten_Resolutions_ResolutionCoverExt`, `AuslanderReiten_Resolutions_ResolutionExtSquare`, `AuslanderReiten_Tensor_TwistedTensor`.
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A002`, `OAIQ031A005`, `OAIQ031A007`, `OAIQ031A009`, `OAIQ031A014`, `OAIQ031A016`, `OAIQ031A018`, `OAIQ031A019` and `OAIQ031A020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A057`, `OAIQ031A058`, `OAIQ031A059`, `OAIQ031A060` and `OAIQ031A088`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A007
import Definitions.Def_OAIQ031A009
import Definitions.Def_OAIQ031A014
import Definitions.Def_OAIQ031A016
import Definitions.Def_OAIQ031A018
import Definitions.Def_OAIQ031A019
import Definitions.Def_OAIQ031A020

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Parameters
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

noncomputable abbrev H₁ : BaseField := parameter 1
noncomputable abbrev H₂ : BaseField := parameter 2

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TSimpleTwist
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

theorem twist_smul_simple (H : kˣ) (a : T k q) (s : Resolution.Simple q) :
    TrivialExtension.twist H a • s = a • s := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistCocycle
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] (q : k) (H : kˣ)

theorem inverseTwist_simple_compatible (a : T k q) (m : Resolution.Simple q) :
    (LinearEquiv.refl k (Resolution.Simple q)) (a • m) =
      (TrivialExtension.twist H).symm a • (LinearEquiv.refl k (Resolution.Simple q)) m := rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem term_finite (hf : ∀ n, Module.Finite R (D.term n)) (n : ℕ) :
    Module.Finite R (term D n) := by
  let := hf n
  let := hf (n+2)
  let := hf (n+4)
  exact inferInstanceAs (Module.Finite R
    ((D.term n × D.term (n+2)) × (D.term (n+2) × D.term (n+4))))

theorem term_projective (hp : ∀ n, Module.Projective R (D.term n)) (n : ℕ) :
    Module.Projective R (term D n) := by
  let := hp n
  let := hp (n+2)
  let := hp (n+4)
  exact inferInstanceAs (Module.Projective R
    ((D.term n × D.term (n+2)) × (D.term (n+2) × D.term (n+4))))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_IteratedCubicCoordinates
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)

variable {X : C} (u : X ≅ Y 0)

def basedIteration (n : ℕ) : X ≅ (Y n)⟦(n:ℤ)⟧ := u ≪≫ iteratedShiftIso Y s n

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_CubicShiftNaturality
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)
variable {X S : C} (u : X ≅ Y 0) (c : ∀ n, Y (n+3) ⟶ Y n)

def coverCubic : X ⟶ X⟦(3 : ℤ)⟧ :=
  (basedIteration Y s u 3).hom ≫ (c 0 ≫ u.inv)⟦(3 : ℤ)⟧'

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_RightDual
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

namespace RightDual
variable {k R V W U : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup V] [Module k V] [Module Rᵐᵒᵖ V] [IsScalarTower k Rᵐᵒᵖ V]
variable [AddCommGroup W] [Module k W] [Module Rᵐᵒᵖ W] [IsScalarTower k Rᵐᵒᵖ W]
variable [AddCommGroup U] [Module k U] [Module Rᵐᵒᵖ U] [IsScalarTower k Rᵐᵒᵖ U]

instance instIsScalarTower : IsScalarTower k R (RightDual k R V) where
  smul_assoc a r φ := by ext v; simp [MulOpposite.op_smul, smul_assoc]
instance instSMulCommClass : SMulCommClass k R (RightDual k R V) where
  smul_comm a r φ := by ext v; rfl

end RightDual

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExactFunctorExtNaturality
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesProjectiveObjects]
variable (η : F ⟶ G) {X Y : C} (P : ProjectiveResolution X)

def mapResolutionNatHom : ProjectiveResolution.Hom (mapResolution F P)
    (mapResolution G P) (η.app X) where
  hom := (η.mapHomologicalComplex (.down ℕ)).app P.complex
  hom_f_zero_comp_π_f_zero := by
    rw [mapResolution_π_zero, mapResolution_π_zero, ChainComplex.single₀_map_f_zero]
    exact (η.naturality (P.π.f 0)).symm

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleGradedSequence
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def first (n : ℤ) : Bottom T X n →ₗ[k] Middle T X n :=
  Linear.rightComp k X (T⟦n⟧).mor₁

def connecting (n : ℤ) : Top T X n →ₗ[k] Bottom T X (n + 1) :=
  Linear.rightComp k X ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁)

variable (hT : T ∈ distTriang C)
include hT

theorem exact_middle (n : ℤ) :
    LinearMap.range (first k T X n) = LinearMap.ker (second k T X n) :=
  shiftedTriangleHom_middle_exact k T hT X n

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedBimodule
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

instance instSMulCommClass : SMulCommClass k R (TwistedBimodule k R σ) where
  smul_comm c r x := by ext; exact (mul_smul_comm c r x.value).symm

end TwistedBimodule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionCokernel
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [Ring R] {M : ModuleCat.{u} R}
variable (P : ProjectiveResolution M)

def resolutionCokernelEquiv :
    (P.complex.X 0 ⧸ LinearMap.range (P.complex.d 1 0).hom) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ (resolution_range_eq_ker P)).trans
    ((P.π.f 0).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtSquare
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
section General
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {X X' Y Y' : C} (P : ProjectiveResolution X) (Q : ProjectiveResolution X')

theorem selfExtIso_eq_of_square {k : Type v} [CommRing k] [Linear k C]
    (e : X ≅ X') {n : ℕ} (x : Ext X X n) (y : Ext X' X' n)
    (h : (Ext.mk₀ e.hom).comp y (zero_add _) = x.comp (Ext.mk₀ e.hom) (add_zero _)) :
    selfExtIso (k := k) e n x = y := by
  rw [selfExtIso_apply, Ext.comp_assoc_of_third_deg_zero, ← h,
    Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
end General

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionCoverExt
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {k : Type v} [CommRing k] [Linear k C]
variable {B S N : C} (P : ProjectiveResolution B) (Q : ProjectiveResolution N)

theorem resolutionExt_cover_conjugate (e : B ≅ S) (j : S ≅ N)
    (φ : ProjectiveResolution.Hom P Q (e.hom ≫ j.hom)) (n : ℕ)
    (f : P.complex.X n ⟶ S) (g : Q.complex.X n ⟶ N)
    (hf : P.complex.d (n+1) n ≫ f = 0) (hg : Q.complex.d (n+1) n ≫ g = 0)
    (h : φ.hom.f n ≫ g = f ≫ j.hom) :
    selfExtIso (k := k) j n ((Ext.mk₀ e.inv).comp
      (P.extMk f (n+1) rfl hf) (zero_add _)) = Q.extMk g (n+1) rfl hg := by
  apply selfExtIso_eq_of_square
  have he := resolutionExt_square P Q (e.hom ≫ j.hom) j.hom φ n f g hf hg h
  have hh := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add n)) he
  rw [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_assoc] at hh
  simpa only [Ext.comp_assoc_of_third_deg_zero] using hh

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

instance instModule : Module k (TwistedLeftModule k R σ M) := (coordinates σ).addEquiv.module k
instance instSMul : SMul R (TwistedLeftModule k R σ M) := ⟨fun r x => ⟨σ.symm r • x.value⟩⟩

omit [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_zero : (0 : TwistedLeftModule k R σ M).value = 0 := rfl
omit [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_add (x y : TwistedLeftModule k R σ M) :
    (x + y).value = x.value + y.value := rfl
omit [Module R M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_scalar_smul (a : k) (x : TwistedLeftModule k R σ M) :
    (a • x).value = a • x.value := rfl
omit [Module k M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_smul (r : R) (x : TwistedLeftModule k R σ M) :
    (r • x).value = σ.symm r • x.value := rfl

instance instModule_1 : Module R (TwistedLeftModule k R σ M) where
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [mul_smul]
  smul_zero r := by ext; simp
  smul_add r x y := by ext; simp [smul_add]
  add_smul r s x := by ext; simp [add_smul]
  zero_smul x := by ext; simp

def scalarEquiv : TwistedLeftModule k R σ M ≃ₗ[k] M where
  __ := coordinates σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TwistedLeftModule

namespace TwistedBimodule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

def untwistBilinear : TwistedBimodule k R σ →ₗ[k] M →ₗ[k] TwistedLeftModule k R σ M where
  toFun f :=
    { toFun := fun m => ⟨σ.symm f.value • m⟩
      map_add' x y := by ext; exact smul_add _ _ _
      map_smul' a x := by ext; exact (smul_comm a (σ.symm f.value) x).symm }
  map_add' f g := by ext m; simp [add_smul]
  map_smul' a f := by ext m; simp [smul_assoc]

theorem untwist_balanced (f : TwistedBimodule k R σ) (r : R) (m : M) :
    untwistBilinear σ (MulOpposite.op r • f) m = untwistBilinear σ f (r • m) := by
  apply TwistedLeftModule.ext
  change σ.symm (f.value * σ r) • m = σ.symm f.value • (r • m)
  simp [mul_smul]

theorem untwist_left (r : R) (f : TwistedBimodule k R σ) (m : M) :
    untwistBilinear σ (r • f) m = r • untwistBilinear σ f m := by
  apply TwistedLeftModule.ext
  change σ.symm (r * f.value) • m = σ.symm r • (σ.symm f.value • m)
  simp [mul_smul]

end TwistedBimodule
end ArExplicit

end OAI
end


