-- Prove2me | Definitions.Def_OAIQ031A038
-- name    : OAIQ031A038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:02:30.120643+00:00
-- url     : https://prove2.me/theorems/87ebec7c-5841-4c23-b8dd-aef7dbb78936
-- title:
--   Definitions bundle OAIQ031A038 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 11 definitions, 1 inductive type or structure, 2 instances and 13 theorems. The definitions and types are `OAI.ArExplicit.BinaryKoszul.zeroDualPieceScalarEquiv`, `OAI.ArExplicit.BinaryKoszul.zeroPieceScalarEquiv`, `OAI.ArExplicit.Candidate`, `OAI.ArExplicit.ConeCokernel.Middle`, `OAI.ArExplicit.ConeCokernel.inclusion`, `OAI.ArExplicit.ConeCokernel.projection`, `OAI.ArExplicit.ConvertedAlgebra`, `OAI.ArExplicit.TIndex.target`, `OAI.ArExplicit.TwistedBimodule.rightLinearEquiv`, `OAI.ArExplicit.bimoduleEnvelopingRightEquiv`, `OAI.ArExplicit.coneLiftKernelComponent`, `OAI.ArExplicit.coneLiftMiddle`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Basic`, `AuslanderReiten_Cocycles_CocycleCorners`, `AuslanderReiten_Cocycles_RawCocycleProducts`, `AuslanderReiten_Complete_TateKoszul`, `AuslanderReiten_Cones_ConeCokernel`, `AuslanderReiten_Cones_ConeConnectingCoordinates`, `AuslanderReiten_HomComplex_FullHomProductReindex`, `AuslanderReiten_Modules_BimoduleEnveloping`, `AuslanderReiten_Modules_TwistedBimodule`, `AuslanderReiten_Resolutions_BinaryKoszul`, `AuslanderReiten_Resolutions_BinaryKoszulDual`, `AuslanderReiten_Resolutions_BinaryKoszulScalar`, `AuslanderReiten_Triangular_ConvertedStructure`.
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A002`, `OAIQ031A003`, `OAIQ031A004`, `OAIQ031A005`, `OAIQ031A006`, `OAIQ031A007`, `OAIQ031A010`, `OAIQ031A011`, `OAIQ031A012`, `OAIQ031A014`, `OAIQ031A015`, `OAIQ031A016` and `OAIQ031A017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A056`, `OAIQ031A057`, `OAIQ031A058`, `OAIQ031A060` and `OAIQ031A068`; the statement `OAI.ArExplicit.Statement.fullStatement_of_mainConclusions`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A004
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A006
import Definitions.Def_OAIQ031A007
import Definitions.Def_OAIQ031A010
import Definitions.Def_OAIQ031A011
import Definitions.Def_OAIQ031A012
import Definitions.Def_OAIQ031A014
import Definitions.Def_OAIQ031A015
import Definitions.Def_OAIQ031A016
import Definitions.Def_OAIQ031A017

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Basic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ArExplicit

universe u v w

structure Candidate where
  R : Type
  [ring : Ring R]
  [algebra : Algebra BaseField R]
  M : Type
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [baseModule : Module BaseField M]
  [tower : IsScalarTower BaseField R M]

attribute [instance] Candidate.ring Candidate.algebra Candidate.addCommGroup
  Candidate.module Candidate.baseModule Candidate.tower

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCorners
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit
namespace TIndex

def target (i : TIndex) : Bool := if i.1 then lowerSource i.2 else lowerTarget i.2

end TIndex

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeConnectingCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def coneLiftMiddle : H.X 0 →ₗ[R] CochainCokernel G :=
  (LinearMap.range (G.d (-1) 0).hom).mkQ.comp
    ((LinearMap.fst R _ _).comp ((coneTermEquiv φ 0).toLinearMap.comp (κ.f 0).hom))

def coneLiftKernelComponent : H.X (-1) →ₗ[R] CochainCokernel F :=
  (LinearMap.range (F.d (-1) 0).hom).mkQ.comp
    ((LinearMap.snd R _ _).comp ((conePreviousTermEquiv φ).toLinearMap.comp (κ.f (-1)).hom))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_RawCocycleProducts
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

include k in

theorem rawCocycleComponent_comm (x : Cocycle K L n) (a b : ℤ) (hab : a=n+b) :
    x.val.v (-(a+1)) (-(b+1)) (by omega) ≫ L.d (-(b+1)) (-b) =
      K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega) := by
  have hx := congrArg (fun z : Cochain K L (n+1) => z.v (-(a+1)) (-b) (by omega))
    (show δ n (n+1) x.val=0 by simp)
  rw [δ_v _ _ rfl _ _ _ (by omega) (-(b+1)) (-a) (by omega) (by omega),
    ResolutionProducts.intUnit_smul_charTwo (k := k), Cochain.zero_v] at hx
  have hh : (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) +
      (K.d (-(a+1)) (-a) ≫ x.val.v (-a) (-b) (by omega)) = 0 := by
    rw [← two_smul k, show (2 : k)=0 from CharP.cast_eq_zero k 2, zero_smul]
  exact (eq_neg_of_add_eq_zero_left hx).trans (eq_neg_iff_add_eq_zero.mpr hh).symm

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [CommRing k]

theorem mulX_injective (n : ℕ) : Function.Injective (mulX k n) := by
  intro f g h
  ext i
  exact congrFun h i.succ

theorem kernel_row (n : ℕ) (u v : Piece k (n + 1)) (h : row k (n + 1) (u, v) = 0) :
    ∃ w : Piece k n, column k n w = (u, v) := by
  let w : Piece k n := fun i => u i.castSucc
  have hu : u (Fin.last (n + 1)) = 0 := by
    have H := congrFun h (Fin.last (n + 2))
    simpa [row, mulX, mulY] using H
  have hv : v 0 = 0 := by
    have H := congrFun h 0
    simpa [row, mulX, mulY] using H
  have huv (i : Fin (n + 1)) : u i.castSucc + v i.succ = 0 := by
    have H := congrFun h i.castSucc.succ
    simpa [row, mulX, mulY] using H
  refine ⟨w, Prod.ext ?_ ?_⟩
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hu.symm
    · simp [w]
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv.symm
    · change -w j = v j.succ
      exact (eq_neg_of_add_eq_zero_right (huv j)).symm

theorem row_zero_injective : Function.Injective (row k 0) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  have hv : v 0 = v' 0 := by
    have H := congrFun h 0
    simpa [row, mulX, mulY] using H
  have hu : u 0 = u' 0 := by
    have H := congrFun h (Fin.last 1)
    change u 0 + 0 = u' 0 + 0 at H
    simpa using H
  apply Prod.ext
  · funext i
    have hi : i = 0 := Fin.eq_zero i
    simpa [hi] using hu
  · funext i
    have hi : i = 0 := Fin.eq_zero i
    simpa [hi] using hv

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszulDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [Field k]

theorem dualRow_surjective (n : ℕ) : Function.Surjective (dualRow k n) := by
  intro f
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective (mulX_injective k n) f
  refine ⟨(g, 0), ?_⟩
  change (mulX k n).dualMap g + (mulY k n).dualMap 0 = f
  simpa using hg

theorem dualColumn_zero_surjective : Function.Surjective (dualColumn k 0) := by
  rintro ⟨f, g⟩
  let l : Module.Dual k (Piece k 0 × Piece k 0) := (-g).coprod f
  obtain ⟨t, ht⟩ := LinearMap.dualMap_surjective_of_injective (row_zero_injective k) l
  refine ⟨t, Prod.ext ?_ ?_⟩
  · apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun ht (0, x)
    simpa [l, row] using hx
  · apply LinearMap.ext
    intro x
    have hx := congrArg Neg.neg (DFunLike.congr_fun ht (x, 0))
    simpa [l, row] using hx

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

@[simp] theorem row_apply (a : ℤ) (v w : H a) : row (x := x) (y := y) a (v, w) =
    x a v + y a w := rfl

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

variable {R M N E : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup E] [Module R E]

namespace ConeCokernel

variable {Q₀ Q₁ P₀ P₁ P₂ : Type*}
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
variable [AddCommGroup P₂] [Module R P₂]
variable (dQ : Q₁ →ₗ[R] Q₀) (dP : P₁ →ₗ[R] P₀) (f : P₁ →ₗ[R] Q₀)

abbrev Middle := (Q₀ × P₀) ⧸ LinearMap.range (coneBlock dQ dP f)

def inclusion : Left dQ →ₗ[R] Middle dQ dP f :=
  (LinearMap.range dQ).liftQ
    ((LinearMap.range (coneBlock dQ dP f)).mkQ.comp (LinearMap.inl R Q₀ P₀)) (by
      rintro x ⟨a,rfl⟩
      change Submodule.Quotient.mk (dQ a, 0) = (0 : Middle dQ dP f)
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨(a,0), by simp⟩)

def projection : Middle dQ dP f →ₗ[R] Right dP :=
  (LinearMap.range (coneBlock dQ dP f)).liftQ
    ((LinearMap.range dP).mkQ.comp (LinearMap.snd R Q₀ P₀)) (by
      rintro x ⟨⟨a,b⟩,rfl⟩
      change Submodule.Quotient.mk (-dP b) = (0 : Right dP)
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨-b, map_neg dP b⟩)

@[simp] theorem inclusion_mk (x : Q₀) :
    inclusion dQ dP f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x,0) := rfl

@[simp] theorem projection_mk (x : Q₀) (y : P₀) :
    projection dQ dP f (Submodule.Quotient.mk (x,y)) = Submodule.Quotient.mk y := rfl

theorem projection_surjective : Function.Surjective (projection dQ dP f) := by
  intro y
  obtain ⟨y,rfl⟩ := (LinearMap.range dP).mkQ_surjective y
  exact ⟨Submodule.Quotient.mk (0,y), rfl⟩

theorem exact : Function.Exact (inclusion dQ dP f) (projection dQ dP f) := by
  intro z
  obtain ⟨⟨x,y⟩,rfl⟩ := (LinearMap.range (coneBlock dQ dP f)).mkQ_surjective z
  constructor
  · intro h
    have hy : y ∈ LinearMap.range dP := (Submodule.Quotient.mk_eq_zero _).mp h
    obtain ⟨b,hb⟩ := hy
    refine ⟨Submodule.Quotient.mk (x + f b), ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨(0,b), ?_⟩
    simp [coneBlock_apply, hb]
  · rintro ⟨w,hw⟩
    obtain ⟨w,rfl⟩ := (LinearMap.range dQ).mkQ_surjective w
    rw [← hw]
    exact Submodule.Quotient.mk_zero _

theorem inclusion_injective (eP : P₂ →ₗ[R] P₁) (f₁ : P₂ →ₗ[R] Q₁)
    (hex : Function.Exact eP dP) (hc : dQ.comp f₁ = f.comp eP) :
    Function.Injective (inclusion dQ dP f) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨x,rfl⟩ := (LinearMap.range dQ).mkQ_surjective z
  obtain ⟨⟨a,b⟩,hab⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hb : dP b = 0 := neg_eq_zero.mp (congrArg Prod.snd hab)
  obtain ⟨c,hc'⟩ := (hex b).mp hb
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨a + f₁ c, ?_⟩
  rw [map_add, show dQ (f₁ c) = f (eP c) from DFunLike.congr_fun hc c, hc']
  exact congrArg Prod.fst hab

end ConeCokernel
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProductReindex
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u w
variable {k : Type u} [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {a b c d : ℤ}

theorem degreeEquiv_trans_apply {H : ℤ → Type u} [∀ i, AddCommGroup (H i)] [∀ i, Module k (H i)]
    (h₁ : a=b) (h₂ : b=c) (x : H a) :
    TateKoszul.degreeEquiv (k := k) H h₂ (TateKoszul.degreeEquiv (k := k) H h₁ x) =
      TateKoszul.degreeEquiv (k := k) H (h₁.trans h₂) x := by
  subst b
  subst c
  rfl

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def rightLinearEquiv : TwistedBimodule k R σ ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun x := MulOpposite.op (σ.symm x.value)
  invFun x := ⟨σ x.unop⟩
  left_inv x := by ext; exact σ.apply_symm_apply x.value
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' r x := by
    apply MulOpposite.unop_injective
    change σ.symm (x.value * σ r.unop) = σ.symm x.value * r.unop
    simp

instance instProjectiveMulOpposite : Module.Projective Rᵐᵒᵖ (TwistedBimodule k R σ) :=
  Module.Projective.of_equiv (rightLinearEquiv σ).symm

instance instFiniteMulOpposite : Module.Finite Rᵐᵒᵖ (TwistedBimodule k R σ) :=
  Module.Finite.equiv (rightLinearEquiv σ).symm

end TwistedBimodule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_BimoduleEnveloping
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M] [Module Rᵐᵒᵖ M]
variable [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
variable [SMulCommClass k R M] [SMulCommClass k Rᵐᵒᵖ M]
variable [SMulCommClass R Rᵐᵒᵖ M]

def bimoduleEnvelopingRightEquiv :
    ((ModuleCat.restrictScalars (tensorRightInclusion k R Rᵐᵒᵖ)).obj
      (bimoduleEnvelopingObject k R M)) ≃ₗ[Rᵐᵒᵖ] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (1 : R) • (a • (show M from x)) = a • (show M from x)
    rw [one_smul]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszulScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BinaryKoszul
universe u
variable (k : Type u) [Field k]

def zeroPieceScalarEquiv : Piece k 0 ≃ₗ[k] k :=
  LinearEquiv.funUnique (Fin 1) k k

def zeroDualPieceScalarEquiv : DualPiece k 0 ≃ₗ[k] k :=
  (zeroPieceScalarEquiv k).symm.dualMap.trans (LinearMap.ringLmapEquivSelf k k k)

end ArExplicit.BinaryKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_ConvertedStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

abbrev ConvertedAlgebra (k : Type*) [Field k] (q : k) (F : Type*) := Triangular (A k q) F

end ArExplicit

end OAI
end


