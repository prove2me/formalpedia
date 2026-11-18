-- Prove2me | Definitions.Def_OAIQ368Chrom014
-- name    : OAIQ368Chrom014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:12:44.390906+00:00
-- url     : https://prove2.me/theorems/b145638b-d147-4141-9186-5aed7ded6938
-- title:
--   Definitions bundle OAIQ368Chrom014 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 14 definitions and 4 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.nearCutPolynomialSeedsRing`, `OAI.ElementaryPositivity.RationalFiber.cocycleLift`, `OAI.ElementaryPositivity.RationalFiber.completedOppositeInverseAction`, `OAI.ElementaryPositivity.RationalFiber.completedPureUnit`, `OAI.ElementaryPositivity.RationalFiber.finitePureMutationNonUnitalNonAssocSemiring`, `OAI.ElementaryPositivity.RationalFiber.finitePureMutationRing`, `OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorus_2`, `OAI.ElementaryPositivity.RationalFiber.instNonUnitalSemiringTorus_2`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_2`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_4`, `OAI.ElementaryPositivity.RationalFiber.oppositeInverseActionHom`, `OAI.ElementaryPositivity.RationalFiber.oppositeInverseRatio`, `OAI.ElementaryPositivity.RationalFiber.pureLaurentUnit`, `OAI.ElementaryPositivity.RationalFiber.purePower`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_LaurentPureAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/LaurentPureAction.lean), [`Chromatic_GradedAlgebra_RationalShearCocycle`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/RationalShearCocycle.lean), [`Chromatic_QuantumTorus_NearCutPolynomialSeeds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/NearCutPolynomialSeeds.lean), [`Chromatic_Walls_CompletedCutAction`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/CompletedCutAction.lean), [`Chromatic_Walls_CompletedPureComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/CompletedPureComparison.lean), [`Chromatic_Walls_FinitePureMutation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FinitePureMutation.lean), [`Chromatic_Walls_RationalCocycleExt`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/RationalCocycleExt.lean), [`Chromatic_Walls_RationalCutIdentity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/RationalCutIdentity.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom006` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.pure_mutated_inverse_finite`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square` and `OAI.ElementaryPositivity.RationalFiber.finite_refinement_import`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom006

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentPureAction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)
local instance instRingTorus_2 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_r17a36e_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_r17a36e_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_2 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_2 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

def purePower : PowerSeries K →+* HahnSeries ℤ (Torus v Ω) :=
  (laurentRayHom v Ω p (hΩ p)).comp (HahnSeries.ofPowerSeries ℤ K)

def pureLaurentUnit : (HahnSeries ℤ (Torus v Ω))ˣ where
  val:=purePower v Ω hΩ p (shiftedElementary v 0)
  inv:=purePower v Ω hΩ p (shiftedElementary v 0)⁻¹
  val_inv:=by
    rw [←map_mul,PowerSeries.mul_inv_cancel _ (by rw [shiftedElementary_constant]; exact one_ne_zero),map_one]
  inv_val:=by
    rw [←map_mul,PowerSeries.inv_mul_cancel _ (by rw [shiftedElementary_constant]; exact one_ne_zero),map_one]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalShearCocycle
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.pureAction_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]
lemma reciprocalUnit_scaleAction (v : Kˣ) (t : ℤ) (a : (RatFunc K)ˣ) :
    reciprocalUnit (scaleAction v (Multiplicative.ofAdd (-t)) a)=
      scaleAction v (Multiplicative.ofAdd t) (reciprocalUnit a) := by
  apply Units.ext
  simp only [reciprocalUnit_val,scaleAction_val]
  have H:=congrArg (fun f : RatFunc K →+* RatFunc K=>f (a:RatFunc K)) (reciprocal_scale (v^(-2*(-t))))
  dsimp only [RingHom.comp_apply] at H
  rw [←zpow_neg,show -(-2*(-t))= -2*t by ring] at H
  exact H

def oppositeInverseRatio (v : Kˣ) (t : ℤ) : (RatFunc K)ˣ := reciprocalUnit (pureRatio v (-t))⁻¹
@[simp] lemma oppositeInverseRatio_zero (v : Kˣ) : oppositeInverseRatio v 0=1 := by simp [oppositeInverseRatio]
lemma oppositeInverseRatio_add (v : Kˣ) (t u : ℤ) :
    oppositeInverseRatio v (t+u)=
      oppositeInverseRatio v t*scaleAction v (Multiplicative.ofAdd t) (oppositeInverseRatio v u) := by
  simp only [oppositeInverseRatio,neg_add,pureRatio_add,map_mul,reciprocalUnit_scaleAction,
    mul_inv_rev,map_inv]
  exact mul_comm _ _
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCocycleExt
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K] (v : Kˣ)
def cocycleLift (c : ℤ → (RatFunc K)ˣ) (h0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scaleAction v (Multiplicative.ofAdd t) (c u)) :
    Multiplicative ℤ →* PureExtension v where
  toFun t:=⟨c t.toAdd,t⟩
  map_one':=by apply SemidirectProduct.ext; exact h0; rfl
  map_mul' t u:=by apply SemidirectProduct.ext; exact hc _ _; rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCutIdentity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)

variable (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
lemma oppositeInverseRatio_val_add (t u : ℤ) : (oppositeInverseRatio v (t+u):RatFunc K)=
    (oppositeInverseRatio v t:RatFunc K)*scale (v^(-2*t)) (oppositeInverseRatio v u:RatFunc K) := by
  rw [oppositeInverseRatio_add,Units.val_mul,scaleAction_val]
  rfl
def oppositeInverseActionHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(oppositeInverseRatio v t:RatFunc K))
    (by simp) (oppositeInverseRatio_val_add v)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedPureComparison
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance instRingTorus_4 : Ring (Torus v Ω) := Torus.instRing v Ω

local instance instNonUnitalSemiringTorus_4_r17a36e_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_4_r17a36e_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
def completedPureUnit : (PowerSeries (HahnSeries ℤ (Torus v Ω)))ˣ :=
  Units.map (PowerSeries.C (R:=HahnSeries ℤ (Torus v Ω))) (pureLaurentUnit v Ω hΩ p)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedCutAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)

def completedOppositeInverseAction : PowerSeries (FiberTorus v Ω α) ≃+*
    PowerSeries (FiberTorus v Ω α) :=
  (completedPureAction v Ω α).trans (completedShearAction v Ω α)

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FinitePureMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
noncomputable section

variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (k:M →+ ℤ) (p:M) (hp:k p=1)
local instance finitePureMutationRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance finitePureMutationAddCommMonoid_r17a36e_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance finitePureMutationAddGroup_r17a36e_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance finitePureMutationNonUnitalSemiring_r17a36e_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance finitePureMutationNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutPolynomialSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance nearCutPolynomialSeedsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


