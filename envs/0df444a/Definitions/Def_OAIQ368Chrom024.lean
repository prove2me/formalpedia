-- Prove2me | Definitions.Def_OAIQ368Chrom024
-- name    : OAIQ368Chrom024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:19:40.696003+00:00
-- url     : https://prove2.me/theorems/134c2c4f-c17a-469c-b760-1709df8fe27c
-- title:
--   Definitions bundle OAIQ368Chrom024 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 21 definitions and 1 theorem. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.completedOne`, `OAI.ElementaryPositivity.QuantumTorus.completedProduct`, `OAI.ElementaryPositivity.QuantumTorus.laurentRegradeFiniteRing`, `OAI.ElementaryPositivity.QuantumTorus.laurentRegradePureRing`, `OAI.ElementaryPositivity.QuantumTorus.mutatedPureLineProductRing`, `OAI.ElementaryPositivity.QuantumTorus.mutationCompletedPositive`, `OAI.ElementaryPositivity.QuantumTorus.mutationRegradeCompatibilityRing`, `OAI.ElementaryPositivity.QuantumTorus.mutationTorusEquiv`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityLineProductUnit`, `OAI.ElementaryPositivity.RationalFiber.actualInfinityLineUnit`, `OAI.ElementaryPositivity.RationalFiber.infinityLineCutRing`, `OAI.ElementaryPositivity.RationalFiber.infinityLineRing`, `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit`, `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_1`, `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_2`, `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_4`, `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_5`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_12`, `OAI.ElementaryPositivity.RationalFiber.mutatedLineFactorPositive`, `OAI.ElementaryPositivity.RationalFiber.mutatedLineProductPositive`, `OAI.ElementaryPositivity.RationalFiber.mutatedPureLineFiberRing`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_GradedAlgebra_LaurentRegradeFinite`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/LaurentRegradeFinite.lean), [`Chromatic_GradedAlgebra_LaurentRegradePure`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/LaurentRegradePure.lean), [`Chromatic_GradedAlgebra_MutationLaurentTransport`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/MutationLaurentTransport.lean), [`Chromatic_GradedAlgebra_MutationOrientedCompatibility`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/MutationOrientedCompatibility.lean), [`Chromatic_Walls_FiniteFiberInfinity`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FiniteFiberInfinity.lean), [`Chromatic_Walls_InfinityCutCharts`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/InfinityCutCharts.lean), [`Chromatic_Walls_InfinityLine`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/InfinityLine.lean), [`Chromatic_Walls_MutatedPureLine`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/MutatedPureLine.lean), [`Chromatic_Walls_MutationInfinityAlgebra`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/MutationInfinityAlgebra.lean), [`Chromatic_Walls_MutationRegradeCompatibility`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/MutationRegradeCompatibility.lean), [`Chromatic_Walls_SimpleIncomingElement`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/SimpleIncomingElement.lean), [`Chromatic_Walls_WallRegrade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/WallRegrade.lean).
--
--   **Imports.** It imports the bundle `OAIQ368Chrom008` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom008

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRegradeFinite
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B D : ℕ)
local instance laurentRegradeFiniteRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_LaurentRegradePure
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ) (B : ℕ)
variable (p : M) (hδ : δ p=0) (hκ : κ p=1)
local instance laurentRegradePureRing : Ring (Torus v Ω) := Torus.instRing v Ω

local instance laurentRegradePureAddCommMonoid_r557acc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance laurentRegradePureAddGroup_r557acc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
include hδ hκ in
lemma pure_laurentBounded (f : PowerSeries R) :
    LaurentBounded v Ω δ κ B (raySeries v Ω p f) := by
  intro n m hm
  rw [coeff_raySeries] at hm
  have he : m=n • p := by
    by_contra H
    exact hm (Finsupp.single_eq_of_ne H)
  subst m
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one,mul_zero,add_zero]
  exact ⟨le_rfl,Int.natCast_nonneg _,le_rfl⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleIncomingElement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
def completedOne : CompletedPositive v Ω C :=
  ⟨1,by simp,FormalLog.graded_one _ (rootGrade_one v Ω C)⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallRegrade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

variable [Fintype I]

variable {R : Type*} [CommRing R] (v : Rˣ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.wallRegradeRing
local instance wallRegradeAddCommMonoid_r557acc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance wallRegradeAddGroup_r557acc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def mutationCompletedPositive (f : CompletedPositive v Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    CompletedPositive v Ω (mutatedRoots Ω C pc) :=
  ⟨mutationCompletion Ω hΩ C coord pc pos v f.val,
    mutationCompletion_constant Ω hΩ C coord pc pos v f.val f.property.1,
    mutationCompletion_graded Ω hΩ C coord hcoord pc pos v f hf⟩

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationRegradeCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {R M I : Type*} [CommRing R] [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d)
variable (pc : I) (pos : Bool)
local instance mutationRegradeCompatibilityRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationLaurentTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M I : Type*} [Field K] [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (pc : I) (pos : Bool)
local instance instRingTorus_2_r557acc_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_3_r557acc_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_5_r557acc_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def mutationTorusEquiv : Torus v Ω ≃+* Torus v Ω :=
  { Equiv.ofBijective (mutationTorusPush Ω hΩ C pc pos v : Torus v Ω → Torus v Ω)
      ⟨Finsupp.mapDomain_injective (mutationLinearPiece_injective Ω hΩ C pc pos),
       Finsupp.mapDomain_surjective (mutationLinearPiece_surjective Ω hΩ C pc pos)⟩ with
    map_mul' := (mutationTorusPush Ω hΩ C pc pos v).map_mul
    map_add' := (mutationTorusPush Ω hΩ C pc pos v).map_add }

end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance instRingTorusLaurentSeriesRatVUnit : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteFiberInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)
local instance instRingTorusLaurentSeriesRatVUnit_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationOrientedCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)
local instance instRingTorusLaurentSeriesRatVUnit_2 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationInfinityAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M)
local instance instRingTorus_12 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityCutCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance instRingTorusLaurentSeriesRatVUnit_4 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance instRingTorusLaurentSeriesRatVUnit_5 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_InfinityLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance infinityLineRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω

local instance infinityLineAddCommMonoid_r557acc_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance infinityLineAddGroup_r557acc_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def mutatedLineFactorPositive (a : ℝ) : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a,
    mutatedLineFactor_constant Ω hΩ C coord pc e he L hdeg v k H a,
    mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a⟩

def actualInfinityLineUnit (a : ℝ) : (PowerSeries (HahnSeries ℤ (Torus LaurentRay.vUnit Ω)))ˣ :=
  infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit
    (mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)

end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance infinityLineCutRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedPureLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RationalFiber
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (v : (LaurentSeries ℚ)ˣ)
local instance mutatedPureLineProductRing : Ring (Torus v Ω) := Torus.instRing v Ω

def completedProduct (l : List (CompletedPositive v Ω C)) : CompletedPositive v Ω C :=
  l.foldr (completedMul v Ω C) (completedOne v Ω C)

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance mutatedPureLineFiberRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω

local instance mutatedPureLineFiberAddCommMonoid_r557acc_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPureLineFiberAddGroup_r557acc_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def actualInfinityLineProductUnit (lo hi : ℝ) (N : ℕ) :
    (PowerSeries (HahnSeries ℤ (Torus LaurentRay.vUnit Ω)))ˣ :=
  ((intervalEventList C e v k lo hi N).map
    (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H)).prod

def mutatedLineProductPositive (lo hi : ℝ) (N : ℕ) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N,
    mutatedLineProduct_constant Ω hΩ C coord pc e he L hdeg v k H lo hi N,
    mutatedLineProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N⟩

end
end ElementaryPositivity.RationalFiber

end

end OAI
end


