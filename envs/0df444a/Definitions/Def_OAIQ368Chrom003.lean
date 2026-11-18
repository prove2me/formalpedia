-- Prove2me | Definitions.Def_OAIQ368Chrom003
-- name    : OAIQ368Chrom003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:05:20.125859+00:00
-- url     : https://prove2.me/theorems/7b9c940e-824b-4021-b139-be7ca3e54a2e
-- title:
--   Definitions bundle OAIQ368Chrom003 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 3 definitions and 14 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.mutationLinearPiece`, `OAI.ElementaryPositivity.QuantumTorus.mutationNewOrder`, `OAI.ElementaryPositivity.QuantumTorus.mutationPieceEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: [`Chromatic_QuantumTorus_MutationFiberArithmetic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/MutationFiberArithmetic.lean), [`Chromatic_Walls_FiniteRayGeometry`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FiniteRayGeometry.lean), [`Chromatic_Walls_FiniteRefinementImportAll`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/FiniteRefinementImportAll.lean), [`Chromatic_Walls_SimpleAdjointFiber`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/SimpleAdjointFiber.lean), [`Chromatic_Walls_WallRegrade`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/WallRegrade.lean).
--
--   **Imports.** It imports the bundles `OAIQ368Chrom001` and `OAIQ368Chrom002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom006`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001
import Definitions.Def_OAIQ368Chrom002

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (e : M →+ E) (he : Function.Injective e) (C : (I → ℤ) →+ M)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
lemma line_cell_signs (S : Finset E) (v h : Module.Dual ℝ E) (a b : ℝ)
    (ha : a∉lineEvents S v h) (hb : b∉lineEvents S v h)
    (H : ∀z∈lineEvents S v h,a < z ↔ b < z) (s : E) (hs : s∈S) :
    (0 < (h+a • v) s → 0 < (h+b • v) s) ∧
    ((h+a • v) s=0 → (h+b • v) s=0) ∧ ((h+a • v) s < 0 → (h+b • v) s < 0) := by
  classical
  by_cases hw : v s=0
  · simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hw,mul_zero,add_zero]
    exact ⟨id,id,id⟩
  · have hz : -h s/v s∈lineEvents S v h:=Finset.mem_image.mpr
      ⟨s,Finset.mem_filter.mpr ⟨hs,hw⟩,rfl⟩
    exact real_line_signs (h s) (v s) a b hw (fun he => ha (he ▸ hz))
      (fun he => hb (he ▸ hz)) (H _ hz)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutationFiberArithmetic
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
lemma fiberUpper_flip (α : I → ℤ) (σ : ℤ) (m : M) :
    fiberUpper coord pc α (-σ) m=fiberUpper coord pc α σ m+
      σ*(∑i∈Finset.univ.erase pc,α i*coord m i) := by
  change (∑i∈Finset.univ.erase pc,max 0 (-(-σ)*α i)*coord m i)=
    (∑i∈Finset.univ.erase pc,max 0 (-σ*α i)*coord m i)+σ*(∑i∈Finset.univ.erase pc,α i*coord m i)
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [neg_neg,max_zero_neg]
  have he : -(σ*α i)= -σ*α i:=by ring
  rw [he]
  ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_SimpleAdjointFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)

def mutationLinearPiece (pos : Bool) : M →+ M :=
  if pos then AddMonoidHom.id M else mutationShear Ω (simpleRoot C pc)

omit [Fintype I] in
include hcoord in
lemma mutationLinearPiece_coordinates (pos : Bool) (m : M) :
    coord (mutationLinearPiece Ω C pc pos m)=
      if pos then coord m else coord m-Ω (simpleRoot C pc) m • Pi.single pc 1 := by
  cases pos
  · simp only [mutationLinearPiece,Bool.false_eq_true,ite_false, if_false,mutationShear,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_sub,map_zsmul]
    congr 1
    change _ • coord (C (Pi.single pc 1))=_
    rw [hcoord]
  · rfl

include hcoord in
lemma mutatedCoordinate_off (pos : Bool) (m : M) (i : I) (hi : i≠pc) :
    mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) i=coord m i := by
  change mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (coord (mutationLinearPiece Ω C pc pos m)) i=_
  rw [mutatedCoefficientMap_off pc _ _ i hi,mutationLinearPiece_coordinates Ω C coord hcoord]
  cases pos <;> simp [hi]

include hcoord in
lemma mutated_nonpDegree (pos : Bool) (m : M) :
    nonpDegree (mutatedCoordinates Ω C coord pc) pc (mutationLinearPiece Ω C pc pos m)=
      nonpDegree coord pc m := by
  change (∑i∈Finset.univ.erase pc,mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m) i)=_
  apply Finset.sum_congr rfl
  intro i hi
  exact mutatedCoordinate_off Ω C coord hcoord pc pos m i (Finset.mem_erase.mp hi).1

include hcoord in
lemma mutationLinearPiece_span {n : ℕ} {m : M} (hm : HasRootDegree C n m) (pos : Bool) :
    C (coord (mutationLinearPiece Ω C pc pos m))=mutationLinearPiece Ω C pc pos m := by
  have hc : C (coord m)=m:=by
    obtain ⟨d,hd,hcd,hem⟩:=root_coordinates C coord hcoord hm
    rw [←hem,hcoord]
  rw [mutationLinearPiece_coordinates Ω C coord hcoord]
  cases pos
  · simp only [Bool.false_eq_true,ite_false, if_false,map_sub,map_zsmul,hc,mutationLinearPiece,mutationShear,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk,simpleRoot]
  · exact hc

include hcoord in
lemma mutated_span {n : ℕ} {m : M} (hm : HasRootDegree C n m) (pos : Bool) :
    mutatedRoots Ω C pc (mutatedCoordinates Ω C coord pc (mutationLinearPiece Ω C pc pos m))=
      mutationLinearPiece Ω C pc pos m := by
  change C (mutatedCoefficientMap pc (mutationPairing Ω C pc)
    (mutatedCoefficientMap pc (mutationPairing Ω C pc) (coord (mutationLinearPiece Ω C pc pos m))))=_
  rw [mutatedCoefficientMap_involutive]
  exact mutationLinearPiece_span Ω C coord hcoord pc hm pos

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
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d)
omit [DecidableEq I] in
include hcoord in
lemma rootOrder_eq {n : ℕ} {m : M} (hm : HasRootDegree C n m) : rootOrder coord m=(n:ℤ) := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  change (∑i,coord m i)=(n:ℤ)
  simp only [hc,←Nat.cast_sum,hd]

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

def mutationPieceEquiv : M ≃+ M :=
  if pos then AddEquiv.refl M else mutationShearEquiv Ω (simpleRoot C pc) (hΩ _)
lemma mutationPieceEquiv_apply (m : M) :
    mutationPieceEquiv Ω hΩ C pc pos m=mutationLinearPiece Ω C pc pos m := by
  cases pos <;> rfl
include hΩ in
lemma mutationLinearPiece_pairing (a b : M) :
    Ω (mutationLinearPiece Ω C pc pos a) (mutationLinearPiece Ω C pc pos b)=Ω a b := by
  cases pos
  · exact mutationShear_pairing Ω hΩ _ a b
  · rfl
include hΩ in
lemma mutationLinearPiece_injective : Function.Injective (mutationLinearPiece Ω C pc pos) := by
  intro a b hab
  apply (mutationPieceEquiv Ω hΩ C pc pos).injective
  simpa only [mutationPieceEquiv_apply] using hab
include hΩ in
lemma mutationLinearPiece_surjective : Function.Surjective (mutationLinearPiece Ω C pc pos) := by
  intro m
  refine ⟨(mutationPieceEquiv Ω hΩ C pc pos).symm m,?_⟩
  rw [←mutationPieceEquiv_apply Ω hΩ C pc pos,AddEquiv.apply_symm_apply]

variable [Fintype I]

def mutationNewOrder : M →+ ℤ :=
  (rootOrder (mutatedCoordinates Ω C coord pc)).comp (mutationLinearPiece Ω C pc pos)

include hcoord in
lemma mutationNewOrder_of_root {n : ℕ} {m : M}
    (hm : HasRootDegree (mutatedRoots Ω C pc) n (mutationLinearPiece Ω C pc pos m)) :
    mutationNewOrder Ω C coord pc pos m=(n:ℤ) :=
  rootOrder_eq (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc)
    (mutatedCoordinates_retraction Ω C coord hcoord pc) hm

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRefinementImportAll
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {A : Type*} [Ring A]
lemma orientPowerSeries_trivial (forward : Bool) (f : PowerSeries A) (N : ℕ)
    (hf : ∀n≤N,coeff n f=coeff n 1) :
    ∀n≤N,coeff n (orientPowerSeries forward f)=coeff n 1 := by
  cases forward
  · have hi : PowerSeries.invOfUnit (1 : PowerSeries A) 1=1 := by
      simpa only [mul_one] using (PowerSeries.invOfUnit_mul (1 : PowerSeries A) 1 (by simp))
    simpa only [orientPowerSeries,Bool.false_eq_true,ite_false, if_false,hi] using
      PowerSeriesAdjoint.inverse_coeff_congr f 1 N hf
  · exact hf

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


