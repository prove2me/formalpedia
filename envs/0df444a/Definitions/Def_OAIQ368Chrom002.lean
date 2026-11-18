-- Prove2me | Definitions.Def_OAIQ368Chrom002
-- name    : OAIQ368Chrom002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:01:48.293789+00:00
-- url     : https://prove2.me/theorems/abf5c40d-413f-4476-801e-0183e8d4bf09
-- title:
--   Definitions bundle OAIQ368Chrom002 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 52 declarations of OpenAI's Lean: 24 definitions and 28 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.kernelSupport`, `OAI.ElementaryPositivity.QuantumTorus.mutationIncomingLabel`, `OAI.ElementaryPositivity.QuantumTorus.mutationIncomingLabelEquiv`, `OAI.ElementaryPositivity.QuantumTorus.mutationIncomingLabelInverse`, `OAI.ElementaryPositivity.QuantumTorus.mutationShear`, `OAI.ElementaryPositivity.QuantumTorus.mutationShearEquiv`, `OAI.ElementaryPositivity.QuantumTorus.mutationShearInverse`, `OAI.ElementaryPositivity.QuantumTorus.nonpSupportFrame`, `OAI.ElementaryPositivity.QuantumTorus.orientPowerSeries`, `OAI.ElementaryPositivity.QuantumTorus.pureCutGauge`, `OAI.ElementaryPositivity.QuantumTorus.realMutationCovector`, `OAI.ElementaryPositivity.QuantumTorus.realShearCovector`, `OAI.ElementaryPositivity.QuantumTorus.realShearCovectorInverse`, `OAI.ElementaryPositivity.QuantumTorus.realShearVector`, `OAI.ElementaryPositivity.QuantumTorus.realSideCovector`, `OAI.ElementaryPositivity.QuantumTorus.rootOrder`, `OAI.ElementaryPositivity.QuantumTorus.shearCovector`, `OAI.ElementaryPositivity.RationalFiber.coefficientUnit`, `OAI.ElementaryPositivity.RationalFiber.expandInfinity`, `OAI.ElementaryPositivity.RationalFiber.expandZero`, `OAI.ElementaryPositivity.RationalFiber.innerHom`, `OAI.ElementaryPositivity.RationalFiber.reciprocal`, `OAI.ElementaryPositivity.RationalFiber.reciprocalEval`, `OAI.ElementaryPositivity.RationalFiber.variableUnit`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_KernelTraceLog`, `Chromatic_GradedAlgebra_MutationRootMap`, `Chromatic_GradedAlgebra_RationalLaurentScalars`, `Chromatic_GradedAlgebra_RationalShearCocycle`, `Chromatic_QuantumTorus_GeometricMutation`, `Chromatic_QuantumTorus_MutationConvexSigns`, `Chromatic_QuantumTorus_MutationFiberArithmetic`, `Chromatic_QuantumTorus_PureCutTelescoping`, `Chromatic_Walls_ComparisonLine`, `Chromatic_Walls_FiniteRayGeometry`, `Chromatic_Walls_FiniteRefinementImportAll`, `Chromatic_Walls_GeometricMutationLines`, `Chromatic_Walls_IncomingEquality`, `Chromatic_Walls_MutatedLineCompletion`, `Chromatic_Walls_NonpJoint`, `Chromatic_Walls_RationalFiberReciprocal`, `Chromatic_Walls_RationalFiberScale`, `Chromatic_Walls_WallLineInitial`, `Chromatic_Walls_WallRegrade`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom003`, `OAIQ368Chrom004` and `OAIQ368Chrom022`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ368_CHROM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_KernelTraceLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)

def kernelSupport (r : M) : AddSubmonoid M := (Ω.flip r).ker.toAddSubmonoid

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteRayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (e : M →+ E) (he : Function.Injective e) (C : (I → ℤ) →+ M)
variable (L : Module.Dual ℝ E)

lemma real_line_signs (u w a b : ℝ) (hw : w≠0) (ha : a≠ -u/w) (hb : b≠ -u/w)
    (H : a < -u/w ↔ b < -u/w) :
    (0 < u+a*w → 0 < u+b*w) ∧ (u+a*w=0 → u+b*w=0) ∧ (u+a*w < 0 → u+b*w < 0) := by
  have hz : u+(-u/w)*w=0:=by field_simp <;> ring
  by_cases has : a < -u/w
  · have hbs:=H.mp has
    rcases lt_or_gt_of_ne hw with hw|hw
    · have ha' : 0 < u+a*w:=by nlinarith
      have hb' : 0 < u+b*w:=by nlinarith
      exact ⟨fun _ => hb',fun h => by linarith,fun h => by linarith⟩
    · have ha' : u+a*w < 0:=by nlinarith
      have hb' : u+b*w < 0:=by nlinarith
      exact ⟨fun h => by linarith,fun h => by linarith,fun _ => hb'⟩
  · have hza : -u/w < a:=lt_of_le_of_ne (le_of_not_gt has) (Ne.symm ha)
    have hzb : -u/w < b:=lt_of_le_of_ne (le_of_not_gt (fun hh => has (H.mpr hh))) (Ne.symm hb)
    rcases lt_or_gt_of_ne hw with hw|hw
    · have ha' : u+a*w < 0:=by nlinarith
      have hb' : u+b*w < 0:=by nlinarith
      exact ⟨fun h => by linarith,fun h => by linarith,fun _ => hb'⟩
    · have ha' : 0 < u+a*w:=by nlinarith
      have hb' : 0 < u+b*w:=by nlinarith
      exact ⟨fun _ => hb',fun h => by linarith,fun h => by linarith⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallLineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E)
lemma finite_upper_bound (S : Finset ℝ) : ∃b,0 < b ∧ ∀a∈S,a < b := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,one_pos,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨b,hb,H⟩:=ih
    refine ⟨max b (a+1),lt_of_lt_of_le hb (le_max_left _ _),?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact lt_of_lt_of_le (by linarith : z < z+1) (le_max_right _ _)
    · exact lt_of_lt_of_le (H z hz) (le_max_left _ _)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_NonpJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)

def nonpSupportFrame (w : M →+ ℤ) (h : M →+ ℝ) (P : AddSubmonoid M) (n : ℤ) : AddSubmonoid M where
  carrier:={m | m=0 ∨ (0<w m ∧ ((w m<n ∨ (w m=n ∧ h m=0)) → m∈P))}
  zero_mem':=Or.inl rfl
  add_mem':=by
    intro a b ha hb
    rcases ha with rfl | ⟨ha,haP⟩
    · simpa using hb
    rcases hb with rfl | ⟨hb,hbP⟩
    · exact Or.inr ⟨by simpa using ha,by simpa using haP⟩
    refine Or.inr ⟨by simpa only [map_add] using add_pos ha hb,?_⟩
    intro hs
    have hsum : w a+w b≤n:=by
      rcases hs with hs | ⟨hs,_⟩
      · simpa only [map_add] using le_of_lt hs
      · exact le_of_eq (by simpa only [map_add] using hs)
    exact P.add_mem (haP (Or.inl (by omega))) (hbP (Or.inl (by omega)))

lemma nonpSupportFrame_target {w : M →+ ℤ} {h : M →+ ℝ} {P : AddSubmonoid M} {n : ℤ}
    {m : M} (hm : m∈nonpSupportFrame w h P n) (hw : w m=n) (hh : h m=0) : m∈P := by
  rcases hm with rfl | hm
  · exact P.zero_mem
  · exact hm.2 (Or.inr ⟨hw,hh⟩)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutationFiberArithmetic
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
lemma max_zero_neg (a : ℤ) : max 0 a=max 0 (-a)+a := by
  by_cases ha : 0≤a
  · rw [max_eq_right ha,max_eq_left (by omega)]; omega
  · rw [max_eq_left (by omega),max_eq_right (by omega)]; omega
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalFiberScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open Polynomial
noncomputable section
open scoped LaurentSeries RatFunc
variable {K : Type*} [Field K]

def expandZero : RatFunc K →+* LaurentSeries K := algebraMap _ _
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalFiberReciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
open scoped LaurentSeries RatFunc
variable {K : Type*} [Field K]
lemma reciprocal_transcendental : Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
  intro h
  exact RatFunc.transcendental_X (IsAlgebraic.inv_iff.mp h)
def reciprocalEval : Polynomial K →ₐ[K] RatFunc K :=
  Polynomial.aeval ((RatFunc.X : RatFunc K)⁻¹)
lemma reciprocalEval_injective : Function.Injective (reciprocalEval (K:=K)) :=
  transcendental_iff_injective.mp reciprocal_transcendental
lemma reciprocalEval_regular :
    (nonZeroDivisors (Polynomial K)) ≤ (nonZeroDivisors (RatFunc K)).comap reciprocalEval :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ reciprocalEval_injective
def reciprocal : RatFunc K →+* RatFunc K :=
  RatFunc.liftRingHom reciprocalEval.toRingHom reciprocalEval_regular
@[simp] lemma reciprocal_polynomial (f : Polynomial K) :
    reciprocal (algebraMap (Polynomial K) (RatFunc K) f)=reciprocalEval f :=
  RatFunc.liftRingHom_algebraMap _ _ _
@[simp] lemma reciprocal_X : reciprocal RatFunc.X=(RatFunc.X : RatFunc K)⁻¹ := by
  change reciprocal (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=_
  rw [reciprocal_polynomial]
  simp [reciprocalEval]
@[simp] lemma reciprocal_constant (a : K) : reciprocal (RatFunc.C a)=RatFunc.C a := by
  rw [←RatFunc.algebraMap_C,reciprocal_polynomial]
  simp [reciprocalEval]
def expandInfinity : RatFunc K →+* LaurentSeries K := expandZero.comp reciprocal
@[simp] lemma expandZero_X : expandZero (RatFunc.X : RatFunc K)=HahnSeries.single (1:ℤ) 1 :=
  RatFunc.coe_X
@[simp] lemma expandZero_constant (a : K) : expandZero (RatFunc.C a)=HahnSeries.C a := by
  change algebraMap (RatFunc K) (LaurentSeries K) (RatFunc.C a)=_
  rw [←RatFunc.algebraMap_C,←IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
  simp
@[simp] lemma expandZero_X_zpow (n : ℤ) :
    expandZero ((RatFunc.X : RatFunc K)^n)=HahnSeries.single n 1 := by
  rw [map_zpow₀,expandZero_X,←RatFunc.single_zpow]
@[simp] lemma expandInfinity_X_zpow (n : ℤ) :
    expandInfinity ((RatFunc.X : RatFunc K)^n)=HahnSeries.single (-n) 1 := by
  change expandZero (reciprocal ((RatFunc.X : RatFunc K)^n))=_
  rw [map_zpow₀,reciprocal_X,inv_zpow,←zpow_neg,expandZero_X_zpow]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalShearCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]
def coefficientUnit (v : Kˣ) : (RatFunc K)ˣ := Units.map RatFunc.C.toMonoidHom v
def variableUnit : (RatFunc K)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
@[simp] lemma coefficientUnit_val (v : Kˣ) : (coefficientUnit v:RatFunc K)=RatFunc.C (v:K) := rfl
@[simp] lemma variableUnit_val : (variableUnit (K:=K):RatFunc K)=RatFunc.X := rfl
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationRootMap
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

def mutationShear (p : M) : M →+ M where
  toFun m:=m-(Ω p m) • p
  map_zero':=by simp
  map_add':=by intro a b; simp only [map_add,add_zsmul]; abel

def mutationShearInverse (p : M) : M →+ M where
  toFun m:=m+(Ω p m) • p
  map_zero':=by simp
  map_add':=by intro a b; simp only [map_add,add_zsmul]; abel

lemma mutationShear_left_inverse (p : M) (hp : Ω p p=0) (m : M) :
    mutationShearInverse Ω p (mutationShear Ω p m)=m := by
  change (m-Ω p m • p)+Ω p (m-Ω p m • p) • p=m
  rw [map_sub,map_zsmul,hp,smul_zero,sub_zero,sub_add_cancel]
lemma mutationShear_right_inverse (p : M) (hp : Ω p p=0) (m : M) :
    mutationShear Ω p (mutationShearInverse Ω p m)=m := by
  change (m+Ω p m • p)-Ω p (m+Ω p m • p) • p=m
  rw [map_add,map_zsmul,hp,smul_zero,add_zero,add_sub_cancel_right]

def mutationShearEquiv (p : M) (hp : Ω p p=0) : M ≃+ M where
  toFun:=mutationShear Ω p
  invFun:=mutationShearInverse Ω p
  left_inv:=mutationShear_left_inverse Ω p hp
  right_inv:=mutationShear_right_inverse Ω p hp
  map_add':=(mutationShear Ω p).map_add

lemma mutationShear_pairing (hΩ : ∀m,Ω m m=0) (p a b : M) :
    Ω (mutationShear Ω p a) (mutationShear Ω p b)=Ω a b := by
  have hs : Ω a p= -Ω p a:=by
    have H:=hΩ (a+p)
    simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
    omega
  change Ω (a-Ω p a • p) (b-Ω p b • p)=Ω a b
  simp only [map_sub,map_zsmul,AddMonoidHom.sub_apply,AddMonoidHom.zsmul_apply,
    smul_eq_mul,hΩ,hs]
  ring

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalLaurentScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K : Type*} [Field K]
lemma ratFunc_hom_ext_ring {A : Type*} [Ring A] (f g : RatFunc K →+* A)
    (hpoly : ∀p : Polynomial K,f (algebraMap (Polynomial K) (RatFunc K) p)=
      g (algebraMap (Polynomial K) (RatFunc K) p)) : f=g := by
  apply RingHom.ext
  intro x
  induction x using RatFunc.induction_on with
  | f p q hq=>
    have hu : IsUnit (f (algebraMap (Polynomial K) (RatFunc K) q)):=
      (isUnit_iff_ne_zero.mpr (RatFunc.algebraMap_ne_zero hq)).map f
    apply hu.mul_right_cancel
    rw [←map_mul,div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hq),hpoly p,hpoly q,
      ←map_mul,div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hq)]
def innerHom {A : Type*} [Ring A] (u : Aˣ) : A →+* A where
  toFun a:=(↑u:A)*a*(↑(u⁻¹):A)
  map_zero':=by simp
  map_one':=by simp
  map_add' a b:=by simp [mul_add,add_mul]
  map_mul' a b:=by simp [mul_assoc]
variable {M : Type*} [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0) (p : M)
include hΩ in
lemma pairing_swap (a b : M) : Ω a b= -Ω b a := by
  have H:=hΩ (a+b)
  simp only [map_add,AddMonoidHom.add_apply,hΩ] at H
  omega
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : M) (hp : Ω p p=0)

def shearCovector (h : M →+ ℝ) : M →+ ℝ := h.comp (mutationShearInverse Ω p)

def mutationIncomingLabel (m : M) : M := m+max 0 (-Ω p m) • p
def mutationIncomingLabelInverse (m : M) : M := m-max 0 (-Ω p m) • p
include hp in
lemma mutationIncomingLabel_pairing (m : M) : Ω p (mutationIncomingLabel Ω p m)=Ω p m := by
  change Ω p (m+max 0 (-Ω p m) • p)=Ω p m
  rw [map_add,map_zsmul,hp,smul_zero,add_zero]
include hp in
lemma mutationIncomingLabelInverse_pairing (m : M) : Ω p (mutationIncomingLabelInverse Ω p m)=Ω p m := by
  change Ω p (m-max 0 (-Ω p m) • p)=Ω p m
  rw [map_sub,map_zsmul,hp,smul_zero,sub_zero]
include hp in
lemma mutationIncomingLabel_left_inverse (m : M) :
    mutationIncomingLabelInverse Ω p (mutationIncomingLabel Ω p m)=m := by
  unfold mutationIncomingLabelInverse
  rw [mutationIncomingLabel_pairing Ω p hp]
  exact add_sub_cancel_right m _
include hp in
lemma mutationIncomingLabel_right_inverse (m : M) :
    mutationIncomingLabel Ω p (mutationIncomingLabelInverse Ω p m)=m := by
  unfold mutationIncomingLabel
  rw [mutationIncomingLabelInverse_pairing Ω p hp]
  exact sub_add_cancel m _
def mutationIncomingLabelEquiv : M ≃ M where
  toFun:=mutationIncomingLabel Ω p
  invFun:=mutationIncomingLabelInverse Ω p
  left_inv:=mutationIncomingLabel_left_inverse Ω p hp
  right_inv:=mutationIncomingLabel_right_inverse Ω p hp
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_GeometricMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (Ω : M →+ M →+ ℤ) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)
variable (hS : ∀x,S x x=0) (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))

def realShearCovector (h : Module.Dual ℝ E) : Module.Dual ℝ E := h+(h (e p)) • S (e p)
def realShearCovectorInverse (h : Module.Dual ℝ E) : Module.Dual ℝ E := h-(h (e p)) • S (e p)

def realMutationCovector (h : Module.Dual ℝ E) : Module.Dual ℝ E :=
  if 0≤h (e p) then h else realShearCovector e S p h
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_MutationConvexSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (e : M →+ E) (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)

def realShearVector (x : E) : E := x+S (e p) x • e p
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
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d)
def rootOrder : M →+ ℤ where
  toFun m:=∑i,coord m i
  map_zero':=by simp
  map_add':=by intro a b; simp [Finset.sum_add_distrib]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
lemma sort_filter_subset {A : Type*} [LinearOrder A] (S T : Finset A) (h : S⊆T) :
    (T.sort (· ≥ ·)).filter (fun a=>decide (a∈S))=S.sort (· ≥ ·) := by
  classical
  have Hp : ((T.sort (· ≥ ·)).filter (fun a=>decide (a∈S))).Perm (S.sort (· ≥ ·)):=by
    apply (List.perm_ext_iff_of_nodup ((T.sort_nodup _).filter _) (S.sort_nodup _)).mpr
    intro a
    simp only [List.mem_filter,Finset.mem_sort,decide_eq_true_eq]
    exact ⟨fun ha=>ha.2,fun ha=>⟨h ha,ha⟩⟩
  exact Hp.eq_of_pairwise' (List.Pairwise.filter _ (T.pairwise_sort _)) (S.pairwise_sort _)

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
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
def orientPowerSeries (forward : Bool) (f : PowerSeries A) : PowerSeries A :=
  if forward then f else PowerSeries.invOfUnit f 1
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_PureCutTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {A J:Type*} [Ring A]
def pureCutGauge (f:PowerSeries A) (side:Bool) : PowerSeries A := if side then f else 1
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GeometricMutationLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
variable (Ω : M →+ M →+ ℤ) (e : M →+ E)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (p : M)
variable (hS : ∀x,S x x=0) (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))

def realSideCovector (pos : Bool) (h : Module.Dual ℝ E) : Module.Dual ℝ E :=
  if pos then h else realShearCovector e S p h
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedLineCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
lemma orientPowerSeries_constant (b : Bool) (f : PowerSeries A) (hf : constantCoeff f=1) :
    constantCoeff (orientPowerSeries b f)=1 := by
  cases b
  · simp only [orientPowerSeries,Bool.false_eq_true,ite_false, if_false,constantCoeff_invOfUnit,
      inv_one,Units.val_one]
  · exact hf
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


