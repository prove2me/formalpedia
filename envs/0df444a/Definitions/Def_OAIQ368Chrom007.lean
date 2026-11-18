-- Prove2me | Definitions.Def_OAIQ368Chrom007
-- name    : OAIQ368Chrom007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:12:41.407902+00:00
-- url     : https://prove2.me/theorems/fd29242e-8745-43cf-9d41-d434385ed435
-- title:
--   Definitions bundle OAIQ368Chrom007 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 58 declarations of OpenAI's Lean: 8 definitions and 50 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.instAddCommMonoidSubtypeTorusMemSubalgebraRatSupportedSubalgebra`, `OAI.ElementaryPositivity.QuantumTorus.instModuleRatSubtypeTorusMemSubalgebraSupportedSubalgebra`, `OAI.ElementaryPositivity.QuantumTorus.intervalEventList`, `OAI.ElementaryPositivity.QuantumTorus.intervalLineEvents`, `OAI.ElementaryPositivity.QuantumTorus.rayUnit`, `OAI.ElementaryPositivity.QuantumTorus.rootTrace`, `OAI.ElementaryPositivity.QuantumTorus.supportLift`, `OAI.ElementaryPositivity.QuantumTorus.supportedSubalgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_CompleteUnit`, `Chromatic_GradedAlgebra_KernelTraceLog`, `Chromatic_GradedAlgebra_MutationDegreeBound`, `Chromatic_GradedAlgebra_SimpleBinomial`, `Chromatic_Walls_ComparisonLine`, `Chromatic_Walls_FiniteElementaryAdjoint`, `Chromatic_Walls_GenericLineJoining`, `Chromatic_Walls_HNTorusFactor`, `Chromatic_Walls_IncomingDisplacement`, `Chromatic_Walls_IncomingRayElement`, `Chromatic_Walls_QuantumTorusRaySeries`, `Chromatic_Walls_RayIncomingIdentification`, `Chromatic_Walls_RayLaurentExpansion`, `Chromatic_Walls_WallLineInitial`, `Chromatic_Walls_WallUnits`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ368Chrom008`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint`, `OAI.ElementaryPositivity.QuantumTorus.section_line_program`, `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction`, `OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure` and `OAI.ElementaryPositivity.RawShuffle.literalInput_primitiveFactor`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom006

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries

section Field
variable {K : Type*} [Field K]

theorem elementary_tail (q u : K) (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) :
    elementary q u = (1 + PowerSeries.C u * PowerSeries.X) *
      PowerSeries.rescale q (elementary q u) := by
  ext n
  cases n with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff, map_mul, map_add, constantCoeff_one,
      constantCoeff_C, constantCoeff_X, mul_zero, add_zero, one_mul]
    rw [constant_elementary, ← coeff_zero_eq_constantCoeff, coeff_rescale]
    simp [elementaryCoeff]
  | succ n =>
    rw [add_mul, one_mul, map_add]
    simp only [coeff_elementary, coeff_rescale]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_rescale, coeff_elementary, elementaryCoeff]
    field_simp [hq n]
    ring

@[simp] theorem rescale_C (a u : K) :
    PowerSeries.rescale a (PowerSeries.C u) = PowerSeries.C u := by
  ext n
  cases n <;> simp

theorem elementary_head (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) :
    PowerSeries.rescale q⁻¹ (elementary q u) =
      (1 + PowerSeries.C (u * q⁻¹) * PowerSeries.X) * elementary q u := by
  have h := congrArg (PowerSeries.rescale q⁻¹) (elementary_tail q u hq)
  simp only [map_mul, map_add, map_one, rescale_C, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale, mul_inv_cancel₀ hq0, PowerSeries.rescale_one,
    RingHom.id_apply] at h
  rw [← mul_assoc (PowerSeries.C u), ← map_mul] at h
  exact h

theorem elementary_shift (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) (t : ℕ) :
    PowerSeries.rescale (q⁻¹ ^ t) (elementary q u) =
      (∏ i ∈ Finset.range t,
        (1 + PowerSeries.C (u * q⁻¹ ^ (i + 1)) * PowerSeries.X)) *
      elementary q u := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← PowerSeries.rescale_rescale, elementary_head q u hq0 hq]
    simp only [map_mul, map_add, map_one, rescale_C, PowerSeries.rescale_X]
    rw [ih]
    rw [Finset.prod_range_succ]
    simp only [pow_succ', map_mul]
    ring

theorem elementary_ratio (q u : K) (hq0 : q ≠ 0)
    (hq : ∀ n : ℕ, 1 - q ^ (n + 1) ≠ 0) (t : ℕ) :
    PowerSeries.rescale (q⁻¹ ^ t) (elementary q u) * (elementary q u)⁻¹ =
      ∏ i ∈ Finset.range t,
        (1 + PowerSeries.C (u * q⁻¹ ^ (i + 1)) * PowerSeries.X) := by
  rw [elementary_shift q u hq0 hq t, mul_assoc,
    PowerSeries.mul_inv_cancel _ (by simp), mul_one]

end Field

namespace RationalRay

theorem degree_pow (x : RatFunc ℚ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).intDegree = n * x.intDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hx) hx, ih]
    push_cast
    ring

theorem q_nonzero : q ≠ 0 := zpow_ne_zero _ v_nonzero

theorem q_degree : q.intDegree = -2 := by
  change (v ^ (-(2 : ℕ) : ℤ)).intDegree = -2
  rw [zpow_neg, zpow_natCast, RatFunc.intDegree_inv, degree_pow v v_nonzero]
  simp [v]

theorem q_not_root_unity (n : ℕ) : 1 - q ^ (n + 1) ≠ 0 := by
  intro h
  have heq := congrArg RatFunc.intDegree (sub_eq_zero.mp h)
  rw [RatFunc.intDegree_one, degree_pow q q_nonzero, q_degree] at heq
  omega

theorem q_pow (n : ℕ) : q ^ n = v ^ (-2 * (n : ℤ)) := by
  rw [q, ← zpow_natCast, ← zpow_mul]

end RationalRay

end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RayLaurentExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.WallUnits
open PowerSeries
open scoped LaurentSeries RatFunc
noncomputable section
namespace LaurentRay

lemma atInfinity_injective : Function.Injective atInfinity := atInfinity.injective

end LaurentRay
end
end ElementaryPositivity.WallUnits
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_CompleteUnit
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.UnitSelections
open WallUnits PowerSeries
open scoped LaurentSeries
noncomputable section

lemma laurent_q_not_root (n : ℕ) : 1-(HahnSeries.single (2:ℤ) (1:ℚ))^(n+1)≠0 := by
  intro h
  have hh : LaurentRay.atInfinity (1-RationalRay.q^(n+1))=LaurentRay.atInfinity 0 := by
    rw [map_sub,map_one,map_pow,LaurentRay.atInfinity_q,map_zero]
    exact h
  exact RationalRay.q_not_root_unity n (LaurentRay.atInfinity_injective hh)

end
end ElementaryPositivity.UnitSelections
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_KernelTraceLog
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FormalLog
noncomputable section
variable {R M : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M→+M→+ℤ)

def supportedSubalgebra (V : AddSubmonoid M) : Subalgebra ℚ (Torus v Ω) where
  toSubsemiring:=(supportedSubring v Ω V).toSubsemiring
  algebraMap_mem' a:=by
    intro m hm
    rw [Algebra.algebraMap_eq_smul_one,Torus.scalar_one]
    change (Finsupp.single 0 (a • (1:R))) m=0
    exact Finsupp.single_eq_of_ne (fun he=>hm (he ▸ V.zero_mem))

local instance instAddCommMonoidSubtypeTorusMemSubalgebraRatSupportedSubalgebra (support : AddSubmonoid M) : AddCommMonoid (supportedSubalgebra v Ω support) :=
  (inferInstance : Ring (supportedSubalgebra v Ω support)).toAddCommMonoid
local instance instModuleRatSubtypeTorusMemSubalgebraSupportedSubalgebra (support : AddSubmonoid M) : Module ℚ (supportedSubalgebra v Ω support) :=
  Algebra.toModule (R:=ℚ) (A:=supportedSubalgebra v Ω support)

def rootTrace (r : M) : supportedSubalgebra v Ω (kernelSupport Ω r)→ₗ[ℚ] R where
  toFun f:=(f:Torus v Ω) r
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

lemma rootTrace_cyclic (hΩ : ∀m,Ω m m=0) (r : M)
    (f g : supportedSubalgebra v Ω (kernelSupport Ω r)) :
    rootTrace v Ω r (f*g)=rootTrace v Ω r (g*f) := by
  apply coefficient_trace v Ω hΩ r f.val g.val
  intro m hm
  exact f.property m (by simpa [kernelSupport] using hm)

variable (V : AddSubmonoid M)
def supportLift (F : PowerSeries (Torus v Ω))
    (hF : ∀n,coeff n F∈supportedSubalgebra v Ω V) :
    PowerSeries (supportedSubalgebra v Ω V) :=
  PowerSeries.mk (fun n=>⟨coeff n F,hF n⟩)

lemma supportLift_map (F : PowerSeries (Torus v Ω))
    (hF : ∀n,coeff n F∈supportedSubalgebra v Ω V) :
    PowerSeries.map (supportedSubalgebra v Ω V).val.toRingHom (supportLift v Ω V F hF)=F := by
  ext n
  simp only [coeff_map,supportLift,coeff_mk]
  rfl

lemma supportLift_constant (F : PowerSeries (Torus v Ω))
    (hF : ∀n,coeff n F∈supportedSubalgebra v Ω V) (hf : constantCoeff F=1) :
    constantCoeff (supportLift v Ω V F hF)=1 := by
  apply Subtype.ext
  change coeff 0 F=1
  rw [coeff_zero_eq_constantCoeff,hf]

lemma kernel_trace_log_product (hΩ : ∀m,Ω m m=0) (r : M)
    (F G : PowerSeries (Torus v Ω)) (hF : constantCoeff F=1) (hG : constantCoeff G=1)
    (hsF : ∀n,coeff n F∈supportedSubalgebra v Ω (kernelSupport Ω r))
    (hsG : ∀n,coeff n G∈supportedSubalgebra v Ω (kernelSupport Ω r)) (n : ℕ) :
    coeff n (FormalLog.log (F*G)) r=
      coeff n (FormalLog.log F) r+coeff n (FormalLog.log G) r := by
  let V:=kernelSupport Ω r
  let A:=supportLift v Ω V F hsF
  let B:=supportLift v Ω V G hsG
  let φ:=(supportedSubalgebra v Ω V).val
  have hA : PowerSeries.map φ.toRingHom A=F:=supportLift_map v Ω V F hsF
  have hB : PowerSeries.map φ.toRingHom B=G:=supportLift_map v Ω V G hsG
  have H:=congrArg (coeff n) (trace_log_product
    (R:=supportedSubalgebra v Ω (kernelSupport Ω r)) (K:=R) (rootTrace v Ω r)
    (rootTrace_cyclic v Ω hΩ r) A B (supportLift_constant v Ω V F hsF hF)
    (supportLift_constant v Ω V G hsG hG))
  simp only [map_add,coeff_traceSeries] at H
  have Hmap (D : PowerSeries (supportedSubalgebra v Ω V)) :
      rootTrace v Ω r (coeff n (FormalLog.log D))=
      coeff n (FormalLog.log (PowerSeries.map φ.toRingHom D)) r := by
    rw [log_map,coeff_map]
    rfl
  rw [Hmap,Hmap,Hmap,map_mul,hA,hB] at H
  exact H
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_HNTorusFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WallUnits.LaurentRay
noncomputable section
lemma vUnit_zpow (k : ℤ) : (↑(vUnit^k) : LaurentSeries ℚ)=HahnSeries.single (-k) 1 := by
  rw [Units.val_zpow_eq_zpow_val]
  change (atInfinity (↑PositiveRay.vUnit))^k=_
  rw [← map_zpow₀]
  exact atInfinity_v_pow k
end
end ElementaryPositivity.WallUnits.LaurentRay

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_QuantumTorusRaySeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance raySeriesAddGroup_rd4ee41_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
lemma raySeries_one (a : M) : raySeries v Ω a 1=1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_raySeries,coeff_one,coeff_one]
  split_ifs with hn
  · subst n
    rw [zero_nsmul]
    rfl
  · exact Torus.monomial_zero v Ω _
lemma monomial_sum {α : Type*} (s : Finset α) (m : M) (f : α → R) :
    Torus.monomial v Ω m (∑i∈s,f i)=∑i∈s,Torus.monomial v Ω m (f i) := by
  change Finsupp.singleAddHom m (∑i∈s,f i)=∑i∈s,Finsupp.singleAddHom m (f i)
  exact map_sum (Finsupp.singleAddHom m) f s
lemma raySeries_mul (a : M) (ha : Ω a a=0) (f g : PowerSeries R) :
    raySeries v Ω a (f*g)=raySeries v Ω a f*raySeries v Ω a g := by
  apply PowerSeries.ext
  intro n
  rw [coeff_raySeries,coeff_mul,coeff_mul,monomial_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [coeff_raySeries,coeff_raySeries,Torus.monomial_mul_monomial]
  have hz : Ω (p.1 • a) (p.2 • a)=0 := by
    simp only [map_nsmul,AddMonoidHom.nsmul_apply,ha,nsmul_zero]
  rw [hz,zpow_zero,Units.val_one,mul_one,←add_nsmul,he]

lemma raySeries_twist (hΩ : ∀m,Ω m m=0) (a m : M) (f : PowerSeries R) :
    raySeries v Ω a f*PowerSeries.C (Torus.X v Ω m)=
    PowerSeries.C (Torus.X v Ω m)*raySeries v Ω a (PowerSeries.rescale (↑(v^(2*Ω a m)):R) f) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_C,coeff_C_mul,coeff_raySeries,coeff_raySeries,coeff_rescale]
  simp only [Torus.X,Torus.monomial_mul_monomial,mul_one,one_mul]
  rw [add_comm (n • a) m]
  congr 1
  have hn : Ω (n • a) m=(n:ℤ)*Ω a m := by simp [map_nsmul]
  have hn' : Ω m (n • a)= -((n:ℤ)*Ω a m) := by
    rw [alternating_skew Ω hΩ m (n • a),hn]
  rw [hn,hn']
  have he : (↑(v^(2*Ω a m)):R)^n * (↑(v^(-((n:ℤ)*Ω a m))):R)=↑(v^((n:ℤ)*Ω a m)) := by
    rw [←Units.val_pow_eq_pow_val,←zpow_natCast,←zpow_mul,←Units.val_mul,←zpow_add]
    congr 2
    ring
  calc
    coeff n f * ↑(v^((n:ℤ)*Ω a m)) = coeff n f * ((↑(v^(2*Ω a m)):R)^n * ↑(v^(-((n:ℤ)*Ω a m)))) := by rw [he]
    _ = ((↑(v^(2*Ω a m)):R)^n * coeff n f) * ↑(v^(-((n:ℤ)*Ω a m))) := by ring
end
end ElementaryPositivity.QuantumTorus
end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

local instance rayUnitAddGroup_rd4ee41_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def rayUnit (a : M) (ha : Ω a a=0) (f : PowerSeries K) (hf : constantCoeff f=1) :
    (PowerSeries (Torus v Ω))ˣ where
  val:=raySeries v Ω a f
  inv:=raySeries v Ω a f⁻¹
  val_inv:=by
    rw [←raySeries_mul v Ω a ha,PowerSeries.mul_inv_cancel f (by rw [hf]; exact one_ne_zero),raySeries_one]
  inv_val:=by
    rw [←raySeries_mul v Ω a ha,PowerSeries.inv_mul_cancel f (by rw [hf]; exact one_ne_zero),raySeries_one]

lemma ray_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (f : PowerSeries K) (hf : constantCoeff f=1) :
    (rayUnit v Ω a (hΩ a) f hf).val * PowerSeries.C (Torus.X v Ω m) *
      (rayUnit v Ω a (hΩ a) f hf).inv=
    PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a
      (PowerSeries.rescale (↑(v^(2*Ω a m)):K) f * f⁻¹) := by
  change raySeries v Ω a f * PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a f⁻¹=_
  rw [raySeries_twist v Ω hΩ,mul_assoc,←raySeries_mul v Ω a (hΩ a)]

lemma ray_inverse_adjoint (hΩ : ∀m,Ω m m=0) (a m : M) (f : PowerSeries K) (hf : constantCoeff f=1) :
    (rayUnit v Ω a (hΩ a) f hf).inv * PowerSeries.C (Torus.X v Ω m) *
      (rayUnit v Ω a (hΩ a) f hf).val=
    PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a
      (PowerSeries.rescale (↑(v^(2*Ω a m)):K) f⁻¹ * f) := by
  change raySeries v Ω a f⁻¹ * PowerSeries.C (Torus.X v Ω m) * raySeries v Ω a f=_
  rw [raySeries_twist v Ω hΩ,mul_assoc,←raySeries_mul v Ω a (hΩ a)]
end
end ElementaryPositivity.QuantumTorus
end
end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingDisplacement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.biHomogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.homogenize_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.infinityCompletedUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma kernel_zero_log (hΩ : ∀m,Ω m m=0) (r : M) (h : M→+ℝ) (hr : h r=0)
    (F : CompletedPositive v Ω C)
    (hF : ∀n,coeff n F.val∈supportedSubalgebra v Ω (kernelSupport Ω r)) (n : ℕ) :
    coeff n (FormalLog.log (chartZero v Ω C h F).val) r=coeff n (FormalLog.log F.val) r := by
  let A:=chartPositive v Ω C h F
  let B:=chartZero v Ω C h F
  let D:=chartNegative v Ω C h F
  have H:=chartThree_supported v Ω C h (kernelSupport Ω r) F hF
  have H1:=kernel_trace_log_product v Ω hΩ r A.val B.val A.property.1 B.property.1 H.1 H.2.1 n
  have H2:=kernel_trace_log_product v Ω hΩ r (A.val*B.val) D.val
    (by simp [A.property.1,B.property.1]) D.property.1
    (PowerSeriesSplit.mul_mem (supportedSubring v Ω (kernelSupport Ω r)) _ _ H.1 H.2.1) H.2.2 n
  have HS:=chart_three_support v Ω C h F
  have hp:=log_positive_zero v Ω h A.val A.property.1 HS.1 r hr n
  have hn:=log_negative_zero v Ω h D.val D.property.1 HS.2.2 r hr n
  rw [H1,hp,hn,zero_add,add_zero] at H2
  rw [show A.val*B.val*D.val=F.val from chart_three_factorization v Ω C h F] at H2
  exact H2.symm

lemma incoming_chart_supported (r : M) (F : CompletedPositive v Ω C) :
    ∀n,coeff n (chartZero v Ω C (incomingCovector Ω r) F).val∈
      supportedSubalgebra v Ω (kernelSupport Ω r) := by
  intro n m hm
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(chartZero v Ω C (incomingCovector Ω r) F).property.1]
    change (Finsupp.single 0 (1:R)) m=0
    apply Finsupp.single_eq_of_ne
    intro he
    exact hm (he ▸ (kernelSupport Ω r).zero_mem)
  | succ n=>
    by_contra hn
    have H:=(chart_three_support v Ω C (incomingCovector Ω r) F).2.1 n m hn
    apply hm
    change Ω m r=0
    change (Ω m r:ℝ)=0 at H
    exact_mod_cast H

theorem incoming_displacement_log (hΩ : ∀m,Ω m m=0) (r : M) (h : M→+ℝ)
    (hr : h r=0) (F : CompletedPositive v Ω C) (n : ℕ) :
    coeff n (FormalLog.log (chartZero v Ω C h
      (chartZero v Ω C (incomingCovector Ω r) F)).val) r=
    coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω r) F).val) r :=
  kernel_zero_log v Ω C hΩ r h hr _ (incoming_chart_supported v Ω C r F) n
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RayIncomingIdentification
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

theorem incoming_ray_log (hΩ : ∀m,Ω m m=0) (r : M) (k : M→+ℝ) (hk : k r=0)
    (F : CompletedPositive v Ω C) (m : M) (hm : OnPositiveRay r m) (n : ℕ) :
    coeff n (FormalLog.log (chartZero v Ω C k
      (chartZero v Ω C (incomingCovector Ω r) F)).val) m=
    coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω m) F).val) m := by
  rw [incoming_same_ray v Ω C hm F]
  exact incoming_displacement_log v Ω C hΩ m k ((hm.eval k).2.1.mpr hk) F n

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_IncomingRayElement
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

lemma incoming_ray_log_support (r : M) (k : M→+ℝ) (F : CompletedPositive v Ω C) (n : ℕ) :
    SupportedOn v Ω (fun m=>Ω m r=0 ∧ k m=0)
      (coeff n (FormalLog.log (chartZero v Ω C k
        (chartZero v Ω C (incomingCovector Ω r) F)).val)) := by
  let B:=chartZero v Ω C (incomingCovector Ω r) F
  let D:=chartZero v Ω C k B
  have hr:= (chartThree_supported v Ω C k (kernelSupport Ω r) B
    (incoming_chart_supported v Ω C r F)).2.1
  have hk:=chartZero_supported_kernel v Ω C k B
  apply strict_log_support v Ω
    (fun a b ha hb=>by
      constructor
      · simp only [map_add,AddMonoidHom.add_apply,ha.1,hb.1,add_zero]
      · simp only [map_add,ha.2,hb.2,add_zero])
    D.val D.property.1 _ n
  intro j m hm
  by_contra hx
  apply hm
  constructor
  · by_contra hn
    exact hx (hr (j+1) m hn)
  · by_contra hn
    exact hx (hk (j+1) m hn)

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_WallLineInitial
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
lemma far_line_lex (S : Finset E) (v h : Module.Dual ℝ E) (b : ℝ)
    (hb : ∀a∈lineEvents S v h,a < b) (s : E) (hs : s∈S) :
    (0 < v s → 0 < (h+b • v) s) ∧ (v s < 0 → (h+b • v) s < 0) ∧
    (v s=0 → (0 < h s → 0 < (h+b • v) s) ∧ (h s=0 → (h+b • v) s=0) ∧
      (h s < 0 → (h+b • v) s < 0)) := by
  classical
  simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  have HB : v s≠0 → -h s/v s < b:=fun hv => hb _
    (Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨hs,hv⟩,rfl⟩)
  constructor
  · intro hh
    have H:=HB (ne_of_gt hh)
    have hz : h s+(-h s/v s)*v s=0:=by field_simp [ne_of_gt hh] <;> ring
    nlinarith
  constructor
  · intro hh
    have H:=HB (ne_of_lt hh)
    have hz : h s+(-h s/v s)*v s=0:=by field_simp [ne_of_lt hh] <;> ring
    nlinarith
  · intro hz
    simp only [hz,mul_zero,add_zero]
    exact ⟨id,id,id⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteElementaryAdjoint
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WallUnits
open PowerSeries
noncomputable section
variable {R : Type*} [CommRing R]
lemma degreeBound_one : DegreeBound 0 (1 : PowerSeries R) := by
  intro n hn
  rw [coeff_one,ite_eq_right (by omega)]
lemma degreeBound_linear (u : R) : DegreeBound 1 (1+PowerSeries.C u*PowerSeries.X) := by
  intro n hn
  rw [map_add,coeff_one,ite_eq_right (by omega),coeff_C_mul,coeff_X,ite_eq_right (by omega),mul_zero,add_zero]
lemma DegreeBound.mul {d e : ℕ} {f g : PowerSeries R} (hf : DegreeBound d f)
    (hg : DegreeBound e g) : DegreeBound (d+e) (f*g) := by
  intro n hn
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have heq:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : d<p.1
  · rw [hf p.1 h,zero_mul]
  · rw [hg p.2 (by omega),mul_zero]
lemma degreeBound_product_linear (u : ℕ → R) (t : ℕ) :
    DegreeBound t (∏i∈Finset.range t,(1+PowerSeries.C (u i)*PowerSeries.X)) := by
  induction t with
  | zero=>simpa using (degreeBound_one (R:=R))
  | succ t ih=>
    rw [Finset.prod_range_succ]
    exact ih.mul (degreeBound_linear (u t))
lemma DegreeBound.rescale {d : ℕ} {f : PowerSeries R} (hf : DegreeBound d f) (u : R) :
    DegreeBound d (PowerSeries.rescale u f) := by
  intro n hn
  rw [coeff_rescale,hf n hn,mul_zero]
end
section
variable {K : Type*} [Field K]
lemma elementary_ratio_degree (q u : K) (hq : q≠0)
    (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t : ℕ) :
    DegreeBound t (PowerSeries.rescale (q⁻¹^t) (elementary q u)*(elementary q u)⁻¹) := by
  rw [elementary_ratio q u hq hq' t]
  exact degreeBound_product_linear _ t
lemma elementary_inverse_ratio_degree (q u : K) (hq : q≠0)
    (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t : ℕ) :
    DegreeBound t (PowerSeries.rescale (q^t) (elementary q u)⁻¹*elementary q u) := by
  have he : PowerSeries.rescale (q^t) (elementary q u)⁻¹*elementary q u=
      PowerSeries.rescale (q^t) (PowerSeries.rescale (q⁻¹^t) (elementary q u)*(elementary q u)⁻¹) := by
    rw [map_mul,PowerSeries.rescale_rescale,←mul_pow,inv_mul_cancel₀ hq,one_pow,
      PowerSeries.rescale_one,RingHom.id_apply,mul_comm]
  rw [he]
  exact (elementary_ratio_degree q u hq hq' t).rescale _
end
end ElementaryPositivity.WallUnits
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
lemma monomial_ray_support (a m x : M) (f : PowerSeries K) (t N : ℕ)
    (hf : DegreeBound t f)
    (hx : coeff N (PowerSeries.C (Torus.X v Ω m)*raySeries v Ω a f) x≠0) :
    N≤t ∧ x=m+N • a := by
  rw [coeff_C_mul,coeff_raySeries,Torus.X,Torus.monomial_mul_monomial,one_mul] at hx
  constructor
  · by_contra h
    rw [hf N (by omega),zero_mul,Torus.monomial_zero] at hx
    exact hx rfl
  · by_contra h
    exact hx (Finsupp.single_eq_of_ne h)
lemma elementary_adjoint_support (hΩ : ∀m,Ω m m=0) (a m x : M)
    (q u : K) (hq : q≠0) (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t N : ℕ)
    (hshift : (↑(v^(2*Ω a m)):K)=q⁻¹^t)
    (hx : coeff N ((rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).val *
      PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).inv) x≠0) :
    N≤t ∧ x=m+N • a := by
  rw [ray_adjoint v Ω hΩ,hshift] at hx
  exact monomial_ray_support v Ω a m x _ t N (elementary_ratio_degree q u hq hq' t) hx
lemma elementary_inverse_adjoint_support (hΩ : ∀m,Ω m m=0) (a m x : M)
    (q u : K) (hq : q≠0) (hq' : ∀n : ℕ,1-q^(n+1)≠0) (t N : ℕ)
    (hshift : (↑(v^(2*Ω a m)):K)=q^t)
    (hx : coeff N ((rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).inv *
      PowerSeries.C (Torus.X v Ω m)*
      (rayUnit v Ω a (hΩ a) (elementary q u) (constant_elementary _ _)).val) x≠0) :
    N≤t ∧ x=m+N • a := by
  rw [ray_inverse_adjoint v Ω hΩ,hshift] at hx
  exact monomial_ray_support v Ω a m x _ t N (elementary_inverse_ratio_degree q u hq hq' t) hx
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SimpleBinomial
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma laurent_q_nonzero : (HahnSeries.single (2:ℤ) (1:ℚ) : LaurentSeries ℚ)≠0 := by
  rw [←LaurentRay.atInfinity_q]
  intro hz
  exact RationalRay.q_nonzero (LaurentRay.atInfinity_injective (hz.trans (map_zero _).symm))
lemma laurent_shift_positive (t : ℕ) :
    (↑(LaurentRay.vUnit^(2*(t:ℤ))) : LaurentSeries ℚ)=
      (HahnSeries.single (2:ℤ) (1:ℚ))⁻¹^t := by
  rw [LaurentRay.vUnit_zpow,←LaurentRay.atInfinity_v_pow,←LaurentRay.atInfinity_q,←map_inv₀,←map_pow]
  congr 1
  rw [inv_pow,RationalRay.q_pow,←zpow_neg]
  congr 1
  ring
lemma laurent_shift_negative (t : ℕ) :
    (↑(LaurentRay.vUnit^(2*(-(t:ℤ)))) : LaurentSeries ℚ)=
      (HahnSeries.single (2:ℤ) (1:ℚ))^t := by
  rw [LaurentRay.vUnit_zpow,←LaurentRay.atInfinity_v_pow,←LaurentRay.atInfinity_q,←map_pow,RationalRay.q_pow]
  congr 2
  ring
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationDegreeBound
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

lemma side_upper_le_abs (pos : Bool) (a : ℤ) : max 0 (-sideSign pos*a)≤|a| := by
  cases pos
  · simp only [sideSign,Bool.false_eq_true,ite_false, if_false,neg_neg,one_mul]
    exact max_le (abs_nonneg _) (le_abs_self _)
  · simp only [sideSign,ite_true, if_true,neg_mul,one_mul]
    exact max_le (abs_nonneg _) (neg_le_abs _)

include hcoord in
lemma fiberUpper_degree_bound (pos : Bool) {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    fiberUpper coord pc (mutationPairing Ω C pc) (sideSign pos) m≤
      (mutationSize Ω C pc:ℤ)*nonpDegree coord pc m := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  change (∑i∈Finset.univ.erase pc,max 0 (-sideSign pos*mutationPairing Ω C pc i)*coord m i)≤
    (mutationSize Ω C pc:ℤ)*(∑i∈Finset.univ.erase pc,coord m i)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right
  · exact (side_upper_le_abs pos _).trans (mutationSize_bound Ω C pc i (Finset.mem_erase.mp hi).1)
  · rw [hc]
    exact Int.natCast_nonneg _

include hcoord in
lemma fiber_full_degree_bound (pos : Bool) {n : ℕ} {m : M} (hm : HasRootDegree C n m)
    (hb : m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    (n:ℤ)≤((mutationSize Ω C pc+1:ℕ):ℤ)*nonpDegree coord pc m := by
  have Hn:=nonpDegree_root_eq C coord hcoord pc hm
  have Hk:=hb.2.trans (fiberUpper_degree_bound Ω C coord hcoord pc pos hm)
  push_cast
  nlinarith

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
open FiniteRayGeometry
noncomputable section

variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (v k : Module.Dual ℝ E)
def intervalLineEvents (lo hi : ℝ) (N : ℕ) : Finset ℝ := by
  classical
  exact (lineEvents (realRootsThrough e C N) v k).filter (fun a=>lo<a ∧ a<hi)
lemma intervalLineEvents_mono (lo hi : ℝ) {N K : ℕ} (h : N≤K) :
    intervalLineEvents C e v k lo hi N⊆intervalLineEvents C e v k lo hi K := by
  classical
  intro a ha
  obtain ⟨ha,hab⟩:=Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e h) v k ha,hab⟩

def intervalEventList (lo hi : ℝ) (N : ℕ) : List ℝ :=
  (intervalLineEvents C e v k lo hi N).sort (· ≥ ·)

lemma intervalEventList_filter (lo hi : ℝ) {N K : ℕ} (h : N≤K) :
    (intervalEventList C e v k lo hi K).filter
      (fun a=>decide (a∈intervalLineEvents C e v k lo hi N))=
    intervalEventList C e v k lo hi N :=
  sort_filter_subset _ _ (intervalLineEvents_mono C e v k lo hi h)

lemma event_not_retained (lo hi : ℝ) {N K : ℕ} (a : ℝ)
    (ha : a∈intervalEventList C e v k lo hi K)
    (hn : a∉intervalLineEvents C e v k lo hi N) :
    a∉lineEvents (realRootsThrough e C N) v k := by
  classical
  have haF : a∈intervalLineEvents C e v k lo hi K:=Finset.mem_sort _ |>.mp ha
  intro ham
  exact hn (Finset.mem_filter.mpr ⟨ham,(Finset.mem_filter.mp haF).2⟩)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_GenericLineJoining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry

section Existence
open FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma generic_paths_via_intermediate (a b k : Module.Dual ℝ E) (P : Finset E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :
    ∃h : Module.Dual ℝ E,RegularCovector C e h ∧
      (∀s∈P,(0<k s → 0<h s) ∧ (k s<0 → h s<0)) ∧
      Nonempty (GenericLinePath C e a h) ∧ Nonempty (GenericLinePath C e h b) := by
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions (realRootsThrough e C) a b k P
  have HH : RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  refine ⟨h,HH,HP,?_,?_⟩
  · let s:=segmentBetween C e a h HA HH (fun N=>(Ha N).join (HA N))
    have p:=GenericLinePath.single C e s
    exact ⟨by simpa only [s,segmentBetween_start,segmentBetween_finish] using p⟩
  · let s:=segmentBetween C e h b HH HB (fun N=>(Hb N).join_reverse (HB N))
    have p:=GenericLinePath.single C e s
    exact ⟨by simpa only [s,segmentBetween_start,segmentBetween_finish] using p⟩

theorem generic_path_exists (a b : Module.Dual ℝ E)
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :
    Nonempty (GenericLinePath C e a b) := by
  obtain ⟨h,_,_,⟨p⟩,⟨q⟩⟩:=generic_paths_via_intermediate C e a b 0 ∅ HA HB
  exact ⟨p.trans C e q⟩
end
end Existence
end ElementaryPositivity.QuantumTorus

end

end OAI
end


