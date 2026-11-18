-- Prove2me | Definitions.Def_OAIQ368Chrom005
-- name    : OAIQ368Chrom005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:07:05.224198+00:00
-- url     : https://prove2.me/theorems/b8d630cc-dc4e-4248-a261-b4330c250bc6
-- title:
--   Definitions bundle OAIQ368Chrom005 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 92 declarations of OpenAI's Lean: 44 definitions, 4 inductive types or structures and 44 theorems. The definitions and types are `OAI.ElementaryPositivity.QuantumTorus.mutatedNoCutTransportPathRing`, `OAI.ElementaryPositivity.QuantumTorus.mutatedNoCutTransportRing`, `OAI.ElementaryPositivity.QuantumTorus.mutationSimpleIncomingRing`, `OAI.ElementaryPositivity.QuantumTorus.mutationSimpleSideRing`, `OAI.ElementaryPositivity.QuantumTorus.polynomialAdjointCoefficientsRing`, `OAI.ElementaryPositivity.QuantumTorus.regrade`, `OAI.ElementaryPositivity.QuantumTorus.regradeAddCommMonoid`, `OAI.ElementaryPositivity.QuantumTorus.regradeAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommGroup`, `OAI.ElementaryPositivity.QuantumTorus.regradeLogAddCommMonoid`, `OAI.ElementaryPositivity.QuantumTorus.regradeLogAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.regradeRing`, `OAI.ElementaryPositivity.QuantumTorus.regradeTopology`, `OAI.ElementaryPositivity.QuantumTorus.rootLaurentCompletionRing`, `OAI.ElementaryPositivity.RationalFiber.ComparisonCrossing`, `OAI.ElementaryPositivity.RationalFiber.CrossingClose`, `OAI.ElementaryPositivity.RationalFiber.CrossingTrivial`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus.gauge`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus.gaugeAdd`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus.gaugeMonomial`, `OAI.ElementaryPositivity.RationalFiber.PureExtension`, `OAI.ElementaryPositivity.RationalFiber.WordRefines`, `OAI.ElementaryPositivity.RationalFiber.completedPureAction`, `OAI.ElementaryPositivity.RationalFiber.completedShearAction`, `OAI.ElementaryPositivity.RationalFiber.fiberReciprocal`, `OAI.ElementaryPositivity.RationalFiber.fiberReciprocalAdd`, `OAI.ElementaryPositivity.RationalFiber.fiberReciprocalTerm`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_5`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_7`, `OAI.ElementaryPositivity.RationalFiber.instRingTorus_8`, `OAI.ElementaryPositivity.RationalFiber.mutationSideAction`, `OAI.ElementaryPositivity.RationalFiber.orientedBounded`, `OAI.ElementaryPositivity.RationalFiber.pureAction`, `OAI.ElementaryPositivity.RationalFiber.pureActionHom`, `OAI.ElementaryPositivity.RationalFiber.pureActionInvHom`, `OAI.ElementaryPositivity.RationalFiber.pureGenerator`, `OAI.ElementaryPositivity.RationalFiber.pureRatio`, `OAI.ElementaryPositivity.RationalFiber.pureStep`, `OAI.ElementaryPositivity.RationalFiber.rationalRegrade`, `OAI.ElementaryPositivity.RationalFiber.readFiberInfinity` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_LaurentPureAction`, `Chromatic_GradedAlgebra_MutationRootMap`, `Chromatic_GradedAlgebra_NonpRegrade`, `Chromatic_GradedAlgebra_NonpRegradeFaithful`, `Chromatic_GradedAlgebra_PureComparisonIdentification`, `Chromatic_GradedAlgebra_RationalRegrade`, `Chromatic_GradedAlgebra_RationalShearCocycle`, `Chromatic_GradedAlgebra_RealRootCoordinates`, `Chromatic_GradedAlgebra_RegradeLog`, `Chromatic_QuantumTorus_PureCutTelescoping`, `Chromatic_QuantumTorus_RationalPureAction`, `Chromatic_Walls_ComparisonRefinement`, `Chromatic_Walls_CompletedCutAction`, `Chromatic_Walls_CompletedInfinityCut`, `Chromatic_Walls_CompletedPureComparison`, `Chromatic_Walls_FiniteFiberInfinity`, `Chromatic_Walls_MutatedNoCutTransport`, `Chromatic_Walls_MutationSimpleIncoming`, `Chromatic_Walls_PolynomialAdjointCoefficients`, `Chromatic_Walls_RationalCutIdentity`, `Chromatic_Walls_RationalFiberReciprocal`, `Chromatic_Walls_RationalFiberScale`, `Chromatic_Walls_RationalPureCocycle`, `Chromatic_Walls_RootLaurentCompletion`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom006` and `OAIQ368Chrom025`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom004

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalFiberScale
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
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
def scaleEquiv (a : Kˣ) : RatFunc K ≃+* RatFunc K :=
  RingEquiv.ofRingHom (scale a) (scale a⁻¹)
    (by rw [scale_mul,mul_inv_cancel,scale_one])
    (by rw [scale_mul,inv_mul_cancel,scale_one])

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalFiberReciprocal
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.reciprocalUnit_val
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
lemma reciprocal_scale (a : Kˣ) :
    (reciprocal (K:=K)).comp (scale a)=(scale a⁻¹).comp reciprocal := by
  apply ratFunc_hom_ext_C_X
  · intro b; simp
  · simp [mul_inv_rev,mul_comm]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalPureCocycle
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]

def scaleAction (v : Kˣ) : Multiplicative ℤ →* MulAut (RatFunc K)ˣ where
  toFun t:=Units.mapEquiv (scaleEquiv (v^(-2*t.toAdd))).toMulEquiv
  map_one':=by
    ext x
    change scale (v^(-2*(0:ℤ))) (x:RatFunc K)=(x:RatFunc K)
    simp
  map_mul' t u:=by
    ext x
    change scale (v^(-2*(t.toAdd+u.toAdd))) (x:RatFunc K)=
      scale (v^(-2*t.toAdd)) (scale (v^(-2*u.toAdd)) (x:RatFunc K))
    rw [show v^(-2*(t.toAdd+u.toAdd))=v^(-2*t.toAdd)*v^(-2*u.toAdd) by rw [mul_add,zpow_add],←scale_mul]
    rfl
@[simp] lemma scaleAction_val (v : Kˣ) (t : Multiplicative ℤ) (a : (RatFunc K)ˣ) :
    ((scaleAction v t a : (RatFunc K)ˣ):RatFunc K)=scale (v^(-2*t.toAdd)) (a:RatFunc K) := rfl
lemma linearFactor_ne_zero (a : K) : (1+RatFunc.C a*RatFunc.X : RatFunc K)≠0 := by
  have he : (1+RatFunc.C a*RatFunc.X : RatFunc K)=
      algebraMap (Polynomial K) (RatFunc K) (1+Polynomial.C a*Polynomial.X) := by simp
  rw [he]
  intro hz
  have h : (1+Polynomial.C a*Polynomial.X : Polynomial K)=0 :=
    (RatFunc.algebraMap_injective (K:=K)) (by simpa using hz)
  have H:=congrArg (Polynomial.coeff · 0) h
  simp at H

def pureStep (v : Kˣ) : (RatFunc K)ˣ := Units.mk0 _ (linearFactor_ne_zero (↑(v⁻¹):K))
abbrev PureExtension (v : Kˣ) := (RatFunc K)ˣ ⋊[scaleAction v] Multiplicative ℤ
def pureGenerator (v : Kˣ) : PureExtension v := ⟨pureStep v,Multiplicative.ofAdd 1⟩
def pureRatio (v : Kˣ) (t : ℤ) : (RatFunc K)ˣ := (pureGenerator v^t).left
lemma pureRight (v : Kˣ) (t : ℤ) : (pureGenerator v^t).right=Multiplicative.ofAdd t := by
  change SemidirectProduct.rightHom (pureGenerator v^t)=_
  rw [map_zpow]
  change (Multiplicative.ofAdd 1)^t=Multiplicative.ofAdd t
  rw [←ofAdd_zsmul,smul_eq_mul,mul_one]
@[simp] lemma pureRatio_zero (v : Kˣ) : pureRatio v 0=1 := by simp [pureRatio]
@[simp] lemma pureRatio_one (v : Kˣ) : pureRatio v 1=pureStep v := by simp [pureRatio,pureGenerator]
lemma pureRatio_add (v : Kˣ) (t u : ℤ) :
    pureRatio v (t+u)=pureRatio v t*scaleAction v (Multiplicative.ofAdd t) (pureRatio v u) := by
  simp only [pureRatio,zpow_add,SemidirectProduct.mul_left,pureRight]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open WallUnits PowerSeries
noncomputable section
variable {K : Type*} [Field K]
variable (v : Kˣ)
def shiftedElementary (t : ℤ) : PowerSeries K :=
  rescale (↑(v^(-2*t)):K) (elementary (↑(v^(-2:ℤ)):K) (↑(v⁻¹):K))
lemma shiftedElementary_constant (t : ℤ) : constantCoeff (shiftedElementary v t)=1 := by
  rw [shiftedElementary,←coeff_zero_eq_constantCoeff,coeff_rescale]
  simp [elementaryCoeff]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalPureAction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
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
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
namespace FiberTorus

def gaugeMonomial (c : ℤ → RatFunc K) (m : M) : RatFunc K →+ FiberTorus v Ω α where
  toFun a:=monomial v Ω α m (a*c (α m))
  map_zero':=by simp
  map_add' a b:=by simp only [_root_.add_mul,monomial_add]
def gaugeAdd (c : ℤ → RatFunc K) : FiberTorus v Ω α →+ FiberTorus v Ω α :=
  Finsupp.liftAddHom (gaugeMonomial v Ω α c)
@[simp] lemma gaugeAdd_monomial (c : ℤ → RatFunc K) (m : M) (a : RatFunc K) :
    gaugeAdd v Ω α c (monomial v Ω α m a)=monomial v Ω α m (a*c (α m)) :=
  Finsupp.liftAddHom_apply_single _ _ _
lemma gaugeAdd_mul (c : ℤ → RatFunc K) (hc : ∀t u,c (t+u)=c t*scale (v^(-2*t)) (c u))
    (f g : FiberTorus v Ω α) :
    gaugeAdd v Ω α c (f*g)=gaugeAdd v Ω α c f*gaugeAdd v Ω α c g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [add_mul,map_add,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [mul_add,map_add,hg,hg']
    | single n b=>
      change gaugeAdd v Ω α c (monomial v Ω α m a*monomial v Ω α n b)=
        gaugeAdd v Ω α c (monomial v Ω α m a)*gaugeAdd v Ω α c (monomial v Ω α n b)
      rw [monomial_mul,gaugeAdd_monomial,gaugeAdd_monomial,gaugeAdd_monomial,monomial_mul]
      simp only [map_add,hc,map_mul]
      congr 1
      change a*twist v α m b*RatFunc.C (↑(v^(Ω m n)):K)*
        (c (α m)*twist v α m (c (α n)))=
        (a*c (α m))*(twist v α m b*twist v α m (c (α n)))*RatFunc.C (↑(v^(Ω m n)):K)
      ring
lemma gaugeAdd_one (c : ℤ → RatFunc K) (hc : c 0=1) : gaugeAdd v Ω α c 1=1 := by
  change gaugeAdd v Ω α c (monomial v Ω α 0 1)=monomial v Ω α 0 1
  rw [gaugeAdd_monomial,map_zero,hc,_root_.mul_one]
def gauge (c : ℤ → RatFunc K) (hc0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scale (v^(-2*t)) (c u)) : FiberTorus v Ω α →+* FiberTorus v Ω α where
  __:=gaugeAdd v Ω α c
  map_one':=gaugeAdd_one v Ω α c hc0
  map_mul':=gaugeAdd_mul v Ω α c hc
@[simp] lemma gauge_monomial (c : ℤ → RatFunc K) (hc0 : c 0=1)
    (hc : ∀t u,c (t+u)=c t*scale (v^(-2*t)) (c u)) (m : M) (a : RatFunc K) :
    gauge v Ω α c hc0 hc (monomial v Ω α m a)=monomial v Ω α m (a*c (α m)) :=
  gaugeAdd_monomial v Ω α c m a
lemma gauge_comp (c d : ℤ → RatFunc K) (f : FiberTorus v Ω α) :
    gaugeAdd v Ω α c (gaugeAdd v Ω α d f)=gaugeAdd v Ω α (fun t=>d t*c t) f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change gaugeAdd v Ω α c (gaugeAdd v Ω α d (monomial v Ω α m a))=
      gaugeAdd v Ω α (fun t=>d t*c t) (monomial v Ω α m a)
    simp only [gaugeAdd_monomial,_root_.mul_assoc]
lemma gaugeAdd_trivial (f : FiberTorus v Ω α) : gaugeAdd v Ω α (fun _=>1) f=f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [map_add,hf,hg]
  | single m a=>
    change gaugeAdd v Ω α (fun _=>1) (monomial v Ω α m a)=monomial v Ω α m a
    rw [gaugeAdd_monomial,_root_.mul_one]
end FiberTorus

lemma pureRatio_val_add (t u : ℤ) : (pureRatio v (t+u):RatFunc K)=
    (pureRatio v t:RatFunc K)*scale (v^(-2*t)) (pureRatio v u:RatFunc K) := by
  rw [pureRatio_add,Units.val_mul,scaleAction_val]
  rfl
lemma pureRatio_inv_val_add (t u : ℤ) : (↑((pureRatio v (t+u))⁻¹):RatFunc K)=
    (↑((pureRatio v t)⁻¹):RatFunc K)*scale (v^(-2*t)) (↑((pureRatio v u)⁻¹):RatFunc K) := by
  simp only [Units.val_inv_eq_inv_val,pureRatio_val_add,map_inv₀,mul_inv_rev]
  exact mul_comm _ _
def pureActionHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(pureRatio v t:RatFunc K)) (by simp) (pureRatio_val_add v)
def pureActionInvHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(↑((pureRatio v t)⁻¹):RatFunc K)) (by simp) (pureRatio_inv_val_add v)
lemma pureAction_cancel (f : FiberTorus v Ω α) :
    pureActionHom v Ω α (pureActionInvHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa using FiberTorus.gaugeAdd_trivial v Ω α f
lemma pureActionInv_cancel (f : FiberTorus v Ω α) :
    pureActionInvHom v Ω α (pureActionHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa using FiberTorus.gaugeAdd_trivial v Ω α f
def pureAction : FiberTorus v Ω α ≃+* FiberTorus v Ω α :=
  RingEquiv.ofRingHom (pureActionHom v Ω α) (pureActionInvHom v Ω α)
    (RingHom.ext (pureAction_cancel v Ω α)) (RingHom.ext (pureActionInv_cancel v Ω α))
@[simp] lemma pureAction_monomial (m : M) (a : RatFunc K) :
    pureAction v Ω α (FiberTorus.monomial v Ω α m a)=
      FiberTorus.monomial v Ω α m (a*(pureRatio v (α m):RatFunc K)) :=
  FiberTorus.gaugeAdd_monomial v Ω α (fun t=>(pureRatio v t:RatFunc K)) m a

def completedPureAction : PowerSeries (FiberTorus v Ω α) ≃+* PowerSeries (FiberTorus v Ω α) :=
  RingEquiv.ofRingHom (PowerSeries.map (pureAction v Ω α).toRingHom)
    (PowerSeries.map (pureAction v Ω α).symm.toRingHom)
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def regrade (f : PowerSeries (Torus v Ω)) : PowerSeries (Torus v Ω) :=
  PowerSeries.mk fun d=>∑n∈Finset.range (B*d+1),coeff d (homogenize v Ω δ (coeff n f))
lemma regrade_coeff (f : PowerSeries (Torus v Ω)) (d : ℕ) :
    coeff d (regrade v Ω δ B f)=
      ∑n∈Finset.range (B*d+1),coeff d (homogenize v Ω δ (coeff n f)) := coeff_mk _ _

section Topology
local instance regradeTopology : TopologicalSpace (Torus v Ω) := ⊥
local instance regradeDiscreteTopology : DiscreteTopology (Torus v Ω) := ⟨rfl⟩
open scoped PowerSeries.WithPiTopology

lemma regrade_hasSum {f : PowerSeries (Torus v Ω)} (hf : RegradeBound v Ω δ B f) :
    HasSum (fun n=>homogenize v Ω δ (coeff n f)) (regrade v Ω δ B f) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [regrade_coeff]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  apply hf.homogenize_vanish v Ω δ B d n
  have H : B*d+1≤n:=by simpa only [Finset.mem_range,not_lt] using hn
  omega

lemma regrade_product_summable {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g) :
    Summable (fun ab : ℕ×ℕ=>homogenize v Ω δ (coeff ab.1 f)*homogenize v Ω δ (coeff ab.2 g)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  intro d
  apply summable_of_hasFiniteSupport
  apply (Finset.finite_toSet ((Finset.range (B*d+1)).product (Finset.range (B*d+1)))).subset
  intro ab hab
  change coeff d (homogenize v Ω δ (coeff ab.1 f)*homogenize v Ω δ (coeff ab.2 g))≠0 at hab
  change ab∈(Finset.range (B*d+1)) ×ˢ (Finset.range (B*d+1))
  rw [Finset.mem_product,Finset.mem_range,Finset.mem_range]
  by_contra H
  apply hab
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro kl hkl
  have hsum:=Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  have hl : B*kl.1≤B*d:=Nat.mul_le_mul_left B (by omega)
  have hr : B*kl.2≤B*d:=Nat.mul_le_mul_left B (by omega)
  by_cases ha : ab.1<B*d+1
  · have hb : B*d<ab.2:=by omega
    rw [hg.homogenize_vanish v Ω δ B kl.2 ab.2 (lt_of_le_of_lt hr hb),Torus.mul_zero]
  · have ha' : B*d<ab.1:=by omega
    rw [hf.homogenize_vanish v Ω δ B kl.1 ab.1 (lt_of_le_of_lt hl ha'),Torus.zero_mul]

end Topology
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_NonpRegradeFaithful
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.pushAdd_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_X _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.push_monomial _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_raySeries _root_.OAI.ElementaryPositivity.QuantumTorus.coeff_weightedRay _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_inv _root_.OAI.ElementaryPositivity.QuantumTorus.completedBiUnit_val _root_.OAI.ElementaryPositivity.QuantumTorus.laurentHomogenize_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embedAdd_monomial _root_.OAI.ElementaryPositivity.RationalFiber.embed_monomial
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
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.regradeFaithfulRing
local instance regradeFaithfulAddCommMonoid_rf14f32_1 : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance regradeFaithfulAddGroup_rf14f32_1 : AddGroup (Torus v Ω) :=
  (Torus.instRing v Ω).toAddGroup
lemma regrade_coeff_eval (f : PowerSeries (Torus v Ω)) (d : ℕ) (m : M) :
    coeff d (regrade v Ω δ B f) m=
      if d=(δ m).toNat then ∑n∈Finset.range (B*d+1),coeff n f m else 0 := by
  classical
  rw [regrade_coeff,nonp_torus_eval_sum]
  simp_rw [homogenize_coeff]
  split_ifs <;> simp_all

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalRegrade
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
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
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
variable (δ : M →+ ℤ) (B : ℕ)
def rationalRegrade (f : PowerSeries (Torus v Ω)) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :=
  PowerSeries.map (embed v Ω hΩ k p hp) (regrade v Ω δ B f)
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

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
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ κ : M →+ ℤ) (p : M) (hδ : δ p=0) (hκ : κ p=1)
local instance instRingTorus_3_rf14f32_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_1_rf14f32_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_1_rf14f32_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_3_rf14f32_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_3_rf14f32_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
include hδ hκ in
lemma pure_biSupported (f : PowerSeries K) : BiSupported v Ω δ κ (raySeries v Ω p f) := by
  intro n m hm
  rw [coeff_raySeries] at hm
  have he : m=n • p := by
    by_contra H
    exact hm (Finsupp.single_eq_of_ne H)
  subst m
  simp only [map_nsmul,hδ,hκ,nsmul_eq_mul,mul_one]
  exact ⟨le_rfl,Int.natCast_nonneg _,by omega⟩
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RationalShearCocycle
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
attribute [-simp] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.gauge_monomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K : Type*} [Field K]
@[simp] lemma scaleAction_coefficientUnit (v w : Kˣ) (t : ℤ) :
    scaleAction v (Multiplicative.ofAdd t) (coefficientUnit w)=coefficientUnit w := by
  apply Units.ext
  simp
@[simp] lemma scaleAction_variableUnit (v : Kˣ) (t : ℤ) :
    scaleAction v (Multiplicative.ofAdd t) variableUnit=coefficientUnit v^(-2*t)*variableUnit := by
  apply Units.ext
  simp [scale_X,Units.val_zpow_eq_zpow_val,map_zpow₀]

def shearRatio (v : Kˣ) (t : ℤ) : (RatFunc K)ˣ :=
  coefficientUnit v^(t*t)*variableUnit^(-t)
@[simp] lemma shearRatio_zero (v : Kˣ) : shearRatio v 0=1 := by simp [shearRatio]
lemma shearRatio_add (v : Kˣ) (t u : ℤ) :
    shearRatio v (t+u)=shearRatio v t*scaleAction v (Multiplicative.ofAdd t) (shearRatio v u) := by
  simp only [shearRatio,map_mul,map_zpow,scaleAction_coefficientUnit,scaleAction_variableUnit,mul_zpow]
  rw [←zpow_mul,show (t+u)*(t+u)=t*t+u*u+(-2*t)*(-u) by ring,
    show -(t+u)= -t+ -u by ring,zpow_add,zpow_add,zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]
@[simp] lemma shearRatio_val (v : Kˣ) (t : ℤ) :
    (shearRatio v t:RatFunc K)=RatFunc.C (↑(v^(t*t)):K)*RatFunc.X^(-t) := by
  simp [shearRatio,Units.val_zpow_eq_zpow_val,map_zpow₀]

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
lemma shearRatio_val_add (t u : ℤ) : (shearRatio v (t+u):RatFunc K)=
    (shearRatio v t:RatFunc K)*scale (v^(-2*t)) (shearRatio v u:RatFunc K) := by
  rw [shearRatio_add,Units.val_mul,scaleAction_val]
  rfl
def shearActionHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(shearRatio v t:RatFunc K)) (by simp) (shearRatio_val_add v)
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

lemma mutatedRoot_p : simpleRoot (mutatedRoots Ω C pc) pc= -simpleRoot C pc := by
  have he : mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single pc 1)=
      -(Pi.single pc 1 : I → ℤ):=by
    ext i
    by_cases hi : i=pc
    · subst i
      rw [mutatedCoefficientMap_at]
      have HH : (∑j∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc j)*((Pi.single pc 1 : I → ℤ) j))=0:=by
        apply Finset.sum_eq_zero
        intro j hj
        simp [(Finset.mem_erase.mp hj).1]
      rw [HH]; simp
    · rw [mutatedCoefficientMap_off pc _ _ i hi]
      simp [hi]
  change C (mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single pc 1))= -C (Pi.single pc 1)
  rw [he,map_neg]

lemma mutatedRoot_off (i : I) (hi : i≠pc) :
    simpleRoot (mutatedRoots Ω C pc) i=simpleRoot C i+
      max 0 (-mutationPairing Ω C pc i) • simpleRoot C pc := by
  have he : mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single i 1)=
      (Pi.single i 1 : I → ℤ)+max 0 (-mutationPairing Ω C pc i) • Pi.single pc 1:=by
    ext j
    by_cases hj : j=pc
    · subst j
      rw [mutatedCoefficientMap_at]
      have HH : (∑a∈Finset.univ.erase pc,max 0 (-mutationPairing Ω C pc a)*((Pi.single i 1 : I → ℤ) a))=
          max 0 (-mutationPairing Ω C pc i):=by
        rw [Finset.sum_eq_single i]
        · simp
        · intro a ha hai; simp [hai]
        · simp [hi]
      rw [HH]
      simp [Ne.symm hi]
    · rw [mutatedCoefficientMap_off pc _ _ j hj]
      simp [Pi.single_apply,hj]
  change C (mutatedCoefficientMap pc (mutationPairing Ω C pc) (Pi.single i 1))=_
  rw [he,map_add,map_zsmul]
  rfl

end
end ElementaryPositivity.QuantumTorus

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
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1)
local instance instRingTorus_5 : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (hδ : δ p=0) (B : ℕ)

local instance instRingTorus_6_rf14f32_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_3_rf14f32_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_3_rf14f32_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_6_rf14f32_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_6_rf14f32_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
inductive ComparisonCrossing where
  | bounded (u : (biSupportedSubring v Ω δ k)ˣ)
      (forward_bound : RegradeBound v Ω δ B u.val.val)
      (inverse_bound : RegradeBound v Ω δ B u.inv.val)
  | pure (forward : Bool)

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_PureComparisonIdentification
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
omit [Fintype I] in
include hcoord in
lemma pureDegree_simple_self : pureDegree coord pc (simpleRoot C pc)=1 := by
  change coord (simpleRoot C pc) pc=1
  rw [simpleRoot_coordinates C coord hcoord,Pi.single_eq_same]

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RealRootCoordinates
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma realRootCoordinates_exists (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    ∃D:E →ₗ[ℝ] (I → ℝ),∀a,D (e (C a))=fun i=>(a i:ℝ) := by
  let f:=Finsupp.linearCombination ℝ (fun i=>e (simpleRoot C i))
  obtain ⟨g,hg⟩:=f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  let D:E →ₗ[ℝ] (I → ℝ):=LinearMap.pi (fun i=>(Finsupp.lapply i).comp g)
  have hd (i:I) : D (e (simpleRoot C i))=Pi.single i 1:=by
    have H:=LinearMap.congr_fun hg (Finsupp.single i 1)
    simp only [LinearMap.comp_apply,LinearMap.id_apply,f,Finsupp.linearCombination_single,one_smul] at H
    funext j
    change g (e (simpleRoot C i)) j=(Pi.single i 1:I → ℝ) j
    rw [H]
    simp [Finsupp.single_apply,Pi.single_apply,eq_comm]
  refine ⟨D,fun a=>?_⟩
  rw [coefficient_simple_expansion C,map_sum,map_sum]
  simp only [map_zsmul,hd]
  ext j
  simp only [Finset.sum_apply,zsmul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij; simp [Ne.symm hij]
  · simp

omit [Fintype I] in
lemma real_coordinate_simple (D:E →ₗ[ℝ] (I → ℝ))
    (hD:∀a,D (e (C a))=fun i=>(a i:ℝ)) (i:I) : D (e (simpleRoot C i))=Pi.single i 1 := by
  rw [simpleRoot,hD]
  ext j
  simp [Pi.single_apply]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RegradeLog
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ : M →+ ℤ) (B : ℕ)
local instance regradeLogRing_rf14f32_1 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance regradeLogNonUnitalSemiring_rf14f32_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance regradeLogNonUnitalNonAssocSemiring_rf14f32_1 : NonUnitalNonAssocSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
local instance regradeLogAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance regradeLogAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance regradeLogAddCommGroup : AddCommGroup (Torus v Ω) := (Torus.instRing v Ω).toAddCommGroup
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ComparisonRefinement
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
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (δ k : M →+ ℤ) (p : M) (hp : k p=1) (B : ℕ)
local instance instRingTorus_7 : Ring (Torus v Ω) := Torus.instRing v Ω
local instance instAddCommMonoidTorus_4_rf14f32_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_4_rf14f32_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_7_rf14f32_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_7_rf14f32_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
inductive CrossingClose (D : ℕ) : ComparisonCrossing v Ω δ k B → ComparisonCrossing v Ω δ k B → Prop where
  | pure (b : Bool) : CrossingClose D (.pure b) (.pure b)
  | bounded (u w : (biSupportedSubring v Ω δ k)ˣ)
      (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
      (hf' : RegradeBound v Ω δ B w.val.val) (hi' : RegradeBound v Ω δ B w.inv.val)
      (he : ∀n≤B*D,coeff n u.val.val=coeff n w.val.val) :
      CrossingClose D (.bounded u hf hi) (.bounded w hf' hi')
inductive WordRefines (D : ℕ) : List (ComparisonCrossing v Ω δ k B) →
    List (ComparisonCrossing v Ω δ k B) → Prop where
  | nil : WordRefines D [] []
  | cons {c c' l l'} (hc : CrossingClose v Ω δ k B D c c') (hl : WordRefines D l l') :
      WordRefines D (c::l) (c'::l')
  | insert {l l'} (u : (biSupportedSubring v Ω δ k)ˣ)
      (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
      (he : ∀n≤B*D,coeff n u.val.val=coeff n 1) (hl : WordRefines D l l') :
      WordRefines D l (.bounded u hf hi::l')
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (δ k : M →+ ℤ) (B : ℕ)
local instance instRingTorus_8 : Ring (Torus v Ω) := Torus.instRing v Ω

local instance instAddCommMonoidTorus_5_rf14f32_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance instAddGroupTorus_5_rf14f32_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance instNonUnitalSemiringTorus_8_rf14f32_1 : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance instNonUnitalNonAssocSemiringTorus_8_rf14f32_1 : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
inductive CrossingTrivial (N : ℕ) : ComparisonCrossing v Ω δ k B → Prop where
  | bounded (u : (biSupportedSubring v Ω δ k)ˣ)
      (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
      (he : ∀n≤N,coeff n u.val.val=coeff n 1) :
      CrossingTrivial N (.bounded u hf hi)

def orientedBounded (u : (biSupportedSubring v Ω δ k)ˣ)
    (hf : RegradeBound v Ω δ B u.val.val) (hi : RegradeBound v Ω δ B u.inv.val)
    (b : Bool) : ComparisonCrossing v Ω δ k B :=
  if b then .bounded u hf hi else .bounded u⁻¹ hi hf

end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutationSimpleIncoming
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
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)
local instance mutationSimpleIncomingRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I) (pos : Bool)

variable {R : Type*} [CommRing R] (v : Rˣ)
local instance mutationSimpleSideRing : Ring (Torus v Ω) := Torus.instRing v Ω
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
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α β : M →+ ℤ) (hβ : ∀m,β m= -α m)

def fiberReciprocalTerm (m : M) : RatFunc K →+ FiberTorus v Ω β where
  toFun a:=FiberTorus.monomial v Ω β m (reciprocal a)
  map_zero':=by simp
  map_add' a b:=by simp only [map_add,FiberTorus.monomial_add]
def fiberReciprocalAdd : FiberTorus v Ω α →+ FiberTorus v Ω β :=
  Finsupp.liftAddHom (fiberReciprocalTerm v Ω β)
lemma fiberReciprocalAdd_monomial (m : M) (a : RatFunc K) :
    fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α m a)=
      FiberTorus.monomial v Ω β m (reciprocal a) := Finsupp.liftAddHom_apply_single _ _ _
include hβ in
lemma reciprocal_twist (m : M) (a : RatFunc K) :
    reciprocal (FiberTorus.twist v α m a)=FiberTorus.twist v β m (reciprocal a) := by
  have H:=congrArg (fun F : RatFunc K →+* RatFunc K=>F a) (reciprocal_scale (v^(-2*α m)))
  change reciprocal (scale (v^(-2*α m)) a)=scale (v^(-2*β m)) (reciprocal a)
  rw [hβ]
  have he : (v^(-2*α m))⁻¹=v^(-2*(-α m)):=by
    rw [←zpow_neg]
    congr 1
    ring
  simpa only [RingHom.coe_comp,Function.comp_apply,he] using H
include hβ in
lemma fiberReciprocalAdd_mul (f g : FiberTorus v Ω α) :
    fiberReciprocalAdd v Ω α β (f*g)=fiberReciprocalAdd v Ω α β f*fiberReciprocalAdd v Ω α β g := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f f' hf hf'=>simp only [_root_.add_mul,map_add,hf,hf']
  | single m a=>
    induction g using Finsupp.induction_linear with
    | zero=>simp
    | add g g' hg hg'=>simp only [_root_.mul_add,map_add,hg,hg']
    | single n b=>
      change fiberReciprocalAdd v Ω α β
        (FiberTorus.monomial v Ω α m a*FiberTorus.monomial v Ω α n b)=
        fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α m a)*
          fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α n b)
      rw [FiberTorus.monomial_mul,fiberReciprocalAdd_monomial,
        fiberReciprocalAdd_monomial,fiberReciprocalAdd_monomial,FiberTorus.monomial_mul]
      simp only [map_mul,reciprocal_constant,reciprocal_twist v α β hβ]
def fiberReciprocal : FiberTorus v Ω α →+* FiberTorus v Ω β where
  __:=fiberReciprocalAdd v Ω α β
  map_one':=by
    change fiberReciprocalAdd v Ω α β (FiberTorus.monomial v Ω α 0 1)=_
    rw [fiberReciprocalAdd_monomial,map_one]
    rfl
  map_mul':=fiberReciprocalAdd_mul v Ω α β hβ

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
lemma shearRatio_inv_val_add (t u : ℤ) : (↑((shearRatio v (t+u))⁻¹):RatFunc K)=
    (↑((shearRatio v t)⁻¹):RatFunc K)*scale (v^(-2*t)) (↑((shearRatio v u)⁻¹):RatFunc K) := by
  simp only [Units.val_inv_eq_inv_val,shearRatio_val_add,map_inv₀,mul_inv_rev]
  exact mul_comm _ _
def shearActionInvHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(↑((shearRatio v t)⁻¹):RatFunc K)) (by simp)
    (shearRatio_inv_val_add v)
lemma shearAction_cancel (f : FiberTorus v Ω α) :
    shearActionHom v Ω α (shearActionInvHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa only [←Units.val_mul,inv_mul_cancel,Units.val_one] using
    FiberTorus.gaugeAdd_trivial v Ω α f
lemma shearActionInv_cancel (f : FiberTorus v Ω α) :
    shearActionInvHom v Ω α (shearActionHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa only [←Units.val_mul,mul_inv_cancel,Units.val_one] using
    FiberTorus.gaugeAdd_trivial v Ω α f
def shearAction : FiberTorus v Ω α ≃+* FiberTorus v Ω α :=
  RingEquiv.ofRingHom (shearActionHom v Ω α) (shearActionInvHom v Ω α)
    (RingHom.ext (shearAction_cancel v Ω α)) (RingHom.ext (shearActionInv_cancel v Ω α))
def completedShearAction : PowerSeries (FiberTorus v Ω α) ≃+* PowerSeries (FiberTorus v Ω α) :=
  RingEquiv.ofRingHom (PowerSeries.map (shearAction v Ω α).toRingHom)
    (PowerSeries.map (shearAction v Ω α).symm.toRingHom)
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])

end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
def mutationSideAction (pos : Bool) : PowerSeries (FiberTorus v Ω α) ≃+*
    PowerSeries (FiberTorus v Ω α) :=
  if pos then RingEquiv.refl _ else completedShearAction v Ω α

end

end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_CompletedInfinityCut
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

lemma complementAlpha_neg_p (m : k.ker) :
    complementAlpha k (-p) Ω m= -complementAlpha k p Ω m := by
  change Ω (-p) m= -Ω p m
  simp

def reciprocalFiber : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+*
    FiberTorus v (complementOmega k Ω) (complementAlpha k (-p) Ω) :=
  fiberReciprocal v (complementOmega k Ω) (complementAlpha k p Ω)
    (complementAlpha k (-p) Ω) (complementAlpha_neg_p Ω k p)

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
open QuantumTorus
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
@[simp] lemma expandInfinity_constant (a : K) :
    expandInfinity (RatFunc.C a)=HahnSeries.C a := by
  change expandZero (reciprocal (RatFunc.C a))=_
  rw [reciprocal_constant,expandZero_constant]

def readFiberInfinity (m : M) : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω) →+ K where
  toFun f:=(expandInfinity (f (off k p hp m))).coeff (-k m)*
    (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)
  map_zero':=by simp
  map_add' f g:=by simp [add_mul]
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_MutatedNoCutTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance mutatedNoCutTransportRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance mutatedNoCutTransportPathRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialAdjointCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
local instance polynomialAdjointCoefficientsRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RootLaurentCompletion
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
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ η : M →+ ℤ) (B : ℕ)
local instance rootLaurentCompletionRing : Ring (Torus v Ω) := Torus.instRing v Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end


