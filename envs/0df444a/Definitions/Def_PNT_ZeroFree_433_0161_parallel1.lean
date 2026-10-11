-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0161_parallel1
-- name    : PNT_ZeroFree_433_0161_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:55:16.831306+00:00
-- url     : https://prove2.me/theorems/2decd38b-2032-4a5a-b230-50727fba74c1
-- title:
--   Zero-free region foundations: GaussSum.BranchScaling [0161_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.BranchScaling
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/BranchScaling.lean#L138-L623

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0059
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/BranchScaling.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff


open scoped BigOperators Classical
namespace LocalReflectionBrackets
variable {F : Type*} [Field F] [Fintype F]

def unitArgumentFactor (χ : MulChar F ℂ) (j : ℕ) (z : F) : ℂ :=
  if j=4 then 1 else (χ^(j+2))⁻¹ z

theorem bracket_mul_unit (χ : MulChar F ℂ) (j : ℕ) (z x : F) (hz : z≠0) :
    bracket χ j (z*x)=unitArgumentFactor χ j z*bracket χ j x := by
  by_cases hj4 : j=4
  · simp [unitArgumentFactor,bracket,hj4,hz]
  · by_cases hj0 : j=0
    · subst j
      simp only [unitArgumentFactor,bracket,show (0:ℕ)≠4 by decide,ite_false,ite_true,
        zero_add,map_mul]
      ring
    · simp only [unitArgumentFactor,bracket,if_neg hj4,if_neg hj0,map_mul]

theorem unitArgumentFactor_norm (χ : MulChar F ℂ) (j : ℕ) (z : F) (hz : z≠0) :
    ‖unitArgumentFactor χ j z‖=1 := by
  by_cases hj : j=4
  · simp [unitArgumentFactor,hj]
  · rw [unitArgumentFactor,if_neg hj]
    exact FiniteRayExpansion.norm_char_unit ((χ^(j+2))⁻¹) (Units.mk0 z hz)

end LocalReflectionBrackets
namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets

theorem unit_ramified_quotient_ne_zero (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (u : Oˣ) (m : ℕ) :
    Ideal.Quotient.mk P ((u:O)*lambda^m)≠0 := by
  rw [map_mul,map_pow]
  apply mul_ne_zero
  · exact (u.isUnit.map (Ideal.Quotient.mk P)).ne_zero
  · exact pow_ne_zero _ (fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h))


end CompletedGauss

namespace InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical


open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem positive_nested_density_bound (f : Frequency → ℝ) (C : ℝ)
    (hf : ∀ q, 0 ≤ f q)
    (hbound : ∀ q, f q ≤ C*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x,y,z)) ≤
      C*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  let I := ∫ t : ℝ,firstLogDensity 0 t
  have hz (x y : ℝ) : (∫ z : ℝ,f (x,y,z)) ≤
      C*firstLogDensity 0 x*firstLogDensity 0 y*I := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z : ℝ => hf (x,y,z)))
      ((firstLogDensity_integrable 0).const_mul (C*firstLogDensity 0 x*firstLogDensity 0 y))
      (Filter.Eventually.of_forall (fun z : ℝ => hbound (x,y,z)))
    simpa only [integral_const_mul,I] using h
  have hy (x : ℝ) : (∫ y : ℝ, ∫ z : ℝ,f (x,y,z)) ≤ C*firstLogDensity 0 x*I*I := by
    have h := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))
      (((firstLogDensity_integrable 0).const_mul (C*firstLogDensity 0 x)).mul_const I)
      (Filter.Eventually.of_forall (hz x))
    simpa only [integral_mul_const,integral_const_mul,I] using h
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => integral_nonneg
      (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z)))))
    ((((firstLogDensity_integrable 0).const_mul C).mul_const I).mul_const I)
    (Filter.Eventually.of_forall hy)
  simp only [integral_mul_const,integral_const_mul] at h
  convert! h using 1 ; dsimp [I] ; ring

theorem polynomial_density_cost (B G : Frequency → ℝ) (J : ℕ) (S C E : ℝ)
    (hS : 0 < S) (hC : 0 ≤ C) (_hE : 0 ≤ E)
    (hB : ∀ q, 0 ≤ B q) (hG : ∀ q, 0 ≤ G q)
    (hdec : ∀ q, S*B q ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*G (x,y,z)) ≤
      (C*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  apply positive_nested_density_bound _ (C*E/S)
    (fun q => mul_nonneg (hB q) (hG q))
  intro q
  have hc : 0 ≤ C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (firstLogDensity_nonneg _ _))
      (firstLogDensity_nonneg _ _)) (firstLogDensity_nonneg _ _)
  have hb := mul_le_mul (hdec q) (henergy q) (hG q) hc
  have heq :
      (C*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)*
        (E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) =
      C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2 := by
    rw [←density_weight_identity J q.1,←density_weight_identity J q.2.1,
      ←density_weight_identity J q.2.2]
    ring
  rw [heq] at hb
  calc
    _ ≤ (C*E*firstLogDensity 0 q.1*firstLogDensity 0 q.2.1*firstLogDensity 0 q.2.2)/S := by
      apply (le_div_iff₀ hS).mpr
      convert! hb using 1 ; ring
    _ = _ := by ring


end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma blockRow_mul (S : Finset ι) (e : ι→ℕ) (a b:O) :
    blockRow p hg S e (a*b)=blockRow p hg S e a*blockRow p hg S e b := by
  simp only [blockRow_eq_product,map_mul,Finset.prod_mul_distrib]

omit [DecidableEq ι] in
lemma blockRow_unit_mul_star (S : Finset ι) (e : ι→ℕ) (u:Oˣ) :
    blockRow p hg S e (u:O)*star (blockRow p hg S e (u:O))=1 := by
  exact GaussGeneratorTransport.finiteSexticRow_unit_mul_star
    (fun i:S=>Ideal.span {p i.val}) (fun i=>hg i.val) (fun i=>e i.val) u

omit [DecidableEq ι] in
lemma originalLabelColumn_unit_c (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (C : Finset ι→ℂ) (u c f : O) (S : Finset ι) :
    originalLabelColumn p hg B ε₁ ε₂ negative C (u*c) f S =
      originalLabelColumn p hg B ε₁ ε₂ negative C c f S*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u^4 := by
  simp only [originalLabelColumn,finiteSquarefreeRow_mul,mul_pow]
  ring

omit [DecidableEq ι] in
lemma row_four_eq_star_square (S : Finset ι) (u:O) :
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u^4=
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S (u^2)) := by
  have h1 : finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simpa only [h1,star_one,mul_one,one_mul] using
    row_four_star (fun i=>Ideal.span {p i}) hg S u 1

theorem threeGaussRowFactor_common_unit
    (N P B : Finset ι) (hNP:Disjoint N P) (hNB:Disjoint N B) (hPB:Disjoint P B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ) (u:Oˣ) (c f d h:O) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) d h =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) d ((u:O)^2*h) := by
  have hU:=blockRow_unit_mul_star p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) (u^2)
  simp only [Units.val_pow_eq_pow_val] at hU
  simp only [threeGaussRowFactor,originalLabelColumn_unit_c,row_four_eq_star_square,
    star_mul,star_star,blockRow_mul]
  rw [threeBlockRow_factor p hg N P B hNP hNB hPB v ε₁ ε₂ ((u:O)^2)]
  simp only [star_mul,star_star]
  let a : ℂ := threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
    (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
    (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) d h *
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg N ((u:O)^2) *
    star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg P ((u:O)^2))
  convert! congrArg (fun z:ℂ=>a*z) hU.symm using 1 <;>
    simp only [a,threeGaussRowFactor,star_mul] <;> ring

theorem actualFirstKernel_common_unit (F B : Finset ι) (hFB:Disjoint F B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ) (X₁ X₂ K:ℝ) (u:Oˣ) (c f d h:O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) W V₁ V₂ X₁ X₂ K d h =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d ((u:O)^2*h) := by
  have hn : ‖eisEmbedding ((u:O)^2*h)‖=‖eisEmbedding h‖ := by
    rw [map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,one_mul]
  simp only [actualFirstKernel,Finset.mul_sum,hn]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP:Disjoint N P
  · simp only [hNP,ite_true]
    rw [threeGaussRowFactor_common_unit p hp hcop hg N P B hNP
      (hFB.mono_left (Finset.mem_powerset.mp hN)) (hFB.mono_left (Finset.mem_powerset.mp hP))
      v ε₁ ε₂ C₁ C₂ u c f d h]
    ring
  · simp only [hNP,ite_false,mul_zero]

omit [DecidableEq ι] in
theorem commonUnitPhase_norm (B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (u:Oˣ) :
    ‖blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)‖=1 := by
  have h:=blockRow_unit_mul_star p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) (u^2)
  have hn:=congrArg norm h
  simp only [norm_mul,norm_star,norm_one,Units.val_pow_eq_pow_val] at hn
  nlinarith [norm_nonneg (blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2))]

def unitSquareRowEquiv (u:Oˣ) : O≃O where
  toFun h := (u:O)^2*h
  invFun h := ((u⁻¹:Oˣ):O)^2*h
  left_inv h := by
    dsimp only
    rw [←mul_assoc,←mul_pow]
    simp
  right_inv h := by
    dsimp only
    rw [←mul_assoc,←mul_pow]
    simp

theorem tsum_actualFirstKernel_common_unit (F B:Finset ι) (hFB:Disjoint F B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ) (X₁ X₂ K:ℝ) (u:Oˣ) (c f d:O) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) W V₁ V₂ X₁ X₂ K d h) =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    ∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d h := by
  let F₀ : O→ℂ := actualFirstKernel p hp hcop hg F B v ε₁ ε₂
    (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
    (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d
  let q := blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)
  calc
    _ = ∑'h:O,q*F₀ ((u:O)^2*h) := by
      apply tsum_congr
      intro h
      exact actualFirstKernel_common_unit p hp hcop hg F B hFB v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K u c f d h
    _ = q*∑'h:O,F₀ ((u:O)^2*h) := tsum_mul_left
    _ = q*∑'h:O,F₀ h := by
      exact congrArg (fun z:ℂ=>q*z) ((unitSquareRowEquiv u).tsum_eq F₀)

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

lemma blockRow_at_zero (S:Finset ι) (e:ι→ℕ) :
    blockRow p hg S e 0=if S=∅ then 1 else 0 := by
  by_cases hS:S=∅
  · simp [hS,blockRow_eq_product]
  · rw [if_neg hS,blockRow_eq_product]
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero hi
    simp only [map_zero,MulChar.map_zero]

lemma threeGaussRowFactor_zero_nonempty
    (N P B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (d:O)
    (hne:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d 0=0 := by
  simp only [threeGaussRowFactor,blockRow_at_zero,if_neg hne,star_zero,mul_zero]

theorem actualFirstKernel_zero
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (d:O) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d 0 =
      if cubeActiveSupport B v ε₁ ε₂=∅ then
        (V₁ (columnLog p X₁ ∅)*V₂ (columnLog p X₂ ∅))*(K:ℂ)*paperRadialFourier W 0*
          threeGaussRowFactor p hp hcop hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d 0 else 0 := by
  unfold actualFirstKernel
  by_cases hB:cubeActiveSupport B v ε₁ ε₂=∅
  · rw [if_pos hB,Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single ∅]
      · simp only [Finset.disjoint_empty_left,ite_true,Finset.empty_union,hB,
          Finset.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,map_zero,norm_zero,
          zero_pow (by decide:2≠0),mul_zero,zero_div]
      · intro P hP hP0
        have hn:(∅∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by simpa only [Finset.empty_union,hB,Finset.union_empty] using hP0
        simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg ∅ P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
      · simp
    · intro N hN hN0
      apply Finset.sum_eq_zero
      intro P hP
      have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
        intro he
        exact hN0 (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
          have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_left _ (Finset.mem_union_left _ hi)
          simp only [he, Finset.notMem_empty] at this))
      simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
    · simp
  · rw [if_neg hB]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro P hP
    have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
      intro he
      exact hB (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
        have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_right _ hi
        simp only [he, Finset.notMem_empty] at this))
    simp only [threeGaussRowFactor_zero_nonempty p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]

theorem actualFirstKernel_truncate
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (hK:0<K) (d:O) (hd:d≠0) (T:Finset O) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)=
      (∑h∈T,actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h)+
      ∑'h:{h:O//h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val := by
  exact (actualFirstKernel_summable p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).sum_add_tsum_subtype_compl T |>.symm

end FirstPassCubeLabels

end

end OAI

end


