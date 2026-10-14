-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0137_parallel2
-- name    : PNT_ZeroFree_433_0137_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:39:50.077581+00:00
-- url     : https://prove2.me/theorems/ae53289f-f433-4278-a2e1-8c7fc149fddc
-- title:
--   Zero-free region foundations: QuadraticSieve.PoissonConstants [0137_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonConstants
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonConstants.lean#L138-L342

import Definitions.Def_PNT_ZeroFree_433_0137_parallel2_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonConstants.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson


theorem poissonUnitBudget_power_envelope
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (G : Ideal O) (hG : G≠0) (K N P D H : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 1≤K) (hN : 1≤N) (hP : 1≤P) (hD : 1≤D) (hH : 1≤H)
    (hconst : ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, x≤H)
    (hscales : ∀x∈([(Ideal.absNorm G:ℝ), K,N,(2*K)*N,N*N,
      (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ), 0≤x ∧ x≤D*P^4) :
    ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp η hη η hη G K N W,
      0≤x ∧ x≤(H*P^(4*η))^8 := by
  let V := H*P^(4*η)
  have hP0 : 0<P := by linarith
  have hR : 1≤P^(4*η) := Real.one_le_rpow hP (by positivity)
  have hV : 1≤V := by dsimp [V]; nlinarith
  have hCV (x : ℝ)
      (hx : x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W) :
      0≤x ∧ x≤V := by
    refine ⟨poissonPrimitiveConstants_nonneg sD sS sT CD CS CT CP hCD hCS hCT hCP
      hexp η hη D (by linarith) W x hx, ?_⟩
    have hh := hconst x hx
    dsimp [V]
    nlinarith
  have hpow (x : ℝ)
      (hx : x∈([(Ideal.absNorm G:ℝ),K,N,(2*K)*N,N*N,
        (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ)) : 0≤x^η ∧ x^η≤V := by
    have hx0 := (hscales x hx).1
    refine ⟨Real.rpow_nonneg hx0 _, ?_⟩
    have hDpow : D^η≤H := hconst _ (by simp [poissonPrimitiveConstants])
    calc
      _ ≤ (D*P^4)^η := Real.rpow_le_rpow hx0 (hscales x hx).2 hη.le
      _ = D^η*P^(4*η) := by
        rw [Real.mul_rpow (by linarith : 0≤D) (by positivity : 0≤P^4)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
      _ ≤ V := mul_le_mul_of_nonneg_right hDpow (by positivity)
  let prims := poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W ++
    [(Ideal.absNorm G:ℝ)^η,K^η,N^η,((2*K)*N)^η,(N*N)^η,
      ((Ideal.absNorm G:ℝ)*(N*N))^η,(K*N)^η]
  have hprims : ∀x∈prims, 0≤x ∧ x≤V := by
    intro x hx
    simp only [prims,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hCV x hx
    all_goals exact hpow _ (by simp)
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈prims) (hn : xs.length≤8) : xs.prod≤V^8 :=
    list_prod_budget xs prims V hV hprims hx hn
  have hp1 (x : ℝ) (hx : x∈prims) : x≤V^8 := by
    simpa using hp [x] (by simpa using hx) (by simp)
  intro x hx
  simp only [poissonUnitBudget,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨by positivity, ?_⟩
    apply ((IdealDivisorBound.ideal_divisor_small_power η hη).choose_spec.2 G hG).trans
    have hh := hp [divisorConstant η hη,(Ideal.absNorm G:ℝ)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength K+1:ℕ) ≤ (2+1/(η*Real.log 2))*K^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη K hK).trans
    have hh := hp [2+1/(η*Real.log 2),K^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength N+1:ℕ) ≤ (2+1/(η*Real.log 2))*N^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη N hN).trans
    have hh := hp [2+1/(η*Real.log 2),N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [256,supportConstant η hη,divisorConstant η hη,N^η,N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [divisorExponentConstant hexp η hη,((2*K)*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖quadraticTransformedSquareProfile W 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨dualMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [dualMiddleDecayConstant (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨originalMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [originalMiddleDecayConstant (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨nonzeroLatticeEnvelopeConstant_nonneg, ?_⟩
    have hh := hp [nonzeroLatticeEnvelopeConstant] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,(N*N)^η,CD,sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,((Ideal.absNorm G:ℝ)*(N*N))^η,CS,sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [CT,sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,N^η,CP,(K*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh

end


end CanonicalQuadraticSieve

end

end OAI

end


