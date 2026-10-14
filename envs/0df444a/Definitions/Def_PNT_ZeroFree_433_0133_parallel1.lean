-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0133_parallel1
-- name    : PNT_ZeroFree_433_0133_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:18:27.955494+00:00
-- url     : https://prove2.me/theorems/d8c9c0ca-447d-450d-a399-54e173d92f3b
-- title:
--   Zero-free region foundations: QuadraticSieve.GlobalBinLoss [0133_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.GlobalBinLoss
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/GlobalBinLoss.lean#L76-L621

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0109_1
import Definitions.Def_PNT_ZeroFree_433_0160_parallel1
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0286_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/GlobalBinLoss.lean
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

namespace CanonicalQuadraticSieve

theorem list_prod_le_power (xs : List ℝ) (U : ℝ) (hU : 0≤U)
    (hxs : ∀x∈xs, 0≤x ∧ x≤U) : xs.prod≤U^xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀y∈xs, 0≤y ∧ y≤U := fun y hy => hxs y (by simp [hy])
    simp only [List.prod_cons,List.length_cons,pow_succ]
    have hp : 0≤xs.prod := List.prod_nonneg (fun y hy => (ht y hy).1)
    exact (mul_le_mul hx.2 (ih ht) hp hU).trans_eq (mul_comm _ _)

theorem list_prod_budget (xs budget : List ℝ) (U : ℝ) (hU : 1≤U)
    (hbudget : ∀x∈budget, 0≤x ∧ x≤U) (hxs : ∀x∈xs, x∈budget) (hlen : xs.length≤8) :
    xs.prod≤U^8 := by
  apply (list_prod_le_power xs U (by linarith) (fun x hx => hbudget x (hxs x hx))).trans
  exact pow_le_pow_right₀ hU hlen

theorem poisson_nine_terms_box
    (d lk ln f e vh vz dv uh du lat cd cs ct cp M N T a b eD eS tail U S : ℝ)
    (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈([d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp] : List ℝ), 0≤x ∧ x≤U)
    (hM : 0≤M) (hN : 0≤N) (hT : 1≤T) (ha : 0≤a)
    (hMS : M≤S) (hNS : N≤S) (hTa : T*a≤S)
    (hb : 0≤b ∧ b≤S) (hED : 0≤eD ∧ eD≤S) (hES : 0≤eS ∧ eS≤S)
    (htail : 0≤tail ∧ tail≤S) :
    d*lk*(8*vh*ln^2*f*e*(M+a) + 8*vz*ln^2*f*e*(M+2*T*a) +
      8*ln^2*lat*dv*f*e*(M+2*T*a) + 65536*cd*eD) +
    1536*d*ct*tail +
    lk*(2*uh*d*ln^2*f*e*(4*N/T+a) + 2*d*ln^2*lat*du*f*e*(N+2*T*a) +
      32768*cs*eS) + uh*d^2*cp*b ≤ 262144*U^8*S := by
  let budget : List ℝ := [d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp]
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈budget) (hn : xs.length≤8) : xs.prod≤U^8 :=
    list_prod_budget xs budget U hU hbudget hx hn
  have hc1 : d*lk*vh*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vh,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc2 : d*lk*vz*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vz,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc3 : d*lk*ln^2*lat*dv*f*e≤U^8 := by
    have hh := hp [d,lk,ln,ln,lat,dv,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc4 : d*lk*cd≤U^8 := by
    have hh := hp [d,lk,cd] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc5 : d*ct≤U^8 := by
    have hh := hp [d,ct] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc6 : lk*uh*d*ln^2*f*e≤U^8 := by
    have hh := hp [lk,uh,d,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc7 : lk*d*ln^2*lat*du*f*e≤U^8 := by
    have hh := hp [lk,d,ln,ln,lat,du,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc8 : lk*cs≤U^8 := by
    have hh := hp [lk,cs] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc9 : uh*d^2*cp≤U^8 := by
    have hh := hp [uh,d,d,cp] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have haS : a≤S := (by nlinarith only [ha, hT] : a≤T*a).trans hTa
  have hdiv : N/T≤N := div_le_self hN hT
  have h1 : M+a≤2*S := by linarith only [hMS, haS]
  have h2 : M+2*T*a≤3*S := by nlinarith only [hMS, hTa]
  have h3 : M+2*T*a≤3*S := h2
  have h6 : 4*N/T+a≤5*S := by rw [mul_div_assoc]; linarith only [hdiv, hNS, haS]
  have h7 : N+2*T*a≤3*S := by nlinarith only [hNS, hTa]
  have hU8 : 0≤U^8 := by positivity
  have ht1 := mul_le_mul hc1 h1 (by positivity : 0≤M+a) hU8
  have ht2 := mul_le_mul hc2 h2 (by positivity : 0≤M+2*T*a) hU8
  have ht3 := mul_le_mul hc3 h3 (by positivity : 0≤M+2*T*a) hU8
  have ht4 := mul_le_mul hc4 hED.2 hED.1 hU8
  have ht5 := mul_le_mul hc5 htail.2 htail.1 hU8
  have ht6 := mul_le_mul hc6 h6 (by positivity : 0≤4*N/T+a) hU8
  have ht7 := mul_le_mul hc7 h7 (by positivity : 0≤N+2*T*a) hU8
  have ht8 := mul_le_mul hc8 hES.2 hES.1 hU8
  have ht9 := mul_le_mul hc9 hb.2 hb.1 hU8
  nlinarith only [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, mul_nonneg hU8 hS]

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonUnitBudget
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [(IdealMobiusDivisorSum.idealDivisors G).card,
   (columnDyadicLength K+1:ℕ), (columnDyadicLength N+1:ℕ),
   256*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2,
   divisorExponentConstant hexp deltaLoss hδ*((2*K)*N)^deltaLoss,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant,
   supportConstant ε hε*(N*N)^ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)),
   supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)),
   CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W,
   supportConstant ε hε*N^ε*CP*(K*N)^deltaLoss]


end CanonicalQuadraticSieve

open scoped BigOperators Classical


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

namespace CubicEisenstein

def matrixGram (g : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ)*star (g : Matrix (Fin 2) (Fin 2) ℂ)

lemma matrixGram_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixGram (g*k)=matrixGram g := by
  have hku : (k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ)=1 :=
    Matrix.mem_unitaryGroup_iff.mp hk
  unfold matrixGram
  simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
  calc
    _ = (g : Matrix (Fin 2) (Fin 2) ℂ)*
        ((k : Matrix (Fin 2) (Fin 2) ℂ)*star (k : Matrix (Fin 2) (Fin 2) ℂ))*
        star (g : Matrix (Fin 2) (Fin 2) ℂ) := by noncomm_ring
    _ = _ := by rw [hku]; simp

def hyperbolicGram : HyperbolicSpace → Matrix (Fin 2) (Fin 2) ℂ :=
  Quotient.lift matrixGram (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixGram_right_unitary g (g⁻¹*h) hk).symm)


lemma hyperbolicGram_injective : Function.Injective hyperbolicGram := by
  intro w w' hw
  induction w using Quotient.inductionOn with | _ g =>
    induction w' using Quotient.inductionOn with | _ h =>
      change matrixGram g=matrixGram h at hw
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      change (g⁻¹*h:SL(2,ℂ))∈compactSubgroup
      apply Matrix.mem_unitaryGroup_iff.mpr
      have hgi : ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*
          (g:Matrix (Fin 2) (Fin 2) ℂ)=1 :=
        congrArg (fun x : SL(2,ℂ) => (x:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel g)
      have hgis : star (g:Matrix (Fin 2) (Fin 2) ℂ)*
          star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)=1 := by
        simpa only [star_mul,star_one] using congrArg star hgi
      simp only [Matrix.SpecialLinearGroup.coe_mul,star_mul]
      calc
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram h*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by unfold matrixGram; noncomm_ring
        _ = ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*matrixGram g*
            star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) := by rw [hw]
        _ = (((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(g:Matrix (Fin 2) (Fin 2) ℂ))*
            (star (g:Matrix (Fin 2) (Fin 2) ℂ)*star ((g⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)) := by
          unfold matrixGram
          noncomm_ring
        _ = 1 := by rw [hgi,hgis]; simp


def complexMatrixRow (g : SL(2,ℂ)) (i : Fin 2) : Fin 2 → ℂ := fun j => g i j

lemma complexMatrixRow_mul (g h : SL(2,ℂ)) (i : Fin 2) :
    complexMatrixRow (g*h) i=rowOperator h (complexMatrixRow g i) := by
  funext j
  simp only [complexMatrixRow,rowOperator_apply,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Matrix.vecMul,dotProduct]

def matrixFrobenius (g : SL(2,ℂ)) : ℝ :=
  rowEnergy (complexMatrixRow g 0)+rowEnergy (complexMatrixRow g 1)

lemma matrixFrobenius_right_unitary (g k : SL(2,ℂ)) (hk : k∈compactSubgroup) :
    matrixFrobenius (g*k)=matrixFrobenius g := by
  simp only [matrixFrobenius,complexMatrixRow_mul,rowEnergy_unitary k hk]

def hyperbolicFrobenius : HyperbolicSpace → ℝ :=
  Quotient.lift matrixFrobenius (by
    intro g h hgh
    have hk : g⁻¹*h∈compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h=g*(g⁻¹*h) := by group
    rw [hh]
    exact (matrixFrobenius_right_unitary g (g⁻¹*h) hk).symm)


end CubicEisenstein

end

end OAI

end


