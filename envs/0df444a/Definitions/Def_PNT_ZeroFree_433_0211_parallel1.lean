-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0211_parallel1
-- name    : PNT_ZeroFree_433_0211_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:09:10.079676+00:00
-- url     : https://prove2.me/theorems/edfda884-e286-4b33-91b6-a907630a9451
-- title:
--   Zero-free region foundations: RowCompletion.ThetaNonvanishing [0211_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.ThetaNonvanishing
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/ThetaNonvanishing.lean#L85-L548

import Definitions.Def_PNT_ZeroFree_433_0005
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0010
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0025
import Definitions.Def_PNT_ZeroFree_433_0026
import Definitions.Def_PNT_ZeroFree_433_0027
import Definitions.Def_PNT_ZeroFree_433_0028
import Definitions.Def_PNT_ZeroFree_433_0033
import Definitions.Def_PNT_ZeroFree_433_0046
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0117
import Definitions.Def_PNT_ZeroFree_433_0117_1
import Definitions.Def_PNT_ZeroFree_433_0118
import Definitions.Def_PNT_ZeroFree_433_0122
import Definitions.Def_PNT_ZeroFree_433_0128
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0152_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel2
import Definitions.Def_PNT_ZeroFree_433_0182_parallel1
import Definitions.Def_PNT_ZeroFree_433_0203_parallel1
import Definitions.Def_PNT_ZeroFree_433_0209_parallel1
import Definitions.Def_PNT_ZeroFree_433_0210
import Definitions.Def_PNT_ZeroFree_433_0235_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/ThetaNonvanishing.lean
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
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical ContDiff Topology
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open ShortDraftHeckeBridge
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open SixthPowerAverage CompactMellinBridge InitialMeanSquare

theorem corrected_weighted_mellin_identity {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal ActualEisensteinCubic.O))
    (hS : ∀P∈S,Prime P) (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : ∀x,x≤1 ∨ 2≤x→W x=0) (s : ℂ) (hRe : 2<s.re) :
    (χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        mellin (fun Z : ℝ=>weightedCompactSum χ S W Z⁻¹) (-s))=
      mellin W s := by
  rw [weightedCompactMellin_eq_series χ S W hW hs s hRe]
  have hc:=SmoothMobiusCorrection.full_LSeries_correction χ S hS s hRe
  have hp:=normFiber_LSeries_eq_pair_inverse χ (baseChangeChar χ) (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s
  have he:=pair_inverse_euler_identity χ (baseChangeChar χ) s (by linarith : 1<s.re)
  rw [←hp,hc] at he
  calc
    _=((χ.LFunction s*(baseChangeChar χ).LFunction s)*
      ((finiteEulerFactor χ S s*SmoothMobiusCorrection.eulerCorrection χ S s)*
        LSeries (weightedCoeff χ S) s))*mellin W s := by ring
    _=mellin W s := by rw [he,one_mul]


end CanonicalRowCompletion

open scoped BigOperators Classical
namespace QuadraticAllOddCRT

section
open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega
open CanonicalQuadraticSieve hiding O

local instance p2mAnonymous_PNT_ZeroFree_433_0211_parallel1_1 : (Ideal.span {lambda} : Ideal ActualEisensteinCubic.O).IsMaximal:=lambdaIdeal_maximal

lemma lambda_odd : ringChar (ActualEisensteinCubic.O⧸Ideal.span {lambda})≠2:=
  ActualEisensteinSieve.lambda_residue_odd

lemma lambda_residue : residue lambda=((3:ZMod 4),(1:ZMod 4)) := by
  have h : lambda=eval (-1) 1 := by
    change (ActualEisensteinCubic.omega-1:ActualEisensteinCubic.O)=((-1:ℤ):ActualEisensteinCubic.O)+((1:ℤ):ActualEisensteinCubic.O)*ActualEisensteinCubic.omega
    push_cast
    ring
  rw [h,residue_eval]
  decide


lemma character_lambda_primary (p : ActualEisensteinCubic.O) (hp : lambda^2∣p-1) :
    character (Ideal.span {lambda}) (Ideal.Quotient.mk (Ideal.span {lambda}) p)=1 := by
  have hm : Ideal.Quotient.mk (Ideal.span {lambda}) p=Ideal.Quotient.mk (Ideal.span {lambda}) (1:ActualEisensteinCubic.O) :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
      ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans hp))
  rw [hm,map_one,map_one]

def lambdaQuadraticRay (r : EisensteinEPrimaryPhase.Coord) : ℂ:=
  quadraticRayValue (EisensteinEPrimaryPhase.mul (residue lambda) r)/
    (quadraticRayValue (residue lambda)*quadraticRayValue r)


end

open ActualEisensteinCubic
open QuadraticGaussRay hiding O
open ActualEisensteinCoordinates hiding O omega

def lambdaQuadraticTable (r : EisensteinEPrimaryPhase.Coord) : ℤ :=
  if ¬EisensteinEPrimaryPhase.odd r then 0
  else if r∈({(0,1),(1,0),(1,2),(1,3),(2,3),(3,3)} : Finset EisensteinEPrimaryPhase.Coord)
    then 1 else -1

lemma lambdaQuadraticTable_mul (r s : EisensteinEPrimaryPhase.Coord) :
    lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
      lambdaQuadraticTable r*lambdaQuadraticTable s := by
  have h : ∀r s : EisensteinEPrimaryPhase.Coord,
      lambdaQuadraticTable (EisensteinEPrimaryPhase.mul r s)=
        lambdaQuadraticTable r*lambdaQuadraticTable s := by decide
  exact h r s

lemma lambdaQuadraticTable_eq_ray (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    (lambdaQuadraticTable r:ℂ)=lambdaQuadraticRay r := by
  have hcmp (a b : ZMod 4) : (a=b) ↔ (a.val=b.val) :=
    (ZMod.val_injective 4).eq_iff.symm
  have hn3 : (-3 : ZMod 4) = 1 := by decide
  rcases r with ⟨a,b⟩
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rcases hcases a with rfl | rfl | rfl | rfl <;>
    rcases hcases b with rfl | rfl | rfl | rfl <;>
    norm_num [EisensteinEPrimaryPhase.odd,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat] at hr <;>
    norm_num [lambdaQuadraticTable,lambdaQuadraticRay,lambda_residue,EisensteinEPrimaryPhase.mul,
      EisensteinEPrimaryPhase.odd,quadraticRayValue,breveGaussianFourTerms_formula,
      Prod.mk.injEq,hcmp,hn3,ZMod.val_zero,ZMod.val_one_eq_one_mod,ZMod.val_ofNat,
      ZMod.val_neg_one,ZMod.val_mul,ZMod.val_add,ZMod.val_sub,
      Complex.I_sq,Complex.I_pow_three,Complex.inv_I,zpow_neg] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_three]
  all_goals
    field_simp [Complex.I_ne_zero]
    change (-2 : ℂ) = Complex.I * (Complex.I ^ (1 : ℤ) + Complex.I ^ (2 - 1 : ℤ))
    norm_num [Complex.I_sq]
    ring_nf
    norm_num [Complex.I_sq]

def lambdaQuadraticCharacter : ActualEisensteinCubic.O→*ℂ where
  toFun n:=(lambdaQuadraticTable (residue n):ℂ)
  map_one' := by
    have h : residue (1:ActualEisensteinCubic.O)=((1:ZMod 4),0):=by
      have h1 : (1:ActualEisensteinCubic.O)=eval 1 0:=by simp [eval]
      rw [h1,residue_eval]
      norm_num
    rw [h]
    exact_mod_cast (show lambdaQuadraticTable ((1:ZMod 4),0)=1 from by decide)
  map_mul' x y := by
    rw [residue_mul,lambdaQuadraticTable_mul]
    push_cast
    rfl

lemma lambdaQuadraticCharacter_periodic (x y : ActualEisensteinCubic.O) (h : (4:ActualEisensteinCubic.O)∣x-y) :
    lambdaQuadraticCharacter x=lambdaQuadraticCharacter y := by
  change (lambdaQuadraticTable (residue x):ℂ)=(lambdaQuadraticTable (residue y):ℂ)
  rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub x y h]

end QuadraticAllOddCRT

open scoped BigOperators Classical
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open CubicJacobiGlobal hiding O
open QuadraticAllOddCRT
open CanonicalQuadraticSieve hiding O
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma localRowValue_square (x : ActualEisensteinCubic.O) (P : Ideal ActualEisensteinCubic.O) :
    localRowValue x P^2=eisEmbedding (primeValue P x) := by
  unfold localRowValue primeValue
  split_ifs with h
  · let : P.IsMaximal:=h.1
    change (actualSextic P h.2 (Ideal.Quotient.mk P x))^2=_
    rw [←MulChar.pow_apply' _ (by decide : (2:ℕ)≠0),canonicalSextic_pow_two]
    rfl
  · simp

theorem idealRowHom_square (x : ActualEisensteinCubic.O) (I : Ideal ActualEisensteinCubic.O) :
    idealRowHom x I^2=eisEmbedding (idealSymbol I x) := by
  have hm (s : Multiset (Ideal ActualEisensteinCubic.O)) :
      (s.map (localRowValue x)).prod^2=eisEmbedding ((s.map (fun P=>primeValue P x)).prod) := by
    induction s using Multiset.induction_on with
    | empty=>simp
    | @cons P s ih=>
      simp only [Multiset.map_cons,Multiset.prod_cons,mul_pow,map_mul,localRowValue_square,ih]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,idealSymbol_zero,zero_pow (by decide : (2:ℕ)≠0)]
  · change (if I=0 then 0 else _)^2=eisEmbedding (if I=0 then 0 else _)
    simp only [if_neg hI]
    exact hm _

lemma actualSextic_cube_quadratic (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P) :
    actualSextic P hg^3=character P := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ,hχ3⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧
      χ^3=(quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ActualEisensteinCubic.O) :=
    ⟨_,rfl,(sexticChar_powers P hg).2.1⟩
  rw [hχ,MulChar.ringHomComp_pow,hχ3]
  ext x
  change eisEmbedding ((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ActualEisensteinCubic.O)=((quadraticChar (ActualEisensteinCubic.O⧸P) x:ℤ):ℂ)
  simp


end CanonicalRowCompletion

namespace CubicEisenstein


open Filter
open scoped BigOperators Classical Topology ContDiff

def weightedHeightProfile (F : ℝ→ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) p)

lemma weightedHeightProfile_axis_differentiable (F : ℝ→ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (r : CuspCosets)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (weightedHeightProfile F r) p j) (p j) :=
  ((rowProfile_axis_derivatives F hF (embeddedRow r) (embeddedRow_ne_zero r) p hp j).1.const_mul _).differentiableAt

lemma heightPoincare_axis_termwise (F : ℝ→ℂ) (hzero : ∀v≤1,F v=0)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    Summable (fun r => deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) ∧
    HasDerivAt (axisSlice (heightPoincareField F) p j)
      (∑'r,deriv (axisSlice (weightedHeightProfile F r) p j) (p j)) (p j) := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [ContinuousAt,Function.update_eq_self] using
      ((continuous_axis_update p j).continuousAt (x := p j))
  have hn : ∀ᶠt in 𝓝 (p j),Function.update p j t∈U := ht (hU.mem_nhds hpU)
  have hz (r : CuspCosets) (hr : r∉S) :
      deriv (axisSlice (weightedHeightProfile F r) p j) (p j)=0 := by
    have he : axisSlice (weightedHeightProfile F r) p j=ᶠ[𝓝 (p j)] (fun _ => 0) := by
      filter_upwards [hn] with t ht
      change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
      rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]
    exact he.deriv_eq.trans (deriv_const _ _)
  refine ⟨summable_of_ne_finset_zero hz,?_⟩
  rw [tsum_eq_sum hz]
  have hd := HasDerivAt.sum (u := S) (fun r hr =>
    (weightedHeightProfile_axis_differentiable F hF r p hp j).hasDerivAt)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  simp only [Finset.sum_apply]
  change (∑'r,weightedHeightProfile F r (Function.update p j t))=
    ∑r∈S,weightedHeightProfile F r (Function.update p j t)
  apply tsum_eq_sum
  intro r hr
  change (cosetCharacter r)⁻¹*F (rowHeight (embeddedRow r) (Function.update p j t))=0
  rw [hzero _ ((hrows _ ht).2 r hr).le,mul_zero]


def eisensteinRemainderField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  smoothEisenstein s p-smoothCuspSeedField a b s p


end CubicEisenstein


end

end OAI

end


