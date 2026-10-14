-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0198_parallel1
-- name    : PNT_ZeroFree_433_0198_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:01:41.035377+00:00
-- url     : https://prove2.me/theorems/6bab2c62-c8a1-47f9-99f6-e7fb0c5437b7
-- title:
--   Zero-free region foundations: CubicSieve.CutoffOrders [0198_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.CutoffOrders
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CutoffOrders.lean#L78-L587

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0015
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0068
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/CutoffOrders.lean
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

namespace SecondPassArithmetic

theorem exists_polynomial_cutoff_order (p q η R : ℝ) (hη : 0<η) :
    ∃N : ℕ,0<N ∧ ∀C Z : ℝ,0≤C → 1≤Z →
      (C*Z^p)^q/Z^(η*N)≤C^q*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((p*q+R)/η))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (p*q+R)/η<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : p*q-η*(N:ℝ)≤-R := by
    have hm := (div_lt_iff₀ hη).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro C Z hC hZ
  have hZ0 : 0<Z := by linarith
  calc
    _ = C^q*Z^(p*q-η*N) := by
      rw [Real.mul_rpow hC (by positivity),←Real.rpow_mul hZ0.le,Real.rpow_sub hZ0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (Real.rpow_nonneg hC _)


theorem reopening_terminal_order (η R : ℝ) (hη : 0<η) :
    ∃N : ℕ,0<N ∧ ∀Z Ksrc : ℝ,1≤Z → 0≤Ksrc → Ksrc≤Z^3 →
      (Ksrc/Z^η)/Z^(η*N)≤Z^(-R) := by
  obtain ⟨N,hN,horder⟩ := exists_polynomial_cutoff_order 3 1 η R hη
  refine ⟨N,hN,?_⟩
  intro Z Ksrc hZ hK hKZ
  have hb : Ksrc/Z^η≤Z^3 := (div_le_self hK (Real.one_le_rpow hZ hη.le)).trans hKZ
  have ho : Z^3/Z^(η*N)≤Z^(-R) := by
    have hh := horder 1 Z zero_le_one hZ
    norm_num [Real.rpow_natCast] at hh ⊢
    exact hh
  exact (div_le_div_of_nonneg_right hb (by positivity)).trans ho

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CompletedGauss (actualSextic)
open ConcreteTraceCRT (eisEmbedding)

theorem sixth_roots_reduce_injective (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) {x y : ActualEisensteinCubic.O}
    (hx : x^6=1) (hy : y^6=1)
    (hxy : Ideal.Quotient.mk P x=Ideal.Quotient.mk P y) : x=y := by
  let : Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
  have hs : x^2=y^2 := cubic_roots_reduce_injective P hg
    (by simpa only [←pow_mul] using hx)
    (by simpa only [←pow_mul] using hy)
    (by simpa only [map_pow] using congrArg (fun z : ActualEisensteinCubic.O⧸P=>z^2) hxy)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h|h
  · exact h
  · have hy0 : Ideal.Quotient.mk P y≠0 := by
      intro hz
      have he := congrArg (Ideal.Quotient.mk P) hy
      simp only [map_pow,map_one,hz,zero_pow (by decide : (6:ℕ)≠0)] at he
      exact zero_ne_one he
    have he : -(Ideal.Quotient.mk P y)=Ideal.Quotient.mk P y := by
      simpa only [h,map_neg] using hxy
    have htwo : (2 : ActualEisensteinCubic.O⧸P)*Ideal.Quotient.mk P y=0 := by linear_combination -he
    exact False.elim ((Ring.two_ne_zero hc) ((mul_eq_zero.mp htwo).resolve_right hy0))

lemma unit_pow_six (u : ActualEisensteinCubic.Oˣ) : (u.val : ActualEisensteinCubic.O)^6=1 := by
  have h := pow_card_eq_one' (x:=u)
  rw [PrimaryIdealUnitReindex.card_units_eq_six] at h
  exact congrArg Units.val h

theorem actualSextic_unit_euler (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) (u : ActualEisensteinCubic.Oˣ) :
    actualSextic P hg (Ideal.Quotient.mk P u.val) =
      eisEmbedding (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6)) := by
  let : Field (ActualEisensteinCubic.O⧸P) := Ideal.Quotient.field P
  have hdata : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,
      actualSextic P hg=χ.ringHomComp eisEmbedding ∧ χ^6=1 ∧
      ∀v : (ActualEisensteinCubic.O⧸P)ˣ,Ideal.Quotient.mk P (χ v)=v.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) := by
    refine ⟨_,rfl,(sexticChar_powers P hg).2.2,?_⟩
    exact sexticChar_reduce_unit P hg hc
  obtain ⟨χ,hχ,hχ6,hreduce⟩ := hdata
  let v : (ActualEisensteinCubic.O⧸P)ˣ := Units.map (Ideal.Quotient.mk P).toMonoidHom u
  have hx : χ v.val ^ 6=1 := by
    rw [←MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),hχ6]
    exact MulChar.one_apply v.isUnit
  have hy : (u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6))^6=1 := by
    rw [←pow_mul,Nat.mul_comm, pow_mul,unit_pow_six,one_pow]
  have he : χ v.val=u.val^((Nat.card (ActualEisensteinCubic.O⧸P)-1)/6) :=
    sixth_roots_reduce_injective P hg hc hx hy (by simpa [v] using hreduce v)
  rw [hχ]
  change eisEmbedding (χ v.val)=_
  exact congrArg eisEmbedding he

end CanonicalUnitEuler

namespace CubicEisenstein


open scoped Topology ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ground_state_test_fderiv (f : E → ℂ) (u : E → ℝ) (x v : E)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (hux : u x ≠ 0) :
    fderiv ℝ (fun y => ‖f y‖^2/u y) x v =
      (2*(conj (f x)*fderiv ℝ f x v).re*u x - ‖f x‖^2*fderiv ℝ u x v)/(u x)^2 := by
  have hc : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa only [zero_add,one_smul,Pi.add_apply,id_eq] using!
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v)
  have hx : (fun t : ℝ => x+t•v) 0 = x := by simp
  have hfc : HasDerivAt (fun t : ℝ => f (x+t•v)) (fderiv ℝ f x v) 0 := by
    have hh : HasFDerivAt f (fderiv ℝ f x) (x+(0:ℝ)•v) := by simpa using hf.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have huc : HasDerivAt (fun t : ℝ => u (x+t•v)) (fderiv ℝ u x v) 0 := by
    have hh : HasFDerivAt u (fderiv ℝ u x) (x+(0:ℝ)•v) := by simpa using hu.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have hzero : (fun t : ℝ => u (x+t•v)) 0 ≠ 0 := by simpa using hux
  have hq := hfc.norm_sq.div huc hzero
  have hdiff : DifferentiableAt ℝ (fun y => ‖f y‖^2/u y) x := by
    simpa only [div_eq_mul_inv,Pi.mul_apply,Pi.inv_apply] using! (hf.norm_sq (𝕜 := ℂ)).mul (hu.inv hux)
  have hqc : HasDerivAt (fun t : ℝ => ‖f (x+t•v)‖^2/u (x+t•v))
      (fderiv ℝ (fun y => ‖f y‖^2/u y) x v) 0 := by
    have hh : HasFDerivAt (fun y => ‖f y‖^2/u y)
        (fderiv ℝ (fun y => ‖f y‖^2/u y) x) (x+(0:ℝ)•v) := by simpa using hdiff.hasFDerivAt
    simpa only [Function.comp_def] using! hh.comp_hasDerivAt 0 hc
  have he := hqc.unique hq
  simpa only [zero_smul,add_zero,real_inner_eq_re_inner ℂ,RCLike.inner_apply',RCLike.re_to_complex] using he


end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold
namespace CubicEisenstein

section


open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ComplexConjugate

theorem ground_state_ofReal_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (x v : E) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => (u y : ℂ)) x v = (fderiv ℝ u x v : ℂ) := by
  change fderiv ℝ (Complex.ofRealCLM ∘ u) x v = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt).fderiv]
  rfl

theorem ground_state_self_product (z : ℂ) : (star z*z).re = ‖z‖^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.star_def,Complex.mul_re,
    Complex.conj_re,Complex.conj_im]
  ring


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold


end CubicEisenstein

namespace SecondPassArithmetic

theorem lowerCubeBin_mass_product (X F B : ℝ) (hB : B≠0) :
    B*((X/B^3)*(Real.exp 1*B)^2*F)*((X/B^3)*(Real.exp 1*B)^3*F)=
      Real.exp 5*(X*F)^2 := by
  have he : (Real.exp 1)^5=Real.exp 5 := by
    rw [show (5:ℝ)=1+1+1+1+1 by norm_num]
    simp only [Real.exp_add]
    ring
  simp only [mul_pow]
  rw [←he]
  field_simp

theorem canonicalBudget_sqrt_product (b₁ b₂ D₁ D₂ Q : ℝ)
    (hD₁ : 0≤D₁) (hD₂ : 0≤D₂) (hQ : 0≤Q)
    (h₁ : b₁≤D₁*Q) (h₂ : b₂≤D₂*Q) :
    Real.sqrt b₁*Real.sqrt b₂≤Real.sqrt D₁*Real.sqrt D₂*Q := by
  calc
    _ ≤ Real.sqrt (D₁*Q)*Real.sqrt (D₂*Q) :=
      mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul hD₁,Real.sqrt_mul hD₂]
      calc
        _ = Real.sqrt D₁*Real.sqrt D₂*(Real.sqrt Q*Real.sqrt Q) := by ring
        _ = _ := by rw [Real.mul_self_sqrt hQ]

theorem canonicalPairBudget_normalized
    (X F B Ksrc Kcut Cf cap U power E t D₁ D₂ b₁ b₂ : ℝ) (J : ℕ)
    (hX : 0<X) (hF : 0≤F) (hB : 0<B) (hKsrc : 0≤Ksrc) (hKcut : 0<Kcut)
    (hCf : 0≤Cf) (hcap : 0≤cap) (hU : 0≤U) (hE : 0≤E)
    (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (h₁ : b₁≤D₁*((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J))
    (h₂ : b₂≤D₂*((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J)) :
    B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap*
      Real.sqrt b₁*Real.sqrt b₂)≤
    (Real.exp 5*Cf*Real.sqrt D₁*Real.sqrt D₂)*(X*F)^2*
      (Ksrc/Kcut)*cap*U^power*E*(1+‖t‖)^(2*J) := by
  let Q:=((X/B^3)*(Real.exp 1*B)^3*F)*U^power*E*(1+‖t‖)^(2*J)
  have hQ : 0≤Q := by dsimp only [Q];positivity
  have hs := canonicalBudget_sqrt_product b₁ b₂ D₁ D₂ Q hD₁ hD₂ hQ
    (by simpa only [Q,mul_assoc] using h₁) (by simpa only [Q,mul_assoc] using h₂)
  have hfac : 0≤B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  calc
    _ = (B*(((X/B^3)*(Real.exp 1*B)^2*F)*(Ksrc/Kcut)*Cf*cap))*(Real.sqrt b₁*Real.sqrt b₂) := by ring
    _ ≤ _ := hh
    _ = _ := by
      dsimp only [Q]
      calc
        _ = (B*((X/B^3)*(Real.exp 1*B)^2*F)*((X/B^3)*(Real.exp 1*B)^3*F))*
            ((Ksrc/Kcut)*Cf*cap*Real.sqrt D₁*Real.sqrt D₂*U^power*E*(1+‖t‖)^(2*J)) := by ring
        _ = _ := by rw [lowerCubeBin_mass_product X F B hB.ne'];ring

end SecondPassArithmetic

end

end OAI

end


