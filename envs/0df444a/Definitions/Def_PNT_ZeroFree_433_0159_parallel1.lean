-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0159_parallel1
-- name    : PNT_ZeroFree_433_0159_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:53.315295+00:00
-- url     : https://prove2.me/theorems/97ed0b9e-9f16-4a14-a11b-9646298e1e72
-- title:
--   Zero-free region foundations: CubicSieve.DyadicKernel [0159_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.DyadicKernel
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/DyadicKernel.lean#L127-L522

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0049
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/DyadicKernel.lean
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
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma multiplicityRow_norm_le_one (B : Finset ι) (v : ι→ℕ) (z:O) :
    ‖multiplicityRow (fun i=>Ideal.span {p i}) hg B v z‖≤1 := by
  simp only [multiplicityRow,norm_prod,norm_pow]
  calc
    _ ≤ ∏i∈B,(1:ℝ) := by
      apply Finset.prod_le_prod (fun i hi=>by positivity)
      intro i hi
      apply pow_le_one₀ (norm_nonneg _)
      let : Fintype (O⧸Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by simp

omit [DecidableEq ι] in
lemma multiplicityRow_support (B : Finset ι) (v : ι→₀ℕ) (hv : v.support⊆B) (z:O) :
    multiplicityRow (fun i=>Ideal.span {p i}) hg B v z =
      multiplicityRow (fun i=>Ideal.span {p i}) hg v.support v z := by
  unfold multiplicityRow
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

def reopenedCanonicalRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (z:O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hp hcop hg Ψ m f H S)*
    (multiplicityRow (fun i=>Ideal.span {p i}) hg pool v z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)


end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic

def completedDualScale (X r C K U B : ℝ) (D E : Ideal O) : ℝ :=
  r^3*(Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)^3*U*B^3*X/(K^2*C^2)

theorem positive_log_scale_identity (k n b K U B R : ℝ)
    (hk : 0<k) (hn : 0<n) (hb : 0<b) (hK : 0<K) (hU : 0<U) (hB : 0<B) :
    R*Real.exp (-2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B))=
      R*(K/k)^2*(n/U)*(b/B)^3 := by
  have h2 : Real.exp ((2:ℝ)*Real.log (k/K))=(k/K)^2 := by
    rw [show (2:ℝ)=(2:ℕ) by rfl,Real.exp_nat_mul,Real.exp_log (div_pos hk hK)]
  have h3 : Real.exp ((3:ℝ)*Real.log (b/B))=(b/B)^3 := by
    rw [show (3:ℝ)=(3:ℕ) by rfl,Real.exp_nat_mul,Real.exp_log (div_pos hb hB)]
  rw [show -2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B)=
      -(2*Real.log (k/K))+Real.log (n/U)+3*Real.log (b/B) by ring,
    Real.exp_add,Real.exp_add,Real.exp_neg,h2,h3,Real.exp_log (div_pos hn hU)]
  field_simp

theorem completed_ideal_kernel_scale (X r C K U B : ℝ)
    (D E I J H : Ideal O) (hI : I≠0) (hJ : J≠0) (hH : H≠0)
    (hK : 0<K) (hU : 0<U) (hB : 0<B) :
    completedDualScale X r C K U B D E *
      Real.exp (-2*Real.log ((Ideal.absNorm H:ℝ)/K)+
        Real.log ((Ideal.absNorm I:ℝ)/U)+3*Real.log ((Ideal.absNorm J:ℝ)/B)) =
      r^3*(Ideal.absNorm (D*I):ℝ)*(Ideal.absNorm (E*J):ℝ)^3*X/
        ((Ideal.absNorm H:ℝ)^2*C^2) := by
  have hpos (lengthScale : Ideal O) (hL : lengthScale≠0) : 0<(Ideal.absNorm lengthScale:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hL (Ideal.absNorm_eq_zero_iff.mp hz))
  rw [positive_log_scale_identity _ _ _ _ _ _ _ (hpos H hH) (hpos I hI) (hpos J hJ) hK hU hB]
  simp only [completedDualScale,map_mul,Nat.cast_mul]
  field_simp

end CompletedGauss

open scoped BigOperators
namespace CompletedDyadic

theorem weighted_scale_identity (x t a s : ℝ) (hx : 0<x) (ht : 0<t) :
    x^a*(t*x^3)^(-s)=t^(-s)*x^(a-3*s) := by
  rw [Real.mul_rpow ht.le (pow_nonneg hx.le _),←Real.rpow_natCast_mul hx.le]
  calc
    _ = t^(-s)*(x^a*x^((3:ℝ)*(-s))) := by ring_nf
    _ = _ := by rw [←Real.rpow_add hx]; congr 2; ring


def ramifiedScale (ρ q : ℝ) (m : ℕ) : ℝ := ρ*q^m

theorem ramifiedScale_pos (ρ q : ℝ) (hρ : 0<ρ) (hq : 0<q) (m : ℕ) :
    0<ramifiedScale ρ q m := by unfold ramifiedScale; positivity


def normMajorant (deltaLoss A K t r H U B : ℝ) : ℝ :=
  K^deltaLoss/(r*Real.sqrt H)*
    (Real.sqrt K*B^(deltaLoss-1/2)*U^deltaLoss+B^deltaLoss*U^(deltaLoss+1/2))/(1+t*r^3*B^3*U)^A

theorem normMajorant_nonneg (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    0≤normMajorant deltaLoss A K t r H U B := by unfold normMajorant; positivity

theorem normMajorant_eq (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    normMajorant deltaLoss A K t r H U B =
      (K*(U*B))^deltaLoss*(Real.sqrt K+Real.sqrt U*Real.sqrt B)/
        (Real.sqrt B*r*Real.sqrt H*(1+t*r^3*B^3*U)^A) := by
  unfold normMajorant
  rw [Real.mul_rpow hK.le (mul_pos hU hB).le,Real.mul_rpow hU.le hB.le,
    Real.rpow_sub hB,Real.rpow_add hU,←Real.sqrt_eq_rpow B,←Real.sqrt_eq_rpow U]
  have hsB : Real.sqrt B≠0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  field_simp

theorem smooth_energy_le_normMajorant_sq (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    (K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+t*r^3*B^3*U)^(2*A)
      ≤(normMajorant deltaLoss A K t r H U B)^2 := by
  rw [normMajorant_eq deltaLoss A K t r H U B hK ht hr hH hU hB,div_pow,mul_pow,
    mul_pow,mul_pow,mul_pow,Real.sq_sqrt hB.le,Real.sq_sqrt hH.le]
  have hc : 0≤(K*(U*B))^deltaLoss := by positivity
  have hden : 0<(B*r^2*H)*(1+t*r^3*B^3*U)^(2*A) := by positivity
  have hp (x : ℝ) (hx : 0≤x) (s : ℝ) : (x^s)^2=x^(2*s) := by
    rw [←Real.rpow_mul_natCast hx]
    congr 1
    ring
  rw [hp _ (mul_pos hK (mul_pos hU hB)).le,hp _ (by positivity)]
  rw [div_div]
  apply div_le_div_of_nonneg_right _ hden.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcross : 0≤2*Real.sqrt K*(Real.sqrt U*Real.sqrt B) := by positivity
  nlinarith [Real.sq_sqrt hK.le,Real.sq_sqrt hU.le,Real.sq_sqrt hB.le,
    sq_nonneg (Real.sqrt K+Real.sqrt U*Real.sqrt B)]


end CompletedDyadic

namespace CompletedGauss

theorem finite_tsum_energy_bound {κ α : Type*} [Fintype κ]
    (f : α→κ→ℂ) (g : α→ℝ) (hg0 : ∀i,0≤g i) (hg : Summable g)
    (hbound : ∀i,(∑k,‖f i k‖^2)≤(g i)^2) :
    (∀k,Summable (fun i => ‖f i k‖)) ∧
    (∑k,‖∑'i,f i k‖^2)≤(∑'i,g i)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : α→EuclideanSpace ℂ κ := fun i => e.symm (f i)
  have hF (i : α) : ‖F i‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    rw [EuclideanSpace.norm_sq_eq]
    exact hbound i
  have hpoint (k : κ) (i : α) : ‖f i k‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖f i j‖) (Finset.mem_univ k)).trans
      (hbound i)
  have hsum (k : κ) : Summable (fun i => ‖f i k‖) :=
    hg.of_nonneg_of_le (fun i => norm_nonneg _) (hpoint k)
  have hfp : Summable f := Pi.summable.mpr (fun k => (hsum k).of_norm)
  have he : (∑'i,F i)=e.symm (fun k => ∑'i,f i k) := by
    rw [show (fun i => F i)=(fun i => e.symm (f i)) from rfl,←e.symm.map_tsum]
    congr 1
    funext k
    exact tsum_apply hfp
  have hn : ‖e.symm (fun k => ∑'i,f i k)‖≤∑'i,g i := by
    rw [←he]
    exact tsum_of_norm_bounded hg.hasSum hF
  refine ⟨hsum,?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq] at hs
  exact hs

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

def completedSmoothDyadicBlock (V₀ V₁ V₂ W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  ∑n∈S i,∑v∈T i,quadraticRow k.val (primaryGenerator (n*v))*β i n v*
    (V₀ (Real.log ((Ideal.absNorm k.val:ℝ)/K))*
      V₁ (Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2))*
      V₂ (Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
          Real.exp (-2*Real.log ((Ideal.absNorm k.val:ℝ)/K)+
            Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
              3*Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))))


end CompletedGauss

end

end OAI

end


