-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0155_parallel1
-- name    : PNT_ZeroFree_433_0155_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:20:05.963316+00:00
-- url     : https://prove2.me/theorems/dc59c8de-4484-42f0-9a87-499c0428939b
-- title:
--   Zero-free region foundations: Eisenstein.DirichletForm [0155_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.DirichletForm
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/DirichletForm.lean#L269-L611

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0050
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0143_parallel1
import Definitions.Def_PNT_ZeroFree_433_0146_parallel1
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/DirichletForm.lean
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

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups


namespace CompletedGauss

section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open CanonicalQuadraticSieve ActualEisensteinCubic


end


open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CanonicalQuadraticSieve

theorem completed_kernel_three_window
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*CubicReflectionKernel.paperKernel (Vstar W)
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨C,hC,h⟩ := completed_kernel_log_separation V slope M hm hv W a b ha hsupp hW A 0
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]


end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff

namespace InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

def initialLogProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(ℝ,ℂ) :=
  ((CubicReflectionKernel.logProfile_compact W a b ha hs).mul_left
    (f := fun t : ℝ => (Real.exp (t/2) : ℂ))).toSchwartzMap (by
      change ContDiff ℝ ∞ (fun t : ℝ => (Real.exp (t/2) : ℂ)*W (Real.exp t))
      have he : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (t/2)) :=
        Real.contDiff_exp.comp (contDiff_id.div_const 2)
      exact (Complex.ofRealCLM.contDiff.comp he).mul
        (hW.comp Real.contDiff_exp))

@[simp] lemma initialLogProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    initialLogProfile W a b ha hs hW t =
      (Real.exp (t/2) : ℂ)*W (Real.exp t) := rfl

theorem initialLogProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∀ t, initialLogProfile W a b ha hs hW t ≠ 0 →
      |t| ≤ |Real.log a|+|Real.log b|+1 := by
  intro t ht
  have hw : W (Real.exp t) ≠ 0 := by
    intro hz
    simp only [initialLogProfile_apply, hz, mul_zero] at ht
    exact ht rfl
  have hm := hs hw
  have hlo : Real.log a ≤ t := by
    simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  have hhi : t ≤ Real.log b := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos t) hm.2
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem initialLogProfile_normalized {ι : Type*} (p : ι → O)
    (hp : ∀ i, p i ≠ 0) (S : Finset ι) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S =
      (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p S/Z) := by
  let n := ‖eisEmbedding (∏ i ∈ S,p i)‖
  have hn : 0 < n := norm_pos_iff.mpr
    (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
  have hpos : 0 < n^2/Z := div_pos (sq_pos_of_pos hn) hZ
  have hexp : Real.exp (Real.log (n^2/Z)/2)=n/Real.sqrt Z := by
    rw [←JointLogSeparation.sqrt_exp_half, Real.exp_log hpos,
      Real.sqrt_div (sq_nonneg n), Real.sqrt_sq hn.le]
  change ((Real.exp (Real.log (n^2/Z)/2) : ℂ)*W (Real.exp (Real.log (n^2/Z)))) /
    (n : ℂ) = (Real.sqrt Z : ℂ)⁻¹*W (n^2/Z)
  rw [hexp, Real.exp_log hpos, Complex.ofReal_div]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hsz : (Real.sqrt Z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hZ).ne'
  field_simp

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
lemma mobiusRow_mul (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (c : ℂ) (z : O) :
    mobiusRow p hg F Ψ m (fun S => c*H S) z = c*mobiusRow p hg F Ψ m H z := by
  simp only [mobiusRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [inputColumn]
  ring

omit [DecidableEq ι] in
theorem mobiusRow_initial_normalization (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z =
      (Real.sqrt Z : ℂ)⁻¹*mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z := by
  have hc : normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) =
      fun T => (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p T/Z) := by
    funext T
    exact initialLogProfile_normalized p hp T Z hZ W a b ha hs hW
  rw [hc, mobiusRow_mul]

omit [DecidableEq ι] in
theorem mobiusRow_initial_energy (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ‖mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z‖^2 =
      ‖mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z‖^2/Z := by
  rw [mobiusRow_initial_normalization p hg hp F Ψ m z Z hZ W a b ha hs hW,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hZ), mul_pow, inv_pow, Real.sq_sqrt hZ.le]
  ring

end InitialMeanSquare

end

end OAI

end


