-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0192_parallel1
-- name    : PNT_ZeroFree_433_0192_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:58:24.047002+00:00
-- url     : https://prove2.me/theorems/23bbe19d-8075-49bd-a089-a4b297f008cb
-- title:
--   Zero-free region foundations: CubicSieve.RankMargins [0192_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.RankMargins
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/RankMargins.lean#L79-L388

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0035
import Definitions.Def_PNT_ZeroFree_433_0042_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0083
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1
import Definitions.Def_PNT_ZeroFree_433_0506_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/RankMargins.lean
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

def canonicalPadding (ε C : ℝ) : ℝ :=
  min ((1:ℝ)/120040) (ε/6002)/(1+C)

theorem canonicalPadding_budget (ε C : ℝ) (hε : 0<ε) (hC : 0≤C) :
    0<canonicalPadding ε C ∧ canonicalPadding ε C≤(1:ℝ)/1000 ∧
    3000*canonicalPadding ε C≤(1:ℝ)/40 ∧
    3001*C*canonicalPadding ε C≤(1:ℝ)/40 ∧
    3001*C*canonicalPadding ε C≤ε/2 ∧
    C*canonicalPadding ε C≤(1:ℝ)/1000 := by
  let a : ℝ := min ((1:ℝ)/120040) (ε/6002)
  have ha : 0<a := lt_min (by norm_num) (div_pos hε (by norm_num))
  have ha₁ : a≤(1:ℝ)/120040 := min_le_left _ _
  have ha₂ : a≤ε/6002 := min_le_right _ _
  have hd : 0<1+C := by linarith
  have heta : 0<canonicalPadding ε C := div_pos ha hd
  have heta₁ : canonicalPadding ε C≤a := div_le_self ha.le (by linarith)
  have hCeta : C*canonicalPadding ε C≤a := by
    change C*(a/(1+C))≤a
    rw [←mul_div_assoc]
    exact (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨heta,?_,?_,?_,?_,?_⟩ <;> nlinarith


end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff


namespace CompletedHeight

section

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

def fixedLogReturnCLM (a b : ℝ) (ha : 0 < a) : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (positiveCutoff a b ha)).comp
    (SchwartzMap.compCLM ℝ
      (patchedLog_temperate (a/2) (max a b+a/2) (by linarith))
      (patchedLog_proper (a/2) (max a b+a/2) (by linarith)))

lemma fixedLogReturnCLM_apply (a b : ℝ) (ha : 0 < a) (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    fixedLogReturnCLM a b ha g x = positiveCutoff a b ha x •
      g (patchedLog (a/2) (max a b+a/2) (by linarith) x) := by
  rw [fixedLogReturnCLM,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      ((positiveCutoff a b ha).hasCompactSupport.hasTemperateGrowth (positiveCutoff a b ha).contDiff)]
  rfl

lemma positiveCutoff_support_bounds (a b : ℝ) (ha : 0 < a) (x : ℝ)
    (hx : positiveCutoff a b ha x ≠ 0) : x ∈ Icc (a/2) (max a b+a/2) := by
  have hm : x ∈ Function.support (positiveCutoff a b ha) := hx
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  constructor <;> linarith [hm.1,hm.2]

theorem frequencyTwist_finite_uniform_degree (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∀g : 𝓢(ℝ,ℂ), ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤ C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  refine ⟨n,?_⟩
  intro g
  let c : ℕ×ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤n := Finset.le_sup hz
  exact (frequencyTwist_seminorm_polynomial g t z.1 z.2).trans
    (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn) (by positivity) hC.le)

def uniformTwistedSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  fixedLogReturnCLM a b ha (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) t)

lemma uniformTwistedSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    uniformTwistedSchwartz W a b ha hs hW t x = normTwistedSource W t x := by
  rw [uniformTwistedSchwartz,fixedLogReturnCLM_apply,frequencyTwist_apply,
    CubicReflectionKernel.logSchwartz_apply]
  by_cases hc : positiveCutoff a b ha x=0
  · have hx : W x=0 := by
      by_contra hx
      have := positiveCutoff_one a b ha x (hs hx)
      exact zero_ne_one (hc.symm.trans this)
    simp only [hc,zero_smul,normTwistedSource,hx,mul_zero]
  · have hb := positiveCutoff_support_bounds a b ha x hc
    have hx : 0 < x := by linarith [hb.1]
    rw [patchedLog_eq_log _ _ _ x hb,Real.exp_log hx]
    by_cases hw : W x=0
    · simp only [hw,mul_zero,smul_zero,normTwistedSource]
    · rw [positiveCutoff_one a b ha x (hs hw),one_smul]
      rfl

theorem normTwistedSource_uniform_degree (a b : ℝ) (ha : 0 < a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W ⊆ Icc a b,∀hW : ContDiff ℝ ∞ W,
    ∃C : ℝ,0<C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (uniformTwistedSchwartz W a b ha hs hW t) ≤
        C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (fixedLogReturnCLM a b ha) S
  obtain ⟨n,hn⟩ := frequencyTwist_finite_uniform_degree s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hbound⟩ := hn (CubicReflectionKernel.logSchwartz W a b ha hs hW)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t
  exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

def HasUniformPolynomialKernel {κ : Type*} (P : κ→ℝ→ℝ→ℂ) : Prop :=
  (∀w t,ContDiffOn ℝ ∞ (CubicReflectionKernel.paperKernel (Vstar (P w t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (CubicReflectionKernel.paperKernel (Vstar (P w t))) i x‖≤
      C*(1+‖t‖)^n

abbrev SupportedSmoothSource (a b : ℝ) :=
  {W : ℝ→ℂ // Function.support W⊆Set.Icc a b ∧ ContDiff ℝ ∞ W}


theorem uniform_polynomial_kernel_log_separation {κ ι : Type*} [Fintype ι]
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel P)
    (V : ι→ℝ→ℂ) (slope M : ι→ℝ) (hM : ∀i,0≤M i)
    (hV : ∀i y,V i y≠0 → |y|≤M i) (A J : ℕ) :
    ∃n : ℕ,∀w : κ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀y : ι→ℝ,(∏i,V i (y i))*CubicReflectionKernel.paperKernel (Vstar (P w θ))
          (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,V i (y i)*FourierBridge.logPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) ∧
      (1+R)^A*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C*(1+‖θ‖)^n ∧
      (∀t : ℝ,(1+R)^A*(1+‖t‖)^J*‖B t‖≤C*(1+‖θ‖)^n) := by
  obtain ⟨n,hn⟩ := hP.2 A (J+(volume : Measure ℝ).integrablePower)
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    V slope M hM hV A J
  refine ⟨n,?_⟩
  intro w
  obtain ⟨D,hD,hkernel⟩ := hn w
  refine ⟨C*D,mul_nonneg hC hD.le,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hb,hp⟩ := hsep (CubicReflectionKernel.paperKernel (Vstar (P w θ))) (hP.1 w θ)
    (D*(1+‖θ‖)^n) (by positivity) (hkernel θ) R hR
  refine ⟨B,hB,hi,?_,?_⟩
  · exact hb.trans_eq (by ring)
  · intro t
    exact (hp t).trans_eq (by ring)

theorem uniform_polynomial_kernel_three_window {κ : Type*}
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel P)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂) (A : ℕ) :
    ∃n : ℕ,∀w : κ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*CubicReflectionKernel.paperKernel (Vstar (P w θ))
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*FourierBridge.logPhase t (-2*r))*
          (V₁ u*FourierBridge.logPhase t u)*(V₂ v*FourierBridge.logPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C*(1+‖θ‖)^n := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨n,hn⟩ := uniform_polynomial_kernel_log_separation P hP V slope M hm hv A 0
  refine ⟨n,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hn w
  refine ⟨C,hC,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h θ R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

end CompletedHeight


end

end OAI

end


