-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0235_parallel1
-- name    : PNT_ZeroFree_433_0235_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:52:24.043618+00:00
-- url     : https://prove2.me/theorems/797a61cc-45bd-47f2-8310-628aff07bd95
-- title:
--   Zero-free region foundations: Eisenstein.InverseCuspCoordinates [0235_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCuspCoordinates.lean#L82-L598

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0119
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1
import Definitions.Def_PNT_ZeroFree_433_0121_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0136_parallel2
import Definitions.Def_PNT_ZeroFree_433_0144_parallel2
import Definitions.Def_PNT_ZeroFree_433_0158_parallel2
import Definitions.Def_PNT_ZeroFree_433_0234_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCuspCoordinates.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate MatrixGroups Matrix

def inverseCuspCoordinates (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ×ℝ :=
  (-d/c-star z/(c^2*((v^2+‖z‖^2:ℝ):ℂ)),v/(‖c‖^2*(v^2+‖z‖^2)))

lemma inverseCuspCoordinates_height_pos (c d : ℂ) (v : ℝ) (z : ℂ)
    (hc : c≠0) (hv : 0<v) : 0<(inverseCuspCoordinates c d v z).2 := by
  dsimp [inverseCuspCoordinates]
  positivity

lemma inverseCuspCoordinates_line (c d : ℂ) (v : ℝ) (direction : ℂ) (t : ℝ) :
    inverseCuspCoordinates c d v ((t:ℂ)*direction)=inverseCuspPath c d v direction t := by
  simp only [inverseCuspCoordinates,inverseCuspPath,star_mul,Complex.star_def,
    Complex.conj_ofReal,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,mul_comm]

theorem inverse_cusp_action (g : SL(2,ℂ)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v) (z : ℂ) :
    g⁻¹ • upperPoint (z+g 0 0/g 1 0) v hv =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) := by
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have h00 : (g⁻¹) 0 0=g 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h01 : (g⁻¹) 0 1= -g 0 1 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h10 : (g⁻¹) 1 0= -g 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have h11 : (g⁻¹) 1 1=g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
  have hl : (-g 1 0)*(z+g 0 0/g 1 0)+g 0 0= -(g 1 0*z) := by
    field_simp
    ; ring
  have ht : g 1 1*(z+g 0 0/g 1 0)+(-g 0 1)=g 1 1*z+1/g 1 0 := by
    field_simp
    linear_combination hdet
  have hden : ‖-(g 1 0*z)‖^2+‖-g 1 0‖^2*v^2=
      ‖g 1 0‖^2*(v^2+‖z‖^2) := by rw [norm_neg,norm_neg,norm_mul,mul_pow];ring
  have hnormc : ((‖g 1 0‖^2:ℝ):ℂ)=g 1 0*star (g 1 0) := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj (g 1 0)).symm
  have hnormz : ((‖z‖^2:ℝ):ℂ)=z*star z := by
    simpa [Complex.normSq_eq_norm_sq,Complex.star_def] using (Complex.mul_conj z).symm
  have hT : v^2+‖z‖^2≠0 := by positivity
  have hTc : ((v^2+‖z‖^2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT
  have hcc : star (g 1 0)≠0 := star_ne_zero.mpr hc
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · rw [h00,h01,h10,h11,hl,ht,hden]
    dsimp [inverseCuspCoordinates]
    rw [Complex.ofReal_mul,hnormc]
    simp only [Complex.star_def,map_neg,map_mul]
    simp only [Complex.star_def] at hcc
    field_simp [hc,hcc,hTc]
    rw [Complex.ofReal_add,Complex.ofReal_pow,hnormz]
    simp only [Complex.star_def,]
    ; ring
  · rw [h10,h11,hl,hden]
    rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

lemma real_linear_horizontal_decompose (A : (ℂ×ℝ)→L[ℝ]ℂ) (z : ℂ) :
    A (z,0)=(z.re:ℂ)*A (1,0)+(z.im:ℂ)*A (Complex.I,0) := by
  have hz : ((z,0):ℂ×ℝ)=z.re • (1,0)+z.im • (Complex.I,0) := by
    apply Prod.ext
    · simpa only [Prod.fst_add,Prod.smul_fst,Complex.real_smul,mul_one] using z.re_add_im.symm
    · simp
  rw [hz,map_add,map_smul,map_smul]
  simp only [Complex.real_smul]

lemma real_linear_wirtinger_swap (A : (ℂ×ℝ)→L[ℝ]ℂ) (k : ℂ) :
    (1/2:ℂ)*(A (k,0)+Complex.I*A (-Complex.I*k,0))=
      k*((1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0))) := by
  rw [real_linear_horizontal_decompose A k,real_linear_horizontal_decompose A (-Complex.I*k)]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,zero_mul,neg_mul,one_mul,
    zero_add,zero_sub,Complex.ofReal_neg]
  conv_rhs => lhs; rw [←k.re_add_im]
  ring_nf
  simp only [Complex.I_sq]
  ring


def horizontalWirtingerZ (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ=>f (z+(t:ℂ))) 0-
    Complex.I*deriv (fun t : ℝ=>f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerZ_eq_fderiv (F : ℂ×ℝ→ℂ) (A : (ℂ×ℝ)→L[ℝ]ℂ)
    (z : ℂ) (v : ℝ) (hF : HasFDerivAt F A (z,v)) :
    horizontalWirtingerZ (fun w=>F (w,v)) z=
      (1/2:ℂ)*(A (1,0)-Complex.I*A (Complex.I,0)) := by
  have hline (direction : ℂ) :
      HasDerivAt (fun t : ℝ=>F (z+(t:ℂ)*direction,v)) (A (direction,0)) 0 := by
    have hz : HasDerivAt (fun t : ℝ=>z+(t:ℂ)*direction) direction 0 := by
      simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const direction).const_add z)
    have hp := hz.prodMk (hasDerivAt_const (0:ℝ) v)
    have hf : HasFDerivAt F A (z+(0:ℂ)*direction,v) := by simpa using hF
    exact hf.comp_hasDerivAt 0 hp
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  rw [horizontalWirtingerZ,h1,hI]


end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

theorem cusp_mellin_reflection (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q) :
    mellin (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) (2*s)=
      A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  have he : (fun v : ℝ=>A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹)))=
      (fun v : ℝ=>A • ((v:ℂ)^(-2:ℂ) • g ((Q*v)⁻¹))) := by
    funext v; simp only [smul_eq_mul]
  rw [he,mellin_const_smul,mellin_cpow_smul]
  have hm := mellin_comp_mul_left (fun v : ℝ=>g v⁻¹) (2*s+(-2:ℂ)) hQ
  rw [mellin_comp_inv] at hm
  rw [hm]
  simp only [smul_eq_mul]
  rw [show -(2*s+(-2:ℂ))=2-2*s by ring]
  ring

theorem cusp_mellin_reflection_of_identity (f g : ℝ→ℂ) (A s : ℂ)
    (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→f v=A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))) :
    mellin f (2*s)=A*(Q:ℂ)^(2-2*s)*mellin g (2-2*s) := by
  rw [←cusp_mellin_reflection g A s Q hQ]
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [hfg v hv]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalPhaseCLM (freq : ℂ) : ℂ →L[ℝ] ℂ :=
  (2*Real.pi*Complex.I:ℂ) •
    (freq • ContinuousLinearMap.id ℝ ℂ +
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (freq • ContinuousLinearMap.id ℝ ℂ))


lemma brevePhase_hasFDerivAt (freq z : ℂ) :
    HasFDerivAt (fun w : ℂ => ShortDraftTrace.breveE (freq*w))
      (ShortDraftTrace.breveE (freq*z) • horizontalPhaseCLM freq) z := by
  have hh := (horizontalPhaseCLM freq).hasFDerivAt.cexp (x:=z)
  convert! hh using 1


end


open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def truncatedCuspProfile (c : ℝ) (f : ℝ→ℂ) (x : ℝ) : ℂ :=
  if c<x then f x else 0

lemma truncatedCuspProfile_eventually_top (c : ℝ) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[atTop] f := by
  filter_upwards [eventually_gt_atTop c] with x hx
  simp only [truncatedCuspProfile,if_pos hx]

lemma truncatedCuspProfile_eventually_zero (c : ℝ) (hc : 0<c) (f : ℝ→ℂ) :
    truncatedCuspProfile c f =ᶠ[𝓝[>] 0] 0 := by
  have he : ∀ᶠx : ℝ in 𝓝[>] 0,x<c := (eventually_lt_nhds hc).filter_mono nhdsWithin_le_nhds
  filter_upwards [he] with x hx
  simp only [truncatedCuspProfile,if_neg (not_lt_of_ge hx.le),Pi.zero_apply]

lemma truncatedCuspProfile_locallyIntegrable (c : ℝ) (hc : 0<c) (f : ℝ→ℂ)
    (hf : ContinuousOn f (Set.Ioi 0)) :
    LocallyIntegrable (truncatedCuspProfile c f) volume := by
  have hcont : Continuous (fun x : ℝ=>f (max (c/2) x)) :=
    hf.comp_continuous (continuous_const.max continuous_id)
      (fun x=>lt_of_lt_of_le (by linarith : 0<c/2) (le_max_left _ _))
  have he : truncatedCuspProfile c f=
      (Set.Ioi c).indicator (fun x : ℝ=>f (max (c/2) x)) := by
    funext x
    by_cases hx : c<x
    · have hm : max (c/2) x=x := max_eq_right (by linarith)
      simp [truncatedCuspProfile,Set.indicator,hx,hm]
    · simp [truncatedCuspProfile,Set.indicator,hx]
  rw [he]
  exact hcont.locallyIntegrable.indicator measurableSet_Ioi

theorem truncatedCuspProfile_mellin_entire (c decay : ℝ) (hc : 0<c) (hdecay : 0<decay)
    (f : ℝ→ℂ) (hf : ContinuousOn f (Set.Ioi 0))
    (hbound : f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x))) :
    (∀s : ℂ,MellinConvergent (truncatedCuspProfile c f) s) ∧
      Differentiable ℂ (mellin (truncatedCuspProfile c f)) := by
  have hlocal := (truncatedCuspProfile_locallyIntegrable c hc f hf).locallyIntegrableOn (Set.Ioi 0)
  have htop : truncatedCuspProfile c f =O[atTop] (fun x : ℝ=>Real.exp (-decay*x)) :=
    hbound.congr' (truncatedCuspProfile_eventually_top c f).symm Filter.EventuallyEq.rfl
  have hzero (b : ℝ) : truncatedCuspProfile c f =O[𝓝[>] 0] (fun x : ℝ=>x^(-b)) :=
    (Asymptotics.isBigO_zero (fun x : ℝ=>x^(-b)) (𝓝[>] 0)).congr'
      (truncatedCuspProfile_eventually_zero c hc f).symm Filter.EventuallyEq.rfl
  constructor
  · intro s
    exact mellinConvergent_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)
  · intro s
    exact mellin_differentiableAt_of_isBigO_rpow_exp hdecay hlocal htop (hzero (s.re-1)) (by linarith)

end CubicEisenstein

end

end OAI

end


