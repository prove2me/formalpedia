-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0253_parallel1
-- name    : PNT_ZeroFree_433_0253_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:46.972982+00:00
-- url     : https://prove2.me/theorems/2dcbd79c-175a-4d3a-8539-2b06028c35c4
-- title:
--   Zero-free region foundations: Eisenstein.CorrespondenceAdjoint [0253_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceAdjoint
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondenceAdjoint.lean#L148-L412

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0219_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondenceAdjoint.lean
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
open scoped BigOperators Classical Topology MatrixGroups

section

lemma continuous_period_integral {X:Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X]
    (f:X→ℂ→ℂ) (hf:Continuous f.uncurry) :
    Continuous (fun x=>∫z in periodDomain,f x z) := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨U,hUc,hUn⟩:=exists_compact_mem_nhds x0
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(hUc.prod (isCompact_closedBall (0:ℂ) radius)).bddAbove_image hf.norm.continuousOn
  apply continuousAt_of_dominated
  · filter_upwards with x using (show Continuous (f x) from hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [hUn] with x hx
    filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
    apply hC
    exact ⟨(x,z),⟨hx,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz⟩,rfl⟩
  · let:=periodDomain_finiteMeasure
    exact integrable_const C
  · filter_upwards with z using (show Continuous (fun x=>f x z) from hf.comp (continuous_id.prodMk continuous_const)).continuousAt


local notation "Eis" => ActualEisensteinCubic.O


end

section
local notation "Eis" => ActualEisensteinCubic.O

lemma continuous_period_fourier_bound (f:ℂ→ℂ) (hf:Continuous f) :
    ∃C:ℝ,0≤C∧∀freq:ℂ,‖∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z)‖≤C := by
  let radius:ℝ:=∑i,‖periodBasis i‖
  obtain ⟨B,hB⟩:=(isCompact_closedBall (0:ℂ) radius).bddAbove_image hf.norm.continuousOn
  refine ⟨max 0 B*(volume.restrict periodDomain).real Set.univ,mul_nonneg (le_max_left _ _) (measureReal_nonneg),?_⟩
  intro freq
  let:=periodDomain_finiteMeasure
  apply norm_integral_le_of_norm_le_const
  filter_upwards [ae_restrict_mem periodDomain_measurable] with z hz
  rw [norm_mul,breveE_norm,mul_one]
  apply le_trans _ (le_max_right _ _)
  apply hB
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right,radius] using norm_mem_periodDomain z hz,rfl⟩

theorem continuous_fourier_bessel_subexponential (f:ℝ→ℂ→ℂ) (c:Eis→ℂ)
    (hf:∀v:ℝ,0<v→Continuous (f v))
    (hfour:∀v:ℝ,∀_hv:0<v,∀h:Eis,h≠0→
      (∫z in periodDomain,f v z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*c h*(v:ℂ)*
          schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v))
    (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0≤C∧∀h:Eis,h≠0→‖c h‖≤C*Real.exp (ε*‖cuspFrequency h‖) := by
  let v:ℝ:=ε/(9*Real.pi)
  have hv:0<v:=div_pos hε (by positivity)
  let area:ℂ:=((9*Real.sqrt 3/2:ℝ):ℂ)
  have harea:0<‖area‖:=norm_pos_iff.mpr cusp_volume_ne_zero
  obtain ⟨B,hB,hbound⟩:=continuous_period_fourier_bound (f v) (hf v hv)
  let D:ℝ:=‖area‖*v*cubicBesselLowerConstant
  have hD:0<D:=mul_pos (mul_pos harea hv) cubicBesselLowerConstant_pos
  refine ⟨B/D,div_nonneg hB hD.le,?_⟩
  intro h hh
  have hx:0<4*Real.pi*‖cuspFrequency h‖*v:=by
    have hr:=norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
    positivity
  have hl: cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))≤
      ‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖:=by
    have hb:=(schlafliBesselK_cubic_lower (4*Real.pi*‖cuspFrequency h‖*v) hx).trans (Complex.re_le_norm _)
    convert! hb using 1
    congr 2
    dsimp [v]
    field_simp

  have hb:=hbound (cuspFrequency h)
  rw [hfour v hv h hh,norm_mul,norm_mul,norm_mul,Complex.norm_of_nonneg hv.le] at hb
  have hm:‖c h‖*(D*Real.exp (-(ε*‖cuspFrequency h‖)))≤B:=by
    calc
      _ = (‖area‖*‖c h‖*v)*(cubicBesselLowerConstant*Real.exp (-(ε*‖cuspFrequency h‖))) := by dsimp [D];ring
      _ ≤ (‖area‖*‖c h‖*v)*‖schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)‖ :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ B := hb
  have hexp:0<Real.exp (-(ε*‖cuspFrequency h‖)):=Real.exp_pos _
  apply (le_div_iff₀ (mul_pos hD hexp)).mpr at hm
  calc
    _ ≤ B/(D*Real.exp (-(ε*‖cuspFrequency h‖))) := hm
    _ = (B/D)*Real.exp (ε*‖cuspFrequency h‖) := by rw [Real.exp_neg];field_simp


end

section
open ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma ninthCuspFrequency_three (h:Eis) :
    3*ninthCuspFrequency h=cuspFrequency h := by
  unfold ninthCuspFrequency cuspFrequency
  ring

lemma sourceFourierKernel_cubic_amplitude (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    (v:ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*(v:ℂ)*schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hvn:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  have hp:(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ)/(v:ℂ)^3:=by
    rw [show -(4/3:ℂ)-1=(2/3:ℂ)-3 by ring,Complex.cpow_sub _ _ hvn]
    congr 1
    exact Complex.cpow_natCast _ 3
  have he:=sourceFourierKernel_cubic_height h hh v hv
  rw [hp] at he
  apply (div_left_inj' (pow_ne_zero 3 hvn)).mp
  calc
    _ = ((v:ℂ)^(2/3:ℂ)/(v:ℂ)^3)*sourceFourierKernel (4/3) (cuspFrequency h*v) := by ring
    _ = _ := he
    _ = _ := by field_simp

lemma ramified_kernel_scaled_bessel (h:Eis) (hh:h≠0) (v:ℝ) (hv:0<v) :
    ((3*v:ℝ):ℂ)^(2/3:ℂ)*sourceFourierKernel (4/3) (ninthCuspFrequency h*(3*v:ℝ))=
      (3:ℂ)^(2/3:ℂ)*cubicBesselNormalizer h*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v) := by
  have hfreq:ninthCuspFrequency h*((3*v:ℝ):ℂ)=cuspFrequency h*v:=by
    push_cast
    rw [←ninthCuspFrequency_three]
    ring
  have hp:((3*v:ℝ):ℂ)^(2/3:ℂ)=(3:ℂ)^(2/3:ℂ)*(v:ℂ)^(2/3:ℂ):=by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (a:=3) (b:=v) (by norm_num) hv.le (2/3:ℂ)
  rw [hfreq,hp,mul_assoc,sourceFourierKernel_cubic_amplitude h hh v hv]
  ring

end


end


end CubicEisenstein

end

end OAI

end


