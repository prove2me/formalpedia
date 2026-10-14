-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0245_parallel1
-- name    : PNT_ZeroFree_433_0245_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:28:01.430532+00:00
-- url     : https://prove2.me/theorems/36c5769a-9530-4c2c-9c86-54fcf46306d1
-- title:
--   Zero-free region foundations: Eisenstein.AffineCuspFourier [0245_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.AffineCuspFourier
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean#L86-L626

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0016
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0111
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel2
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/AffineCuspFourier.lean
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
open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineLowerTerm_eq_shifted (q r:Eis) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    affineLowerTerm q r z v s a d=
      (eisEmbedding (symbol r d)*eisEmbedding (symbol d a)*
        ((‖eisEmbedding (q*a)‖^2:ℝ):ℂ)^(-s))*
          shiftedHeightKernel v s (eisEmbedding d/eisEmbedding (q*a)) z := by
  rw [affineLowerTerm,rowHeight_eq_shiftedHeightKernel z v hv s (q*a) d (mul_ne_zero hq ha)]
  ring

lemma affineLowerTerm_integrable (q r:Eis) (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    Integrable (fun z=>affineLowerTerm q r z v s a d) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma affineLowerTerm_fourier_integral (q r:Eis) (v:ℝ) (hv:0<v) (s freq:ℂ)
    (a d:Eis) (ha:a≠0) (hq:q≠0) :
    (∫z:ℂ,affineLowerTerm q r z v s a d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding (q*a)‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
            ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding (q*a))) := by
  simp_rw [affineLowerTerm_eq_shifted q r _ v hv s a d ha hq,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding (q*a)) freq]
  ring_nf

lemma affineCuspGaussTerm_factor (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a) :
    (eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol x a)*residueAdditive (3*k) a x) := by
  have hs:symbol (a+3*x) a=symbol (3*x) a:=symbol_congr ⟨1,by ring⟩
  rw [ramified_symbol_primary_shift_signed j n r a x hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary,map_mul eisEmbedding (symbol 3 a) (symbol x a)]
  have hp:=affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) x ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol x a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

lemma affineCuspTwistedCoefficient_add (h h1 q r a k x m:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a) :
    (eisEmbedding (symbol r (a+3*(x+a*m)))*eisEmbedding (symbol (a+3*(x+a*m)) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a))=
    (eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a)) := by
  rw [affineCuspGaussTerm_factor h h1 q r a k (x+a*m) j n ha hprimary hq hr hh hk,
    affineCuspGaussTerm_factor h h1 q r a k x j n ha hprimary hq hr hh hk]
  rw [symbol_congr (show a∣x+a*m-x from ⟨m,by ring⟩),
    residueAdditive_three_congr k a (x+a*m) x ha ⟨m,by ring⟩]

lemma affineLowerTerm_weighted_translate (h h1 q r a k x m:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a (a+3*(x+a*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affineLowerTerm q r (z+3*eisEmbedding m/eisEmbedding q) v s a (a+3*x)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q)) := by
  let c1:=eisEmbedding (symbol r (a+3*(x+a*m)))*eisEmbedding (symbol (a+3*(x+a*m)) a)
  let c0:=eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a)
  let B:=ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a)
  let Q:=ninthCuspFrequency h*(3*eisEmbedding m/eisEmbedding q)
  have harg:ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a)=B+Q:=by
    dsimp [B,Q]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq,eisEmbedding_ne_zero ha]
    ;ring
  have hcoef:=affineCuspTwistedCoefficient_add h h1 q r a k x m j n ha hprimary hq hr hh hk
  change c1*ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(x+a*m))/eisEmbedding (q*a))=
    c0*ShortDraftTrace.breveE B at hcoef
  rw [harg,AddChar.map_add_eq_mul] at hcoef
  have heB:ShortDraftTrace.breveE B≠0:=Complex.exp_ne_zero _
  have heQ:ShortDraftTrace.breveE Q≠0:=Complex.exp_ne_zero _
  have hmult:c1*ShortDraftTrace.breveE Q=c0:=by
    apply mul_right_cancel₀ heB
    calc
      _ = c1*(ShortDraftTrace.breveE B*ShortDraftTrace.breveE Q) := by ring
      _ = _ := hcoef
  have hsolve:c1=c0*ShortDraftTrace.breveE (-Q):=by
    rw [AddChar.map_neg_eq_inv]
    calc
      c1=c1*(ShortDraftTrace.breveE Q*(ShortDraftTrace.breveE Q)⁻¹) := by rw [mul_inv_cancel₀ heQ,mul_one]
      _ = (c1*ShortDraftTrace.breveE Q)*(ShortDraftTrace.breveE Q)⁻¹ := by ring
      _ = _ := by rw [hmult]
  have hrow:eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))=
      eisEmbedding (q*a)*(z+3*eisEmbedding m/eisEmbedding q)+eisEmbedding (a+3*x):=by
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq]
    ;ring
  change c1*((v/(‖eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))‖^2+
    ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=_
  rw [hsolve,hrow]
  unfold affineLowerTerm
  have hphase:-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q)=(-Q)+(-ninthCuspFrequency h*z):=by
    dsimp [Q];ring
  rw [hphase,AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma affineLowerIntegral_sum_translate (h h1 q r a k x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re) :
    (∑'m:Eis,∫z in periodDomain,affineLowerTerm q r z v s a (a+3*(x+a*m))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ∫z:ℂ,affineLowerTerm q r z v s a (a+3*x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint:=trace_mul_integrable (fun z=>affineLowerTerm q r z v s a (a+3*x))
    (affineLowerTerm_integrable q r v hv s hs a (a+3*x) ha hq) (ninthCuspFrequency h)
  rw [←finite_index_period_unfold q hq _ hint]
  apply tsum_congr
  intro m
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>affineLowerTerm_weighted_translate
    h h1 q r a k x m j n ha hprimary hq hr hh hk z v s)

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineDenominator_integral_formula (h h1 q r k:Eis) (j n:ℕ) (a:PrimaryLower)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hk:3*k=h1+ramifiedAffineParameter j n*a.val)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun d:PrimaryCoprimeDenominator a=>∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*ramifiedAffineGauss h q r a.val := by
  let e:=(cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hpair:=e.summable_iff.mpr hsum
  change Summable (fun p:CubicUnitResidue a.val×Eis=>∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) at hpair
  rw [←e.tsum_eq]
  change (∑'p:CubicUnitResidue a.val×Eis,∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=_
  rw [hpair.tsum_prod]
  have hinner (x:CubicUnitResidue a.val) :
      (∑'m:Eis,∫z in periodDomain,
        affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val x.val+a.val*m))*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*
        (((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)*
            ((eisEmbedding (symbol r (a.val+3*GaussianShiftedPartition.representative a.val x.val))*
              eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val x.val) a.val))*
                ShortDraftTrace.breveE (ninthCuspFrequency h*
                  eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val x.val)/eisEmbedding (q*a.val)))) := by
    rw [affineLowerIntegral_sum_translate h h1 q r a.val k _ j n (primaryLower_ne_zero a)
      (primaryLower_primary a) hq hr hh hk v hv s hs,
      affineLowerTerm_fourier_integral q r v hv s _ a.val _ (primaryLower_ne_zero a) hq]
  simp_rw [hinner]
  unfold ramifiedAffineGauss
  simp_rw [mul_assoc]
  rw [tsum_mul_left,tsum_mul_left,tsum_mul_left,tsum_mul_left]

lemma affineCuspFrequency_lift (h1:Eis) (j n:ℕ) (a:PrimaryLower)
    (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n) :
    ∃k:Eis,3*k=h1+ramifiedAffineParameter j n*a.val := by
  have hh:=dvd_add hfreq (a.2.mul_left (ramifiedAffineParameter j n))
  have hd:(3:Eis)∣h1+ramifiedAffineParameter j n*a.val:=by
    convert! hh using 1 ;ring
  obtain ⟨k,hk⟩:=hd
  exact ⟨k,hk.symm⟩

lemma affineCusp_norm_factor (q:Eis) (s:ℂ) (a:PrimaryLower) :
    ((‖eisEmbedding (q*a.val)‖^2:ℝ):ℂ)^(-s)=
      ((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s) := by
  rw [map_mul,norm_mul,mul_pow,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) (sq_nonneg _)]

theorem affineCusp_branch_fourier (h h1 q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
            unramifiedCubicGaussSeries s (3*r^2*h1) := by
  rw [hsum.tsum_sigma]
  have ha (a:PrimaryLower):
      (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
        affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
        ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q))*
        (((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*cubicUnitGaussSum (3*r^2*h1) a.val) := by
    obtain ⟨k,hk⟩:=affineCuspFrequency_lift h1 j n a hfreq
    rw [affineDenominator_integral_formula h h1 q r k j n a hq hr hh hk v hv s hs
      (hsum.sigma_factor a),ramifiedAffineGauss_eq_unramified h h1 q r a.val k j n
        (primaryLower_ne_zero a) (primaryLower_primary a) hq hr hh hk,
      affineCusp_norm_factor]
    ring
  simp_rw [ha]
  rw [tsum_mul_left]
  congr 1
  rw [←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  change ((‖eisEmbedding (CompletedGauss.primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (3*r^2*h1) (CompletedGauss.primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(CompletedGauss.primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]

end


section
open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem quotient_weighted_period_unfold (q:Eis) (hq:q≠0)
    (ψ:(Eis⧸Ideal.span {q})→ℂ) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*
      ∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (∑'r:Eis⧸Ideal.span {q},ψ r)*(∫z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℂ:=fun n=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hs:Summable (fun n:Eis=>ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*I n):=by
    apply (((finite_index_period_integrals_summable q hq f hf).norm).mul_left ‖ψ‖).of_norm_bounded
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm ψ _) (norm_nonneg _)
  have hinner (r:Eis⧸Ideal.span {q}):
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
        ψ (Ideal.Quotient.mk (Ideal.span {q}) n.val)*I n.val)=ψ r*(∫z:ℂ,f z) := by
    have heval (n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r})):
        Ideal.Quotient.mk (Ideal.span {q}) n.val=r:=n.2
    simp_rw [heval]
    rw [tsum_mul_left,GaussianFiberEquiv.fiber_tsum q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)]
    congr 1
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ):
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b:=by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    change (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    simp_rw [he]
    rw [←integral_eq_period_integrals (fun z=>f (z+b)) (hf.comp_add_right b)]
    exact integral_add_right_eq_self f b
  rw [←(hs.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q})) ).tsum_eq]
  change (∑'r:Eis⧸Ideal.span {q},∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),
    ψ (Ideal.Quotient.mk (Ideal.span {q}) n.val)*I n.val)=_
  simp_rw [hinner]
  exact tsum_mul_right

theorem character_weighted_period_unfold (q:Eis) (hq:q≠0)
    (ψ:AddChar (Eis⧸Ideal.span {q}) ℂ) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,ψ (Ideal.Quotient.mk (Ideal.span {q}) n)*
      ∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      if ψ=1 then (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) else 0 := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  rw [quotient_weighted_period_unfold q hq ψ f hf,tsum_fintype]
  split_ifs with hψ
  · rw [AddChar.sum_eq_card_of_eq_one hψ]
    congr 1
    change (Fintype.card (Eis⧸Ideal.span {q}):ℂ)=(Nat.card (Eis⧸Ideal.span {q}):ℂ)
    rw [Nat.card_eq_fintype_card]
  · rw [AddChar.sum_eq_zero_of_ne_one hψ,zero_mul]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def affinePeriodChar (q:Eis) (hq:q≠0) (ell:Eis) : AddChar (Eis⧸Ideal.span {q}) ℂ :=
  (eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates q hq).mulShift
    (Ideal.Quotient.mk (Ideal.span {q}) ell)

lemma affinePeriodChar_mk (q:Eis) (hq:q≠0) (ell x:Eis) :
    affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) x)=
      ShortDraftTrace.breveE (eisEmbedding (ell*x)/(eisEmbedding q*eisLam)) := by
  simp only [affinePeriodChar,AddChar.mulShift_apply,←map_mul,eisTraceModChar,
    IdealGaussCRT.traceModChar_mk]

lemma affinePeriodChar_eq_one (q:Eis) (hq:q≠0) (ell:Eis) :
    affinePeriodChar q hq ell=1 ↔ q∣ell := by
  constructor
  · intro h
    by_contra hd
    have hz:Ideal.Quotient.mk (Ideal.span {q}) ell≠0:=by
      intro he
      exact hd (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he))
    exact GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive q hq hz h
  · intro hd
    have hz:Ideal.Quotient.mk (Ideal.span {q}) ell=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hd)
    simp [affinePeriodChar,hz]

lemma affineCusp_general_weighted_translate (h q r a ell x m:Eis) (j n:ℕ)
    (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hell:3*ell=h+ramifiedAffineParameter j n*q*a)
    (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a (a+3*(x+a*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
        (affineLowerTerm q r (z+3*eisEmbedding m/eisEmbedding q) v s a (a+3*x)*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m/eisEmbedding q))) := by
  let A:=eisEmbedding (ramifiedAffineParameter j n*(a*m))/eisLam/3
  let delta:=3*eisEmbedding m/eisEmbedding q
  have hchar:eisEmbedding (symbol r (a+3*(x+a*m)))=
      eisEmbedding (symbol r (a+3*x))*ShortDraftTrace.breveE A:=by
    have hd:lambda^2∣a+3*x-1:=primary_add_three a x hprimary
    have h:=ramified_symbol_primary_shift_signed j n r (a+3*x) (a*m) hr hd
    convert! h using 1 ; congr 2 ;ring
  have hden:symbol (a+3*(x+a*m)) a=symbol (a+3*x) a:=
    symbol_congr ⟨3*m,by ring⟩
  have hrow:eisEmbedding (q*a)*z+eisEmbedding (a+3*(x+a*m))=
      eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x):=by
    dsimp [delta]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero hq]
    ;ring
  have hell':eisEmbedding ell=(eisEmbedding h+eisEmbedding (ramifiedAffineParameter j n)*eisEmbedding q*eisEmbedding a)/3:=by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he:=congrArg eisEmbedding hell
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  have harg:A+ninthCuspFrequency h*delta=eisEmbedding (ell*m)/(eisEmbedding q*eisLam):=by
    dsimp [A,delta,ninthCuspFrequency,cuspFrequency]
    simp only [map_mul]
    rw [hell']
    field_simp [eisEmbedding_ne_zero hq,eisLam_ne_zero]
    ;ring
  have hphase:ShortDraftTrace.breveE A*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+delta)):=by
    rw [affinePeriodChar_mk,←harg,←AddChar.map_add_eq_mul,←AddChar.map_add_eq_mul]
    congr 1
    ring
  unfold affineLowerTerm
  rw [hchar,hden,hrow]
  change _=affinePeriodChar q hq ell (Ideal.Quotient.mk (Ideal.span {q}) m)*
    ((eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ((v/(‖eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x)‖^2+
        ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+delta)))
  calc
    _ = ((eisEmbedding (symbol r (a+3*x))*eisEmbedding (symbol (a+3*x) a))*
      ((v/(‖eisEmbedding (q*a)*(z+delta)+eisEmbedding (a+3*x)‖^2+
        ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s)*
        (ShortDraftTrace.breveE A*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) := by ring
    _ = _ := by rw [hphase];ring

lemma affineCusp_masked_inner (h q r a ell x:Eis) (j n:ℕ)
    (ha:a≠0) (hprimary:lambda^2∣a-1) (hq:q≠0)
    (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hell:3*ell=h+ramifiedAffineParameter j n*q*a)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re) :
    (∑'m:Eis,∫z in periodDomain,affineLowerTerm q r z v s a (a+3*(x+a*m))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      if q∣ell then (Ideal.absNorm (Ideal.span {q}):ℂ)*
        (∫z:ℂ,affineLowerTerm q r z v s a (a+3*x)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) else 0 := by
  have hint:=trace_mul_integrable (fun z=>affineLowerTerm q r z v s a (a+3*x))
    (affineLowerTerm_integrable q r v hv s hs a (a+3*x) ha hq) (ninthCuspFrequency h)
  simp_rw [affineCusp_general_weighted_translate h q r a ell x _ j n hprimary hq hr hell,
    integral_const_mul]
  rw [character_weighted_period_unfold q hq (affinePeriodChar q hq ell) _ hint]
  simp only [affinePeriodChar_eq_one]

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma affineDenominator_zero (h h1 q r:Eis) (j n:ℕ) (a:PrimaryLower)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q)
    (hfreq:¬(3:Eis)∣h1+ramifiedAffineParameter j n)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun d:PrimaryCoprimeDenominator a=>∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'d:PrimaryCoprimeDenominator a,∫z in periodDomain,
      affineLowerTerm q r z v s a.val d.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=0 := by
  have hdiv:(3:Eis)∣h+ramifiedAffineParameter j n*q*a.val:=by
    have ht:=dvd_add hbase (a.2.mul_left (ramifiedAffineParameter j n*q))
    convert! ht using 1 ;ring
  obtain ⟨ell,hell⟩:=hdiv
  have hell':3*ell=h+ramifiedAffineParameter j n*q*a.val:=hell.symm
  have hne:¬q∣ell:=by
    rintro ⟨b,hb⟩
    have he:q*(3*b)=q*(h1+ramifiedAffineParameter j n*a.val):=by
      rw [hb,hh] at hell'
      linear_combination hell'
    have hc:=mul_left_cancel₀ hq he
    have ht:(3:Eis)∣h1+ramifiedAffineParameter j n*a.val:=⟨b,hc.symm⟩
    apply hfreq
    have hh:=dvd_sub ht (a.2.mul_left (ramifiedAffineParameter j n))
    convert! hh using 1 ;ring
  let e:=(cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hpair:=e.summable_iff.mpr hsum
  change Summable (fun p:CubicUnitResidue a.val×Eis=>∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)) at hpair
  rw [←e.tsum_eq]
  change (∑'p:CubicUnitResidue a.val×Eis,∫z in periodDomain,
    affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val p.1.val+a.val*p.2))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=_
  rw [hpair.tsum_prod]
  have hinner (x:CubicUnitResidue a.val):
      (∑'m:Eis,∫z in periodDomain,
        affineLowerTerm q r z v s a.val (a.val+3*(GaussianShiftedPartition.representative a.val x.val+a.val*m))*
          ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=0:=by
    rw [affineCusp_masked_inner h q r a.val ell _ j n (primaryLower_ne_zero a)
      (primaryLower_primary a) hq hr hell' v hv s hs,if_neg hne]
  simp only [hinner,tsum_zero]

theorem affineCusp_branch_fourier_masked (h h1 q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh:h=q*h1) (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (hsum:Summable (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))) :
    (∑'p:UnitLowerData,∫z in periodDomain,
      affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      if (3:Eis)∣h1+ramifiedAffineParameter j n then
        (Ideal.absNorm (Ideal.span {q}):ℂ)*((‖eisEmbedding q‖^2:ℝ):ℂ)^(-s)*
          ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
            ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
              unramifiedCubicGaussSeries s (3*r^2*h1) else 0 := by
  split_ifs with hfreq
  · exact affineCusp_branch_fourier h h1 q r j n hq hr hh hfreq v hv s hs hsum
  · rw [hsum.tsum_sigma]
    simp only [affineDenominator_zero h h1 q r j n _ hq hr hh hbase hfreq v hv s hs
      (hsum.sigma_factor _),tsum_zero]


end CubicEisenstein

end

end OAI

end


