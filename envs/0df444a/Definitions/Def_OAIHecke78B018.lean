-- Prove2me | Definitions.Def_OAIHecke78B018
-- name    : OAIHecke78B018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:46:22.209382+00:00
-- url     : https://prove2.me/theorems/f1362b65-6353-4db6-bede-467f44eb5dc3
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 19 of 29
-- statement:
--   Definitions bundle 19 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B017` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Eisenstein.AffineCuspFourier`, `Eisenstein.IntegralCover`, `Eisenstein.CoverTrace`, `Eisenstein.CubeCuspAverage`, `Eisenstein.InverseCorrespondence`, `Eisenstein.CorrespondenceTests`, `Eisenstein.CorrespondencePullback`, `Detector.HighRowsRamified`, `Detector.HighRowsSelectedRamified`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B018

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.AffineCuspFourier
  Eisenstein.IntegralCover
  Eisenstein.CoverTrace
  Eisenstein.CubeCuspAverage
  Eisenstein.InverseCorrespondence
  Eisenstein.CorrespondenceTests
  Eisenstein.CorrespondencePullback
  Detector.HighRowsRamified
  Detector.HighRowsSelectedRamified
-/

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
    convert (preTransparency := .instances) hh using 1 ;ring
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
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma hasSum_diagonal_unit_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:UnitLowerData=>∫z in periodDomain,
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val*
        ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalUnitCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [diagonal_unit_summand])

theorem diagonal_unit_eisenstein_fourier (u t:Eisˣ) (j:ℕ) (h h1:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hh:h=(t:Eis)*h1) (hfreq:(3:Eis)∣h1+ramifiedAffineParameter j 0)
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
          unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*h1) := by
  have hsum:=hasSum_diagonal_unit_integrals u t v hv s (ninthCuspFrequency h) hs
  rw [←hsum.tsum_eq]
  have h:=affineCusp_branch_fourier h h1 (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
    (by simpa using hr) hh hfreq v hv s (by linarith) hsum.summable
  simpa only [GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,Complex.ofReal_one,
    Complex.one_cpow,Ideal.span_singleton_eq_top.mpr t.isUnit,Ideal.absNorm_top,map_one,Nat.cast_one,one_mul] using h

lemma onceCusp_q_norm (t:Eisˣ) (j:Fin 3) :
    ‖eisEmbedding (onceCuspScale t*omega^j.val)‖^2=3 := by
  have hw:‖eisEmbedding omega‖=1:=by
    let w:Eisˣ:=(omega_primitive.isUnit (by decide)).unit
    have hw:(w:Eis)=omega:=(omega_primitive.isUnit (by decide)).unit_spec
    rw [←hw]
    exact GaussGeneratorTransport.norm_eisEmbedding_unit w
  simp only [onceCuspScale,map_mul,norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,
    one_mul,map_pow,norm_pow,hw,one_pow,mul_one,ramifiedEmbedding_traceLambda]
  rw [←ramifiedEmbedding_traceLambda,←norm_pow,←map_pow,ramifiedTraceLambda_square]
  norm_num [map_ofNat]

lemma onceCusp_q_absNorm (t:Eisˣ) (j:Fin 3) :
    Ideal.absNorm (Ideal.span {onceCuspScale t*omega^j.val})=3 := by
  have h:=onceCusp_q_norm t j
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at h
  exact_mod_cast h

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
    convert (preTransparency := .instances) h using 1 ; congr 2 ;ring
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
    convert (preTransparency := .instances) ht using 1 ;ring
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
    convert (preTransparency := .instances) hh using 1 ;ring
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

theorem diagonal_once_eisenstein_fourier (u t:Eisˣ) (j:Fin 3→ℕ) (h:Eis) (h1:Fin 3→Eis)
    (hr:∀l,(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^(j l)*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^(j l)*ramifiedTraceLambda))
    (hh:∀l,h=(onceCuspScale t*omega^l.val)*h1 l)
    (hbase:∀l,(3:Eis)∣h+ramifiedAffineParameter (j l) 1*(onceCuspScale t*omega^l.val))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ∑l:Fin 3,if (3:Eis)∣h1 l+ramifiedAffineParameter (j l) 1 then
        (3:ℂ)*(3:ℂ)^(-s)*((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
          ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
            unramifiedCubicGaussSeries s
              (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*h1 l) else 0 := by
  have hsum:=hasSum_diagonal_once_integrals u t v hv s (ninthCuspFrequency h) hs
  rw [←hsum.tsum_eq,hsum.summable.tsum_prod,tsum_fintype]
  apply Finset.sum_congr rfl
  intro l hl
  have hq:onceCuspScale t*omega^l.val≠0:=mul_ne_zero (onceCusp_scale_ne_zero t)
    (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero)
  have h:=affineCusp_branch_fourier_masked h (h1 l) (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) (j l) 1 hq
      (by simpa only [pow_one] using hr l) (hh l) (hbase l) v hv s (by linarith)
        (hsum.summable.prod_factor l)
  simpa only [onceCusp_q_norm,onceCusp_q_absNorm,Nat.cast_ofNat,Complex.ofReal_ofNat] using h

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedOmegaUnit : Eisˣ := (omega_primitive.isUnit (by decide)).unit
lemma ramifiedOmegaUnit_val : (ramifiedOmegaUnit:Eis)=omega :=
  (omega_primitive.isUnit (by decide)).unit_spec

lemma onceCusp_q_as_scale (t:Eisˣ) (l:Fin 3) :
    onceCuspScale (t*ramifiedOmegaUnit^l.val)=onceCuspScale t*omega^l.val := by
  simp only [onceCuspScale,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
  ring

lemma onceCusp_q_congr_scale (t:Eisˣ) (l:Fin 3) :
    (3:Eis)∣onceCuspScale t*omega^l.val-onceCuspScale t := by
  obtain ⟨b,hb⟩:=halfPrimary_omega_pow l.val
  have he:onceCuspScale t*omega^l.val-onceCuspScale t=
      (onceCuspScale t*(omega-1))*b:=by
    linear_combination onceCuspScale t*hb
  rw [he]
  exact (onceCusp_scale_lambda t).mul_right b

lemma onceCusp_q_dvd_three (t:Eisˣ) (l:Fin 3) :
    onceCuspScale t*omega^l.val∣(3:Eis) := by
  rw [←onceCusp_q_as_scale]
  exact ⟨onceCuspComplement _,(onceCusp_scale_complement _).symm⟩

lemma onceCusp_q_trace_dvd (t:Eisˣ) (l:Fin 3) :
    (3:Eis)∣ramifiedTraceLambda*(onceCuspScale t*omega^l.val) := by
  refine ⟨-(t:Eis)*omega^l.val,?_⟩
  unfold onceCuspScale
  linear_combination (t:Eis)*omega^l.val*ramifiedTraceLambda_square

lemma onceCusp_q_dvd_frequency (t:Eisˣ) (l:Fin 3) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) : onceCuspScale t*omega^l.val∣h := by
  have hd:(3:Eis)∣h-onceCuspScale t*omega^l.val:=by
    convert (preTransparency := .instances) dvd_sub hfreq (onceCusp_q_congr_scale t l) using 1 ;ring
  have hh:onceCuspScale t*omega^l.val∣h-onceCuspScale t*omega^l.val:=
    (onceCusp_q_dvd_three t l).trans hd
  simpa only [sub_add_cancel] using dvd_add hh (dvd_refl (onceCuspScale t*omega^l.val))

lemma onceCusp_period_congruence (t:Eisˣ) (l:Fin 3) (h:Eis) (j:ℕ)
    (hfreq:(3:Eis)∣h-onceCuspScale t) :
    (3:Eis)∣h+ramifiedAffineParameter j 1*(onceCuspScale t*omega^l.val) := by
  have hd:(3:Eis)∣h-onceCuspScale t*omega^l.val:=by
    convert (preTransparency := .instances) dvd_sub hfreq (onceCusp_q_congr_scale t l) using 1 ;ring
  have ht:=(onceCusp_q_trace_dvd t l).mul_left (j:Eis)
  convert (preTransparency := .instances) dvd_add hd ht using 1 ; simp only [ramifiedAffineParameter,Nat.cast_one] ;ring

def onceCuspFrequencyQuotient (t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (l:Fin 3) : Eis :=
  Classical.choose (onceCusp_q_dvd_frequency t l h hfreq)

lemma onceCuspFrequencyQuotient_spec (t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (l:Fin 3) :
    h=(onceCuspScale t*omega^l.val)*onceCuspFrequencyQuotient t h hfreq l :=
  Classical.choose_spec (onceCusp_q_dvd_frequency t l h hfreq)

def onceCuspRayUnit (u t:Eisˣ) (l:Fin 3) : Eisˣ := u⁻¹^2*t*ramifiedOmegaUnit^l.val

def onceCuspRayIndex (u t:Eisˣ) (l:Fin 3) : Fin 3 :=
  Classical.choose (unit_eq_sign_omega (onceCuspRayUnit u t l))

lemma onceCuspRayIndex_spec (u t:Eisˣ) (l:Fin 3) :
    (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^(onceCuspRayIndex u t l).val*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^(onceCuspRayIndex u t l).val*ramifiedTraceLambda) := by
  have he:(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=
      (onceCuspRayUnit u t l:Eis)*ramifiedTraceLambda:=by
    simp only [onceCuspRayUnit,onceCuspScale,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    ring
  have hh:=Classical.choose_spec (unit_eq_sign_omega (onceCuspRayUnit u t l))
  change (onceCuspRayUnit u t l:Eis)=omega^(onceCuspRayIndex u t l).val ∨
    (onceCuspRayUnit u t l:Eis)=-(omega^(onceCuspRayIndex u t l).val) at hh
  rw [he]
  rcases hh with hh|hh
  · exact Or.inl (by rw [hh])
  · exact Or.inr (by rw [hh];ring)

def onceCuspGaussSeries (u t:Eisˣ) (h:Eis) (hfreq:(3:Eis)∣h-onceCuspScale t) (s:ℂ) : ℂ :=
  ∑l:Fin 3,if (3:Eis)∣onceCuspFrequencyQuotient t h hfreq l+
    ramifiedAffineParameter (onceCuspRayIndex u t l).val 1 then
      (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
        unramifiedCubicGaussSeries s
          (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*onceCuspFrequencyQuotient t h hfreq l) else 0

theorem onceCusp_eisenstein_fourier (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*onceCuspGaussSeries u t h hfreq s := by
  rw [diagonal_once_eisenstein_fourier u t (fun l=>(onceCuspRayIndex u t l).val) h
    (onceCuspFrequencyQuotient t h hfreq) (onceCuspRayIndex_spec u t)
      (onceCuspFrequencyQuotient_spec t h hfreq)
        (fun l=>onceCusp_period_congruence t l h _ hfreq) v hv s hs,
    onceCuspGaussSeries,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  split_ifs <;>ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Manifold ContDiff
open Finset AddChar MulChar EisensteinEmbedding

lemma hyperbolicAction_contMDiff (g : SL(2,ℂ)) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      (fun w : HyperbolicSpace=>g•w) := by
  intro w
  rw [contMDiffAt_iff]
  refine ⟨(continuous_hyperbolic_action g).continuousAt,?_⟩
  have hp : hyperbolicSpatialCoordinates w∈hyperbolicSpatialChart.target :=
    hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have he : (fun p : SpatialCoordinates=>hyperbolicSpatialCoordinates
      (g•hyperbolicSpatialChart.symm p))=ᶠ[𝓝 (hyperbolicSpatialCoordinates w)]mobiusSpatial g := by
    filter_upwards [hyperbolicSpatialChart.open_target.mem_nhds hp] with p hpt
    rw [mobiusSpatial_coordinates_global]
    exact congrArg (mobiusSpatial g) (hyperbolicSpatialChart.right_inv hpt)
  have hd := ((mobiusSpatial_contDiffAt g _ (hyperbolicSpatialCoordinates_positive w)).congr_of_eventuallyEq he).contDiffWithinAt (s:=Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.preimage_id_eq,Set.range_id,
    hyperbolicSpatial_chartAt,hyperbolicSpatialChart_apply,Function.comp_def,id_eq] using hd

lemma kernel_contMDiff_of_lift (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞
      (fun w : HyperbolicSpace=>f (integralOrbitProjection globalKubotaKernel w))) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f := by
  intro q
  have hq : q∈(kernelQuotientChart q).source := mem_chart_source SpatialCoordinates q
  have hp : kernelQuotientChart q q∈hyperbolicSpatialChart.target :=
    ((kernelQuotientChart q).map_source hq).1
  have hs : ContMDiffOn 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I:=𝓘(ℝ,SpatialCoordinates)) (n:=∞) (x:=q.out))
  have hd := (hf (hyperbolicSpatialChart.symm (kernelQuotientChart q q))).comp _
    (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds hp))
  have he : (fun p=>f ((kernelQuotientChart q).symm p))=
      (fun p=>f (integralOrbitProjection globalKubotaKernel (hyperbolicSpatialChart.symm p))) := by
    funext p
    rw [kernelQuotientChart_symm]
  have hdc : ContDiffAt ℝ ∞ (fun p=>f ((kernelQuotientChart q).symm p))
      (kernelQuotientChart q q) := by
    rw [he]
    exact hd.contDiffAt
  have hc : ContinuousAt f q := by
    have hc := hdc.continuousAt.comp
      ((kernelQuotientChart q).continuousOn.continuousAt
        ((kernelQuotientChart q).open_source.mem_nhds hq))
    apply hc.congr
    filter_upwards [(kernelQuotientChart q).open_source.mem_nhds hq] with r hr
    exact congrArg f ((kernelQuotientChart q).left_inv hr)
  rw [contMDiffAt_iff]
  refine ⟨hc,?_⟩
  have hh := hdc.contDiffWithinAt (s:=Set.univ)
  simpa only [extChartAt_coe,extChartAt_coe_symm,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Function.id_comp,Function.comp_id,Set.range_id,
    kernelSpatial_chartAt,chartAt_self_eq,OpenPartialHomeomorph.refl_apply,Function.comp_def,id_eq] using hh

lemma kernelSource_comp_contMDiff (M : CubicKubota.levelTwo) (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (fun q=>f (kernelSourceAction M q)) := by
  apply kernel_contMDiff_of_lift
  exact (hf.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff (sourceComplexMatrix M))

def kernelSourceTest (M : CubicKubota.levelTwo) (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨fun q=>f.1 (kernelSourceAction M q),kernelSource_comp_contMDiff M f.1 f.2.1,
    f.2.2.comp_homeomorph (kernelSourceHomeomorph M)⟩

def kernelSourceTestLinear (M : CubicKubota.levelTwo) : kernelSmoothTests→ₗ[ℂ]kernelSmoothTests where
  toFun := kernelSourceTest M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma kernelSourceTest_field (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelTestField (kernelSourceTest M f)=kernelTestField f ∘ euclideanAction (sourceComplexMatrix M) := by
  funext p
  change f.1 (integralOrbitProjection globalKubotaKernel
      (sourceComplexMatrix M•euclideanToHyperbolic p))=
    f.1 (integralOrbitProjection globalKubotaKernel
      (euclideanToHyperbolic (euclideanAction (sourceComplexMatrix M) p)))
  rw [euclideanAction,euclideanToHyperbolic_coordinates]

lemma kernelSourceTest_energyDensity (M : CubicKubota.levelTwo) (f : kernelSmoothTests)
    (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelSourceTest M f) w=
      kernelTestEnergyDensity f (sourceComplexMatrix M•w) := by
  have hp := hyperbolicHeight_pos w
  have he : hyperbolicEuclideanCoordinates (sourceComplexMatrix M•w)=
      euclideanAction (sourceComplexMatrix M) (hyperbolicEuclideanCoordinates w) := by
    rw [euclideanAction,euclideanToHyperbolic_coordinates]
  have hR := hyperbolic_cotangent_energy_comp (sourceComplexMatrix M)
    (fun p : EuclideanSpatial=>(kernelTestField f p).re) (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  have hI := hyperbolic_cotangent_energy_comp (sourceComplexMatrix M)
    (fun p : EuclideanSpatial=>(kernelTestField f p).im) (hyperbolicEuclideanCoordinates w) hp
    ((kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp))
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [kernelSourceTest_field,he]
  exact congrArg₂ (fun a b : ℝ=>a+b) hR hI

lemma kernelSourceTest_quotientDensity (M : CubicKubota.levelTwo) (f : kernelSmoothTests)
    (q : KernelQuotient) :
    kernelQuotientEnergyDensity (kernelSourceTest M f) q=
      kernelQuotientEnergyDensity f (kernelSourceAction M q) := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelSourceTest_energyDensity M f w

lemma kernelSourceTest_energy (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelSourceTest M f)=kernelDirichletEnergy f := by
  unfold kernelDirichletEnergy
  simp_rw [kernelSourceTest_quotientDensity]
  exact (kernelSourceAction_measurePreserving M).integral_comp
    (kernelSourceHomeomorph M).measurableEmbedding _

lemma kernelSourceTest_mass (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelSourceTest M f)=kernelSourcePullback M (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  have hbase := (kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelSmoothTests_memLp f).coeFn_toLp
  filter_upwards [(kernelSmoothTests_memLp (kernelSourceTest M f)).coeFn_toLp,
    kernelSourcePullback_ae_eq M (kernelSmoothTestsToL2 f),hbase] with q hnew hpull hbase
  exact hnew.trans (hpull.trans hbase).symm

lemma kernelSourceTest_graph_norm (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelSourceTest M f)‖=‖kernelEnergyGraphCore f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [kernelEnergyGraphCore_norm_sq,kernelEnergyGraphCore_norm_sq,
    kernelSourceTest_energy,kernelSourceTest_mass,LinearIsometry.norm_map]

def kernelSourceEnergyPullback (M : CubicKubota.levelTwo) : KernelEnergyGraph→ₗᵢ[ℂ]KernelEnergyGraph :=
  (kernelEnergyGraphCore.comp (kernelSourceTestLinear M)).extendOfIsometry
    kernelEnergyGraphCore_dense (kernelSourceTest_graph_norm M)

lemma kernelSourceEnergyPullback_core (M : CubicKubota.levelTwo) (f : kernelSmoothTests) :
    kernelSourceEnergyPullback M (kernelEnergyGraphCore f)=kernelEnergyGraphCore (kernelSourceTest M f) :=
  LinearMap.extendOfIsometry_eq (kernelEnergyGraphCore.comp (kernelSourceTestLinear M))
    kernelEnergyGraphCore_dense (kernelSourceTest_graph_norm M) f

lemma kernelSourceEnergyPullback_mass (M : CubicKubota.levelTwo) (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelSourceEnergyPullback M u)=kernelSourcePullback M (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelSourceEnergyPullback M).continuous)
    ((kernelSourcePullback M).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelSourceEnergyPullback M (kernelEnergyGraphCore f))=
    kernelSourcePullback M (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelSourceEnergyPullback_core,kernelEnergyMass_core,kernelEnergyMass_core,kernelSourceTest_mass]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelSourceEnergyPullback_inverse (M : CubicKubota.levelTwo) (u : KernelEnergyGraph) :
    kernelSourceEnergyPullback M (kernelSourceEnergyPullback M⁻¹ u)=u := by
  apply kernelEnergyMass_injective
  rw [kernelSourceEnergyPullback_mass,kernelSourceEnergyPullback_mass,
    kernelSourcePullback_comp,inv_mul_cancel,kernelSourcePullback_one]

lemma kernelSourceEnergyPullback_surjective (M : CubicKubota.levelTwo) :
    Function.Surjective (kernelSourceEnergyPullback M) :=
  fun u=>⟨kernelSourceEnergyPullback M⁻¹ u,kernelSourceEnergyPullback_inverse M u⟩

theorem kernelSource_variationalSolution (M : CubicKubota.levelTwo) (F : KernelQuotientL2) :
    kernelSourceEnergyPullback M (kernelVariationalSolution F)=
      kernelVariationalSolution (kernelSourcePullback M F) := by
  apply kernelVariationalSolution_unique
  intro v
  obtain ⟨w,rfl⟩ := kernelSourceEnergyPullback_surjective M v
  rw [←kernelEnergyGraph_inner,LinearIsometry.inner_map_map,
    kernelSourceEnergyPullback_mass,LinearIsometry.inner_map_map,kernelEnergyGraph_inner]
  exact kernelVariationalSolution_equation F w

theorem kernelSource_variationalResolvent (M : CubicKubota.levelTwo) (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelSourcePullback M F)=
      kernelSourcePullback M (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelSourcePullback M F))=
    kernelSourcePullback M (kernelEnergyMass (kernelVariationalSolution F))
  rw [←kernelSource_variationalSolution,kernelSourceEnergyPullback_mass]

theorem kernelSource_operatorGraph (M : CubicKubota.levelTwo)
    (F G : KernelQuotientL2) (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelSourcePullback M F,kernelSourcePullback M G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelSource_variationalResolvent,hFG]

theorem kernelSource_eigenvector (M : CubicKubota.levelTwo) (F : KernelQuotientL2)
    (eigenvalue : ℂ) (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelSourcePullback M F,eigenvalue • kernelSourcePullback M F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelSource_operatorGraph M F (eigenvalue • F) hF

end CubicEisenstein

section

open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def cubeCuspHeightWeight (p:Eis) (j:Fin 4) : ℂ :=
  (((Ideal.absNorm (Ideal.span {p}):ℝ)^((2*(j.val:ℝ)-3)/3)):ℝ)

lemma cubeCuspHeightWeight_zero (p:Eis) :
    cubeCuspHeightWeight p 0=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ := by
  unfold cubeCuspHeightWeight
  generalize Ideal.absNorm (Ideal.span {p}) = n
  norm_num [Real.rpow_neg_one]

lemma cubeCuspHeightWeight_three (p:Eis) :
    cubeCuspHeightWeight p 3=(Ideal.absNorm (Ideal.span {p}):ℂ) := by
  unfold cubeCuspHeightWeight
  generalize Ideal.absNorm (Ideal.span {p}) = n
  norm_num

theorem actualCubeCuspPhaseSum_height (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) :
    actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2 := by
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp.ne_zero)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  by_cases hc:p∣((A:SL(2,Eis)) 1 0)
  · rw [actualCubeCuspPhaseSum_dvd A p hp hprimary hA hc,
      cubeCuspHeightWeight_zero]
    field_simp
  · have hcop:IsCoprime ((A:SL(2,Eis)) 1 0) p:=(hp.coprime_iff_not_dvd.mpr hc).symm
    rw [actualCubeCuspPhaseSum_coprime A p hp hprimary hA hcop,
      cubeCuspHeightWeight_zero,cubeCuspHeightWeight_three]
    field_simp
    ; ring

theorem actualCubeCuspPhaseSum_normalized (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) :
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹ := by
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp.ne_zero)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℂ)≠0:=by exact_mod_cast hqN
  rw [actualCubeCuspPhaseSum_height A p hp hprimary hA]
  field_simp

end CubicKubota

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeDilationRoot (p:Eis) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))

lemma cubeDilationRoot_sq (p:Eis) : cubeDilationRoot p^2=eisEmbedding p^3 :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (eisEmbedding p^3) (by decide : 0<2))

lemma cubeDilationRoot_ne_zero (p:Eis) (hp:p≠0) : cubeDilationRoot p≠0 := by
  intro h
  have hs:=cubeDilationRoot_sq p
  rw [h,zero_pow (by decide)] at hs
  exact pow_ne_zero 3 (eisEmbedding_ne_zero hp) hs.symm

def cubeAverageMatrix (p:Eis) (hp:p≠0) (q:Eis) : SL(2,ℂ) :=
  complexDiagonal (cubeDilationRoot p)⁻¹ (inv_ne_zero (cubeDilationRoot_ne_zero p hp)) *
    complexTranslation (3*eisEmbedding q)

lemma cubeAverageMatrix_entries (p:Eis) (hp:p≠0) (q:Eis) :
    (cubeAverageMatrix p hp q : Matrix (Fin 2) (Fin 2) ℂ)=
      !![(cubeDilationRoot p)⁻¹,(cubeDilationRoot p)⁻¹*(3*eisEmbedding q);0,cubeDilationRoot p] := by
  unfold cubeAverageMatrix
  rw [Matrix.SpecialLinearGroup.coe_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonal, complexTranslation, Matrix.mul_apply, Fin.sum_univ_two]

lemma cubeAverageMatrix_add_multiple (p:Eis) (hp:p≠0) (q n:Eis) :
    cubeAverageMatrix p hp (q+p^3*n)=
      complexTranslation (3*eisEmbedding n)*cubeAverageMatrix p hp q := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  have hz := cubeDilationRoot_ne_zero p hp
  have he := cubeDilationRoot_sq p
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation,
      map_add, map_mul, map_pow]
  rw [← he]
  field_simp

lemma cubeAverageMatrix_translate_one (p:Eis) (hp:p≠0) (q t:Eis)
    (ht:3*t=1-p^3) :
    cubeAverageMatrix p hp q*complexTranslation 1=
      complexTranslation 1*cubeAverageMatrix p hp (q+t) := by
  have ht':3*eisEmbedding t=1-eisEmbedding p^3:=by
    simpa only [map_mul,map_sub,map_one,map_ofNat,map_pow] using congrArg eisEmbedding ht
  have hz:=cubeDilationRoot_ne_zero p hp
  have he:=cubeDilationRoot_sq p
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, map_add]
  field_simp
  linear_combination -ht'-he

def cubeAverage (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (w:HyperbolicSpace) : ℂ :=
  (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
    ∑' r:Eis⧸Ideal.span {p^3},
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)

lemma cubeAverage_summand_congr (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (a b:Eis) (hab:p^3∣a-b) (w:HyperbolicSpace) :
    F (cubeAverageMatrix p hp a • w)=F (cubeAverageMatrix p hp b • w) := by
  obtain ⟨n,hn⟩:=hab
  have ha:a=b+p^3*n:=by linear_combination hn
  rw [ha,cubeAverageMatrix_add_multiple,mul_smul,hF]

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeAverageMatrix_action (p:Eis) (hp:p≠0) (q:Eis)
    (z:ℂ) (v:ℝ) (hv:0<v) :
    cubeAverageMatrix p hp q • upperPoint z v hv =
      upperPoint ((z+3*eisEmbedding q)/eisEmbedding p^3)
        (v/‖eisEmbedding p‖^3) (div_pos hv (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) 3)) := by
  rw [cubeAverageMatrix,mul_smul,complexTranslation_action,complexDiagonal_action]
  apply upperPoint_congr
  · rw [inv_pow,cubeDilationRoot_sq]
    ring
  · have hn:‖cubeDilationRoot p‖^2=‖eisEmbedding p‖^3:=by
      rw [←norm_pow,cubeDilationRoot_sq,norm_pow]
    rw [Complex.normSq_eq_norm_sq,norm_inv,inv_pow,hn]
    ring

theorem cubeAverage_period_one (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1)
    (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (hF1:∀w:HyperbolicSpace,F (complexTranslation 1 • w)=F w)
    (w:HyperbolicSpace) :
    cubeAverage p hp F (complexTranslation 1 • w)=cubeAverage p hp F w := by
  have hd:(3:Eis)∣1-p^3:=by
    have hh:=(three_dvd_primary_sub_one p hprimary).trans (sub_one_dvd_pow_sub_one p 3)
    simpa only [neg_sub] using dvd_neg.mpr hh
  obtain ⟨t,ht⟩:=hd
  let a:(Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}):=
    { toFun:=fun r=>r+Ideal.Quotient.mk _ t
      invFun:=fun r=>r-Ideal.Quotient.mk _ t
      left_inv:=fun r=>add_sub_cancel_right r _
      right_inv:=fun r=>sub_add_cancel r _ }
  let f (r:Eis⧸Ideal.span {p^3}):=
    F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
        (complexTranslation 1 • w))=f (a r) := by
    rw [←mul_smul,cubeAverageMatrix_translate_one p hp _ t ht.symm,mul_smul,hF1]
    apply cubeAverage_summand_congr p hp F hF
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [map_add,GaussianShiftedPartition.representative_spec,
      GaussianShiftedPartition.representative_spec]
    rfl
  unfold cubeAverage
  congr 1
  calc
    _ = ∑' r,f (a r):=tsum_congr hpoint
    _ = ∑' r,f r:=a.tsum_eq f

end CubicEisenstein
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def integralCoverMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient K :=
  Quotient.map' id (by
    rintro w u ⟨M,hM⟩
    exact ⟨Subgroup.inclusion hHK M,hM⟩)

lemma integralCoverMap_projection {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralOrbitProjection H w)=integralOrbitProjection K w := rfl

lemma integralCoverMap_measurable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Measurable (integralCoverMap hHK) := by
  apply measurable_from_quotient.mpr
  exact measurable_integralOrbitProjection K

lemma integralCoverMap_continuous {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Continuous (integralCoverMap hHK) := continuous_id.quotient_map' _

abbrev IntegralCoverCosets (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) := K ⧸ H.subgroupOf K

def integralCoverRep (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : K := q.out

def integralCoverSheet (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : Set HyperbolicSpace :=
  (fun w=>integralCoverRep H K q • w) ⁻¹' hyperbolicFundamentalSet K

def integralCoverDomain (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) : Set HyperbolicSpace :=
  ⋃q : IntegralCoverCosets H K,integralCoverSheet H K q

lemma integralCoverSheet_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) :
    MeasurableSet (integralCoverSheet H K q) :=
  (measurable_const_smul (integralCoverRep H K q)) (hyperbolicFundamentalSet_measurable K)

lemma integralCoverDomain_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K] :
    MeasurableSet (integralCoverDomain H K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  exact MeasurableSet.iUnion (integralCoverSheet_measurable H K)

lemma fundamental_reduction_unique (K : Subgroup (SL(2,ActualEisensteinCubic.O))) (hK : K≤CubicKubota.levelThree)
    (r s : K) (w : HyperbolicSpace) (hr : r•w∈hyperbolicFundamentalSet K)
    (hs : s•w∈hyperbolicFundamentalSet K) : r=s := by
  have he : s•w=r•w := by
    have hh := hyperbolicFundamentalSet_orbit_unique K (r•w) hr (s*r⁻¹)
      (by simpa only [mul_smul,inv_smul_smul] using hs)
    simpa only [mul_smul,inv_smul_smul] using hh
  have hfix : (r⁻¹*s)•w=w := by rw [mul_smul,he,inv_smul_smul]
  exact inv_mul_eq_one.mp (subgroup_action_free K hK _ w hfix)

lemma integralCoverSheet_pairwiseDisjoint (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hK : K≤CubicKubota.levelThree) : Pairwise (fun q r=>Disjoint (integralCoverSheet H K q) (integralCoverSheet H K r)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro w hwq hwr
  have he := fundamental_reduction_unique K hK (integralCoverRep H K q)
    (integralCoverRep H K r) w hwq hwr
  apply hqr
  exact Quotient.out_injective he

lemma integralCoverRep_mul_projection {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (q : IntegralCoverCosets H K) (h : H) :
    ((integralCoverRep H K q*Subgroup.inclusion hHK h : K) : IntegralCoverCosets H K)=q := by
  rw [QuotientGroup.mk_mul_of_mem _ (show Subgroup.inclusion hHK h∈H.subgroupOf K from h.property)]
  exact QuotientGroup.out_eq' q

lemma integralCover_inclusion_smul {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (h : H) (w : HyperbolicSpace) :
    (Subgroup.inclusion hHK h)•w=h•w := rfl

lemma mul_smul_mem_set_iff {G X : Type*} [Monoid G] [MulAction G X]
    (a b : G) (w v : X) (hv : v = b • w) (S : Set X) :
    a • v ∈ S ↔ (a * b) • w ∈ S := by
  rw [hv, mul_smul]

lemma mem_integralCoverSheet (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    w ∈ integralCoverSheet H K q ↔
      integralCoverRep H K q • w ∈ hyperbolicFundamentalSet K := Iff.rfl

lemma integralCoverSheet_membership {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (q : IntegralCoverCosets H K) (h : H) (w : HyperbolicSpace) :
    h•w∈integralCoverSheet H K q ↔
      (integralCoverRep H K q*Subgroup.inclusion hHK h)•w∈hyperbolicFundamentalSet K := by
  exact (mem_integralCoverSheet H K q (h • w)).trans
    (mul_smul_mem_set_iff (integralCoverRep H K q) (Subgroup.inclusion hHK h)
      w (h • w) (integralCover_inclusion_smul hHK h w).symm (hyperbolicFundamentalSet K))

lemma integralCoverDomain_covers {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (w : HyperbolicSpace) :
    ∃h : H,h•w∈integralCoverDomain H K := by
  obtain ⟨k,hk⟩ := hyperbolicFundamentalSet_covers K w
  let q : IntegralCoverCosets H K := k
  let r := integralCoverRep H K q
  have hr : r⁻¹*k∈H.subgroupOf K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' q)
  let h : H := ⟨((r⁻¹*k:K):SL(2,ActualEisensteinCubic.O)),hr⟩
  have hin : Subgroup.inclusion hHK h=r⁻¹*k := rfl
  refine ⟨h,Set.mem_iUnion.mpr ⟨q,?_⟩⟩
  apply (integralCoverSheet_membership hHK q h w).mpr
  change (r*Subgroup.inclusion hHK h)•w∈hyperbolicFundamentalSet K
  rw [hin,mul_inv_cancel_left]
  exact hk

lemma integralCoverDomain_unique {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) (w : HyperbolicSpace)
    (h1 h2 : H) (hh1 : h1•w∈integralCoverDomain H K)
    (hh2 : h2•w∈integralCoverDomain H K) : h1=h2 := by
  obtain ⟨q1,hq1⟩ := Set.mem_iUnion.mp hh1
  obtain ⟨q2,hq2⟩ := Set.mem_iUnion.mp hh2
  have he : integralCoverRep H K q1*Subgroup.inclusion hHK h1=
      integralCoverRep H K q2*Subgroup.inclusion hHK h2 := by
    apply fundamental_reduction_unique K hK _ _ w
    · exact (integralCoverSheet_membership hHK q1 h1 w).mp hq1
    · exact (integralCoverSheet_membership hHK q2 h2 w).mp hq2
  have hqeq : q1=q2 := by
    have hproj := congrArg (fun k : K=>(k : IntegralCoverCosets H K)) he
    rw [integralCoverRep_mul_projection hHK q1 h1,
      integralCoverRep_mul_projection hHK q2 h2] at hproj
    exact hproj
  subst q2
  exact (Subgroup.inclusion_injective hHK) (mul_left_cancel he)

theorem integralCoverDomain_isFundamentalDomain {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IsFundamentalDomain H (integralCoverDomain H K) hyperbolicVolume := by
  apply IsFundamentalDomain.mk' (integralCoverDomain_measurable H K).nullMeasurableSet
  intro w
  obtain ⟨h,hh⟩ := integralCoverDomain_covers hHK w
  exact ⟨h,hh,fun g hg=>integralCoverDomain_unique hHK hK w g h hg hh⟩

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverSheet_measure (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K)
    (S : Set (IntegralOrbitQuotient K)) (hS : MeasurableSet S) :
    hyperbolicVolume ((integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q)=
      integralQuotientVolume K S := by
  have he : (integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q=
      (fun w=>integralCoverRep H K q • w) ⁻¹'
        ((integralOrbitProjection K) ⁻¹' S ∩ hyperbolicFundamentalSet K) := by
    ext w
    change (integralOrbitProjection K w∈S ∧ integralCoverRep H K q•w∈hyperbolicFundamentalSet K) ↔
      (integralOrbitProjection K (integralCoverRep H K q•w)∈S ∧
        integralCoverRep H K q•w∈hyperbolicFundamentalSet K)
    rw [integralSubgroup_smul,integralOrbitProjection_eq]
  rw [he,measure_preimage_smul]
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS)]

theorem integralCoverMap_measure {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    Measure.map (integralCoverMap hHK) (integralQuotientVolume H)=
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hH : H≤CubicKubota.levelThree := hHK.trans hK
  rw [←integralQuotientVolume_independent H hH (integralCoverDomain H K)
    (integralCoverDomain_isFundamentalDomain hHK hK)]
  rw [Measure.map_map (integralCoverMap_measurable hHK) (measurable_integralOrbitProjection H)]
  change Measure.map (integralOrbitProjection K) (hyperbolicVolume.restrict (integralCoverDomain H K))=_
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS),Measure.smul_apply,smul_eq_mul]
  rw [integralCoverDomain,Set.inter_iUnion]
  rw [measure_iUnion]
  · simp_rw [integralCoverSheet_measure H K _ S hS]
    rw [tsum_fintype]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
  · intro q r hqr
    exact (integralCoverSheet_pairwiseDisjoint H K hK hqr).mono Set.inter_subset_right Set.inter_subset_right
  · intro q
    exact ((measurable_integralOrbitProjection K) hS).inter (integralCoverSheet_measurable H K q)

lemma integralCoverMap_measurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    MeasurePreserving (integralCoverMap hHK) (integralQuotientVolume H)
      ((H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) :=
  ⟨integralCoverMap_measurable hHK,integralCoverMap_measure hHK hK⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace InnerProduct
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

abbrev IntegralQuotientL2 (H : Subgroup (SL(2,ActualEisensteinCubic.O))) :=
  Lp ℂ 2 (integralQuotientVolume H)

def integralCoverPullback {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 K→L[ℂ]IntegralQuotientL2 H :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl)

theorem integralCoverPullback_ae {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) :
    integralCoverPullback hHK hK F=ᵐ[integralQuotientVolume H]
      fun q=>F (integralCoverMap hHK q) := by
  have hm := integralCoverMap_measurePreserving hHK hK
  have he := dominatedComplexL2_ae
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans
    (hm.quasiMeasurePreserving.ae_eq_comp he)

theorem integralCoverPullback_norm_le {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) :
    ‖integralCoverPullback hHK hK F‖≤(H.relIndex K:ℝ)^((1:ℝ)/2)*‖F‖ := by
  change ‖Lp.compMeasurePreserving (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)
    (dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl F)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  simpa only [ENNReal.toReal_natCast] using dominatedComplexL2_norm_le
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) F

def integralCoverTrace {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 H→L[ℂ]IntegralQuotientL2 K :=
  ContinuousLinearMap.adjoint (integralCoverPullback hHK hK)

theorem integralCoverTrace_pairing {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) (G : IntegralQuotientL2 H) :
    ⟪F,integralCoverTrace hHK hK G⟫_ℂ=⟪integralCoverPullback hHK hK F,G⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right _ _ _

theorem integralCoverPullback_opNorm_le {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    ‖integralCoverPullback hHK hK‖≤(H.relIndex K:ℝ)^((1:ℝ)/2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact integralCoverPullback_norm_le hHK hK

theorem integralCoverTrace_opNorm_le {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    ‖integralCoverTrace hHK hK‖≤(H.relIndex K:ℝ)^((1:ℝ)/2) := by
  rw [integralCoverTrace,ContinuousLinearMap.adjoint.norm_map]
  exact integralCoverPullback_opNorm_le hHK hK

end

local notation "O" => ActualEisensteinCubic.O

def integralCoverFiberPoint (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) : IntegralOrbitQuotient H :=
  Quotient.liftOn' q (fun r : K=>integralOrbitProjection H (r⁻¹•w)) (by
    intro a b hab
    have hh : b⁻¹*a∈H.subgroupOf K := by
      have h : a⁻¹*b∈H.subgroupOf K := QuotientGroup.leftRel_apply.mp hab
      simpa only [mul_inv_rev,inv_inv] using (H.subgroupOf K).inv_mem h
    apply Quotient.sound
    refine ⟨⟨((b⁻¹*a:K):SL(2,ActualEisensteinCubic.O)),hh⟩,?_⟩
    change (b⁻¹*a)•(a⁻¹•w)=b⁻¹•w
    simp only [mul_smul,smul_inv_smul])

lemma integralCoverFiberPoint_mk (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (r : K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K r w=integralOrbitProjection H (r⁻¹•w) := rfl

lemma integralCoverFiberPoint_rep (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K q w=
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) := by
  conv_lhs => rw [←QuotientGroup.out_eq' q]
  rfl

lemma integralCoverFiberPoint_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (k : K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K (k•q) (k•w)=integralCoverFiberPoint H K q w := by
  induction q using Quotient.inductionOn with
  | _ r =>
    change integralOrbitProjection H ((k*r)⁻¹•(k•w))=integralOrbitProjection H (r⁻¹•w)
    rw [mul_inv_rev,mul_smul,inv_smul_smul]

lemma integralCoverFiberPoint_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) : Measurable (integralCoverFiberPoint H K q) := by
  have he : integralCoverFiberPoint H K q=fun w=>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) :=
    funext (integralCoverFiberPoint_rep H K q)
  rw [he]
  exact (measurable_integralOrbitProjection H).comp (measurable_const_smul _)

def integralCoverTraceLift (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (w : HyperbolicSpace) : ℂ :=
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  ∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)

lemma integralCoverTraceLift_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (k : K) (w : HyperbolicSpace) :
    integralCoverTraceLift H K f (k•w)=integralCoverTraceLift H K f w := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  unfold integralCoverTraceLift
  rw [←(MulAction.bijective k).sum_comp (fun q=>f (integralCoverFiberPoint H K q (k•w)))]
  simp only [integralCoverFiberPoint_smul]

def integralCoverTraceFunction (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) : IntegralOrbitQuotient K→ℂ :=
  Quotient.lift (integralCoverTraceLift H K f) (by
    rintro w u ⟨k,rfl⟩
    exact (integralCoverTraceLift_smul H K f k w).symm)

lemma integralCoverTraceFunction_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f) :
    Measurable (integralCoverTraceFunction H K f) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply measurable_from_quotient.mpr
  change Measurable (integralCoverTraceLift H K f)
  unfold integralCoverTraceLift
  exact Finset.measurable_sum Finset.univ (fun q _=>hf.comp (integralCoverFiberPoint_measurable H K q))

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def IntegralCoverIntertwines {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) : Prop :=
  ∀h : H,g*integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (e h:SL(2,ActualEisensteinCubic.O))*g

lemma integralCoverIntertwines_action {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (h : H) (w : HyperbolicSpace) : g•(h•w)=(e h)•(g•w) := by
  rw [integralSubgroup_smul,integralSubgroup_smul,←mul_smul,he, mul_smul]

lemma integralCoverIntertwines_inverse {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralCoverIntertwines e.symm g⁻¹ := by
  intro j
  have hh := he (e.symm j)
  rw [e.apply_symm_apply] at hh
  have hh' := congrArg (fun A : SL(2,ℂ)=>g⁻¹*A*g⁻¹) hh
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh'.symm

def integralConjugateMap {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient J :=
  Quotient.map' (fun w=>g•w) (by
    rintro w u ⟨h,rfl⟩
    exact ⟨e h,(integralCoverIntertwines_action e g he h w).symm⟩)

lemma integralConjugateMap_projection {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) (w : HyperbolicSpace) :
    integralConjugateMap e g he (integralOrbitProjection H w)=
      integralOrbitProjection J (g•w) := rfl

lemma integralConjugateMap_measurable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    Measurable (integralConjugateMap e g he) := by
  apply measurable_from_quotient.mpr
  exact (measurable_integralOrbitProjection J).comp (measurable_const_smul g)

lemma integralConjugateMap_continuous {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    Continuous (integralConjugateMap e g he) :=
  (continuous_hyperbolic_action g).quotient_map' _

lemma integralConjugateMap_inverse {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
      (integralConjugateMap e g he q)=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection H (g⁻¹•(g•w))=integralOrbitProjection H w
    rw [inv_smul_smul]

def integralConjugateHomeomorph {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H≃ₜIntegralOrbitQuotient J where
  toFun := integralConjugateMap e g he
  invFun := integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
  left_inv := integralConjugateMap_inverse e g he
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ w =>
      change integralOrbitProjection J (g•(g⁻¹•w))=integralOrbitProjection J w
      rw [smul_inv_smul]
  continuous_toFun := integralConjugateMap_continuous e g he
  continuous_invFun := integralConjugateMap_continuous e.symm g⁻¹ _

lemma integralConjugate_fundamentalDomain {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) :
    IsFundamentalDomain J ((fun w : HyperbolicSpace=>g•w) '' hyperbolicFundamentalSet H)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain H hH).image_of_equiv
    (MulAction.toPerm g)
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm g).symm
      hyperbolicVolume hyperbolicVolume from
      (measurePreserving_smul g⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    e.symm.toEquiv
  intro j w
  change g•(e.symm j•w)=j•(g•w)
  simpa only [e.apply_symm_apply] using integralCoverIntertwines_action e g he (e.symm j) w

theorem integralConjugateMap_measurePreserving {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree) :
    MeasurePreserving (integralConjugateMap e g he) (integralQuotientVolume H)
      (integralQuotientVolume J) := by
  refine ⟨integralConjugateMap_measurable e g he,?_⟩
  have hmap := (measurePreserving_smul g hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul g) (hyperbolicFundamentalSet H)
  change Measure.map (integralConjugateMap e g he)
    (Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)))=_
  rw [Measure.map_map (integralConjugateMap_measurable e g he) (measurable_integralOrbitProjection H)]
  change Measure.map ((integralOrbitProjection J) ∘ (fun w : HyperbolicSpace=>g•w))
    (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))=_
  rw [←Measure.map_map (measurable_integralOrbitProjection J) (measurable_const_smul g),hmap.map_eq]
  exact integralQuotientVolume_independent J hJ _ (integralConjugate_fundamentalDomain e g he hH)

def integralConjugatePullback {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree) :
    Lp ℂ 2 (integralQuotientVolume J)→ₗᵢ[ℂ]Lp ℂ 2 (integralQuotientVolume H) :=
  Lp.compMeasurePreservingₗᵢ ℂ (integralConjugateMap e g he)
    (integralConjugateMap_measurePreserving e g he hH hJ)

theorem integralConjugatePullback_ae {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : Lp ℂ 2 (integralQuotientVolume J)) :
    integralConjugatePullback e g he hH hJ F=ᵐ[integralQuotientVolume H]
      fun q=>F (integralConjugateMap e g he q) :=
  Lp.coeFn_compMeasurePreserving F (integralConjugateMap_measurePreserving e g he hH hJ)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma scaled_cusp_periodic_upper
    (F : HyperbolicSpace→ℂ) (v : ℝ) (hv : 0<v)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (n : ActualEisensteinCubic.O) (z : ℂ) :
    F (integralComplexMatrix T • upperPoint (3*(z+3*eisEmbedding n)) v hv)=
      F (integralComplexMatrix T • upperPoint (3*z) v hv) := by
  rw [integral_upper_triangular_action T hT,integral_upper_triangular_action T hT]
  have hleft : eisEmbedding (T 0 0)^2*(3*(z+3*eisEmbedding n))+
      eisEmbedding (T 0 0*T 0 1)=
      3*((eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)/3)+
        3*eisEmbedding ((T 0 0)^2*n)) := by
    simp only [map_mul,map_pow]
    ring
  have hright : eisEmbedding (T 0 0)^2*(3*z)+eisEmbedding (T 0 0*T 0 1)=
      3*(eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)/3) := by ring
  rw [hleft,hright]
  exact hp ((T 0 0)^2*n) _

theorem sourceCusp_scaled_periodic (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v)
    (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix M •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have he (w : HyperbolicSpace) : cubicSourceResidualFunction (integralComplexMatrix M • w)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • w)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  calc
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*(z+3*eisEmbedding n)) v hv)) := he _
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*z) v hv)) :=
      congrArg (fun w : ℂ=>levelTwoComplexCharacter G*w)
        (scaled_cusp_periodic_upper
          (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
          v hv (sourceCuspRepresentative_periodic j v hv) T hT n z)
    _ = _ := (he _).symm

lemma sourceCusp_scaled_continuous (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ=>cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*z) v hv)) := by
  let c : ℂ→UpperCoordinates := fun z=>⟨(3*z,v),hv⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).prodMk continuous_const
  have ht := (continuous_translatedUpperCoordinates (integralComplexMatrix M)).comp hc
  have hh : Continuous (fun z : ℂ=>integralComplexMatrix M • upperPoint (3*z) v hv) := by
    simpa only [Function.comp_def,c] using ht
  exact cubicSourceResidualFunction_continuous.comp hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem period_integral_eisenstein_affine (f : ℂ→ℂ) (hf : Measurable f)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (b : ActualEisensteinCubic.O) (hb : b≠0) (c : ℂ) :
    (∫z in periodDomain,f (eisEmbedding b*z+c))=∫z in periodDomain,f z := by
  have hg : Measurable (fun z : ℂ=>f (z+c)) :=
    hf.comp (continuous_id.add continuous_const).measurable
  have hgp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n+c)=f (z+c) := by
    intro n z
    rw [show z+3*eisEmbedding n+c=(z+c)+3*eisEmbedding n by ring,hp]
  rw [period_integral_eisenstein_mul (fun z=>f (z+c)) hg hgp b hb]
  simpa only [add_comm] using period_integral_translation f hp c

lemma complex_upper_triangular_bottom_ne_zero (T : SL(2,ℂ)) (hT : T 1 0=0) : T 1 1≠0 := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using T.property
  intro hz
  rw [hz,mul_zero] at hdet
  exact zero_ne_one hdet

lemma complex_upper_triangular_action (T : SL(2,ℂ)) (hT : T 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    T • upperPoint z v hv=
      upperPoint ((T 0 0*z+T 0 1)/T 1 1) (v/‖T 1 1‖^2)
        (div_pos hv (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
          (complex_upper_triangular_bottom_ne_zero T hT)))) := by
  have hd := complex_upper_triangular_bottom_ne_zero T hT
  have hs : star (T 1 1)≠0 := by
    intro hz
    apply hd
    simpa only [star_star,star_zero] using congrArg star hz
  have hprod : T 1 1*star (T 1 1)=((‖T 1 1‖^2:ℝ):ℂ) := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq] using Complex.mul_conj (T 1 1)
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [hT,zero_mul,zero_add,star_zero,mul_zero,add_zero,norm_zero]
    norm_num only [zero_pow,mul_zero,add_zero]
    simp only [zero_mul,add_zero]
    rw [←hprod]
    field_simp [hd,hs]
  · simp only [hT,zero_mul,zero_add,norm_zero]
    norm_num

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem sourceCusp_average_enlarged_affine (M : SL(2,ActualEisensteinCubic.O)) (b : ActualEisensteinCubic.O) (hb : b≠0)
    (c : ℂ) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z+c)) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  exact (period_integral_eisenstein_affine
    (fun z=>cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))
    (sourceCusp_scaled_continuous M v hv).measurable
    (sourceCusp_scaled_periodic M v hv) b hb c).trans (sourceCusp_average_all M v hv)

theorem sourceCusp_average_complex_upper (M : SL(2,ActualEisensteinCubic.O)) (T : SL(2,ℂ))
    (hT : T 1 0=0) (b d : ActualEisensteinCubic.O) (hd : d≠0)
    (hscale : (T 0 0/T 1 1)*eisEmbedding b=eisEmbedding d)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix M • (T • upperPoint (3*(eisEmbedding b*z)) v hv)))=
      sourceCuspConstant M*((v/‖T 1 1‖^2:ℝ):ℂ)^(2/3:ℂ) := by
  have hcoord (z : ℂ) : (T 0 0*(3*(eisEmbedding b*z))+T 0 1)/T 1 1=
      3*(eisEmbedding d*z+(T 0 1/T 1 1)/3) := by
    rw [add_div]
    rw [show T 0 0*(3*(eisEmbedding b*z))/T 1 1=
      3*((T 0 0/T 1 1)*eisEmbedding b)*z by ring,hscale]
    ring
  simp_rw [complex_upper_triangular_action T hT,hcoord]
  exact sourceCusp_average_enlarged_affine M d hd _ _ _

lemma sourceCuspConstant_congruent (M N : SL(2,ActualEisensteinCubic.O))
    (h : N*M⁻¹∈CubicKubota.levelThree) :
    sourceCuspConstant N=
      CubicKubota.complexCharacter ⟨N*M⁻¹,h⟩*sourceCuspConstant M := by
  let g : CubicKubota.levelThree := ⟨N*M⁻¹,h⟩
  let g₂ : CubicKubota.levelTwo :=
    ⟨(g:SL(2,ActualEisensteinCubic.O)),CubicKubota.levelThree_le_levelTwo g.property⟩
  have hg : (g₂:SL(2,ActualEisensteinCubic.O))*M=N := by
    change (N*M⁻¹)*M=N
    group
  have hh := sourceCuspConstant_left g₂ M
  rw [hg] at hh
  change sourceCuspConstant N=
    CubicKubota.levelTwoComplexCharacter
      ⟨(g:SL(2,ActualEisensteinCubic.O)),CubicKubota.levelThree_le_levelTwo g.property⟩*sourceCuspConstant M at hh
  rw [CubicKubota.levelTwoComplexCharacter_restrict] at hh
  exact hh

end CubicEisenstein

section

open scoped Classical MatrixGroups BigOperators
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeCuspTriangular {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) : SL(2,ℂ) :=
  (integralComplexMatrix d.matrix)⁻¹*cubeAverageMatrix p hp q*integralComplexMatrix A

lemma cubeCuspTriangular_factor {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) :
    cubeAverageMatrix p hp q*integralComplexMatrix A=
      integralComplexMatrix d.matrix*cubeCuspTriangular d hp := by
  unfold cubeCuspTriangular
  group

lemma cubeCuspTriangular_entries {A:SL(2,Eis)} {p q:Eis} (d:CubeCuspData A p q) (hp:p≠0) :
    cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val ∧
    cubeCuspTriangular d hp 1 0=0 ∧
    cubeCuspTriangular d hp 1 1=(cubeDilationRoot p)⁻¹*eisEmbedding p^(3-d.exponent.val) := by
  let B:=cubeAverageMatrix p hp q*integralComplexMatrix A
  have hz:=cubeDilationRoot_ne_zero p hp
  have he:=cubeDilationRoot_sq p
  have hx:eisEmbedding (A 0 0)+3*eisEmbedding q*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    simpa only [map_add,map_mul,map_pow,map_ofNat] using congrArg eisEmbedding d.first
  have hy:eisEmbedding p^3*eisEmbedding (A 1 0)=
      eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    simpa only [map_mul,map_pow] using congrArg eisEmbedding d.second
  have hB0:B 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 0 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 0 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    linear_combination (cubeDilationRoot p)⁻¹*hx
  have hB1:B 1 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*eisEmbedding (d.matrix 1 0):=by
    change (∑k:Fin 2,cubeAverageMatrix p hp q 1 k*integralComplexMatrix A k 0)=_
    rw [Fin.sum_univ_two]
    simp only [cubeAverageMatrix_entries,integralComplexMatrix_apply,Matrix.cons_val_one,
      Matrix.cons_val_zero,Matrix.cons_val_fin_one,Matrix.of_apply,zero_mul,zero_add]
    rw [mul_assoc,←hy,←he]
    field_simp
  have hinv:(integralComplexMatrix d.matrix : Matrix (Fin 2) (Fin 2) ℂ)⁻¹=
      !![eisEmbedding (d.matrix 1 1),-eisEmbedding (d.matrix 0 1);
        -eisEmbedding (d.matrix 1 0),eisEmbedding (d.matrix 0 0)] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
    rfl
  have hT:cubeCuspTriangular d hp=(integralComplexMatrix d.matrix)⁻¹*B:=by
    dsimp [cubeCuspTriangular,B]
    group
  have hdet:eisEmbedding (d.matrix 0 0)*eisEmbedding (d.matrix 1 1)-
      eisEmbedding (d.matrix 0 1)*eisEmbedding (d.matrix 1 0)=1:=by
    have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
      simpa only [Matrix.det_fin_two] using d.matrix.property
    simpa only [map_sub,map_mul,map_one] using congrArg eisEmbedding hd
  have h00:cubeCuspTriangular d hp 0 0=(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    linear_combination (cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val*hdet
  have h10:cubeCuspTriangular d hp 1 0=0:=by
    rw [hT]
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,integralComplexMatrix_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.of_apply,hB0,hB1]
    ring
  refine ⟨h00,h10,?_⟩
  have hd:cubeCuspTriangular d hp 0 0*cubeCuspTriangular d hp 1 1=1:=by
    simpa only [Matrix.det_fin_two,h10,mul_zero,sub_zero] using (cubeCuspTriangular d hp).property
  rw [h00] at hd
  have hnon:(cubeDilationRoot p)⁻¹*eisEmbedding p^d.exponent.val≠0:=
    mul_ne_zero (inv_ne_zero hz) (pow_ne_zero _ (eisEmbedding_ne_zero hp))
  apply mul_left_cancel₀ hnon
  rw [hd]
  have hpow:eisEmbedding p^d.exponent.val*eisEmbedding p^(3-d.exponent.val)=eisEmbedding p^3:=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  calc
    1=(cubeDilationRoot p)⁻¹^2*eisEmbedding p^3:=by rw [←he,inv_pow,inv_mul_cancel₀ (pow_ne_zero 2 hz)]
    _=_:=by rw [←hpow];ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeCuspTriangular_integral_scale {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) :
    (cubeCuspTriangular d hp 0 0/cubeCuspTriangular d hp 1 1)*eisEmbedding (p^3)=
      eisEmbedding (p^(2*d.exponent.val)) := by
  obtain ⟨h00,_,h11⟩:=cubeCuspTriangular_entries d hp
  rw [h00,h11,map_pow,map_pow]
  have he:eisEmbedding p≠0:=eisEmbedding_ne_zero hp
  have hz:=cubeDilationRoot_ne_zero p hp
  have hpow:eisEmbedding p^3=eisEmbedding p^d.exponent.val*eisEmbedding p^(3-d.exponent.val):=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  rw [hpow]
  have htwo:eisEmbedding p^(2*d.exponent.val)=(eisEmbedding p^d.exponent.val)^2:=by
    rw [mul_comm 2 d.exponent.val,pow_mul]
  rw [htwo]
  field_simp

lemma cube_scale_norm_real (r:ℝ) (hr:0< r) (j:Fin 4) :
    (r^3)⁻¹*(r^(3-j.val))^2=r^(3-2*(j.val:ℝ)) := by
  fin_cases j <;> norm_num [Real.rpow_neg_natCast,Real.rpow_neg_one]
  all_goals field_simp

lemma cubeCuspTriangular_norm_sq {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) :
    ‖cubeCuspTriangular d hp 1 1‖^2 =
      ‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)) := by
  obtain ⟨_,_,h11⟩:=cubeCuspTriangular_entries d hp
  rw [h11,norm_mul,norm_inv,norm_pow,mul_pow,inv_pow]
  have hn:‖cubeDilationRoot p‖^2=‖eisEmbedding p‖^3:=by
    rw [←norm_pow,cubeDilationRoot_sq,norm_pow]
  rw [hn]
  exact cube_scale_norm_real _ (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) d.exponent

lemma cubeCuspTriangular_height {A:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData A p q) (hp:p≠0) (v:ℝ) (hv:0<v) :
    ((v/‖cubeCuspTriangular d hp 1 1‖^2:ℝ):ℂ)^(2/3:ℂ)=
      (v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  rw [cubeCuspTriangular_norm_sq]
  have hnon:0<‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)):=Real.rpow_pos_of_pos hr _
  have hcast:((2/3:ℝ):ℂ)=(2/3:ℂ):=by norm_num
  rw [←hcast,←Complex.ofReal_cpow (le_of_lt (div_pos hv hnon)),
    ←Complex.ofReal_cpow hv.le]
  unfold cubeCuspHeightWeight
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [Real.div_rpow hv.le hnon.le,←Real.rpow_mul hr.le]
  have hp2:(‖eisEmbedding p‖^2)^((2*(d.exponent.val:ℝ)-3)/3)=
      ‖eisEmbedding p‖^(((2*(d.exponent.val:ℝ)-3)/3)*2):=by
    rw [←Real.rpow_natCast_mul hr.le 2]
    congr 1
    ring
  rw [hp2,div_eq_mul_inv,←Real.rpow_neg hr.le]
  congr 1
  ring_nf

end CubicEisenstein

namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_primary_shift_cases (A:levelTwo) :
    ∃t:Fin 2, lambda^2∣((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0)-1 ∨
      lambda^2∣(-((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0))-1 := by
  rcases integer_congruence_primary_cases ((A:SL(2,Eis)) 0 0)
    (levelTwoRight A 0 0) (levelTwo_entry_integer A 0 0) with ha|ha|ha
  · rcases integer_congruence_primary_cases ((A:SL(2,Eis)) 1 0)
      (levelTwoRight A 1 0) (levelTwo_entry_integer A 1 0) with hc|hc|hc
    · have h1:(3:Eis)∣1:=by
        have hd:(A:SL(2,Eis)) 0 0*(A:SL(2,Eis)) 1 1-
          (A:SL(2,Eis)) 0 1*(A:SL(2,Eis)) 1 0=1:=by
            simpa only [Matrix.det_fin_two] using (A:SL(2,Eis)).property
        rw [←hd]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
      have hl:lambda∣(1:Eis):=(dvd_pow_self lambda (by decide:2≠0)).trans
        (lambda_sq_dvd_three.trans h1)
      exact (residue_lambda_prime.not_isUnit (isUnit_of_dvd_one hl)).elim
    · refine ⟨1,Or.inl ?_⟩
      convert (preTransparency := .instances) dvd_add (lambda_sq_dvd_three.trans ha) hc using 1 ; norm_num ; ring
    · refine ⟨1,Or.inr ?_⟩
      convert (preTransparency := .instances) dvd_add (dvd_neg.mpr (lambda_sq_dvd_three.trans ha)) hc using 1 ; norm_num ; ring
  · exact ⟨0,Or.inl (by simpa using ha)⟩
  · exact ⟨0,Or.inr (by simpa using ha)⟩

end CubicKubota
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma rationalComplex_S_sq_action (w:HyperbolicSpace) :
    rationalComplex (ModularGroup.S^2) • w=w := by
  have he:rationalComplex (ModularGroup.S^2)=complexDiagonal (-1) (by norm_num):=by
    have hS : ((ModularGroup.S ^ 2 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![-1, 0; 0, -1] := by decide
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change eisEmbedding ((Int.castRingHom Eis) ((ModularGroup.S ^ 2 : SL(2,ℤ)) i j)) = _
    rw [congrFun (congrFun hS i) j]
    fin_cases i <;> fin_cases j <;> simp [complexDiagonal]
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [he,complexDiagonal_action]
  apply upperPoint_congr <;> norm_num

lemma rationalComplex_T_eq : rationalComplex ModularGroup.T=complexTranslation 1 := by
  rw [← rationalUnipotent_one]
  apply Subtype.ext
  rw [rationalComplex_unipotent_coe]
  norm_num [complexTranslation]

theorem exists_primary_cusp_shift (A:levelTwo) :
    ∃B:levelTwo, lambda^2∣((B:SL(2,Eis)) 0 0)-1 ∧
      ∃t:Fin 2,∀w:HyperbolicSpace,
        integralComplexMatrix (B:SL(2,Eis)) • w=
          complexTranslation (t.val:ℂ) • (integralComplexMatrix (A:SL(2,Eis)) • w) := by
  obtain ⟨t,ht⟩:=levelTwo_primary_shift_cases A
  let T:levelTwo:=⟨rationalEmbedding (ModularGroup.T^t.val),rational_mem_levelTwo _⟩
  let S:levelTwo:=⟨rationalEmbedding (ModularGroup.S^2),rational_mem_levelTwo _⟩
  have hT:((T*A:levelTwo):SL(2,Eis)) 0 0=
      (A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0:=by
    have hmatrix : ((ModularGroup.T ^ t.val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        !![1, (t.val : ℤ); 0, 1] := by
      fin_cases t <;> decide
    change ((((ModularGroup.T ^ t.val : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.castRingHom Eis)) * ((A : SL(2, Eis)) : Matrix (Fin 2) (Fin 2) Eis)) 0 0 = _
    rw [hmatrix]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hST:((S*(T*A):levelTwo):SL(2,Eis)) 0 0=
      -((A:SL(2,Eis)) 0 0+(t.val:Eis)*(A:SL(2,Eis)) 1 0):=by
    have hneg (M:SL(2,Eis)) : (rationalEmbedding (ModularGroup.S^2)*M) 0 0= -M 0 0:=by
      have hmatrix : ((ModularGroup.S ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
          !![-1, 0; 0, -1] := by decide
      change ((((ModularGroup.S ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
        (Int.castRingHom Eis)) * (M : Matrix (Fin 2) (Fin 2) Eis)) 0 0 = _
      rw [hmatrix]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    exact (hneg ((T*A:levelTwo):SL(2,Eis))).trans (congrArg (fun x:Eis=> -x) hT)
  have hzero:complexTranslation 0=1:=by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [complexTranslation]
  have hact (w:HyperbolicSpace):integralComplexMatrix ((T*A:levelTwo):SL(2,Eis)) • w=
      complexTranslation (t.val:ℂ) • (integralComplexMatrix (A:SL(2,Eis)) • w):=by
    change integralComplexMatrix (rationalEmbedding (ModularGroup.T^t.val)*(A:SL(2,Eis))) • w=_
    rw [map_mul,mul_smul]
    change rationalComplex (ModularGroup.T^t.val) • (integralComplexMatrix (A:SL(2,Eis)) • w)=_
    fin_cases t
    · simp only [pow_zero,map_one,one_smul,Nat.cast_zero,hzero]
    · simp only [pow_one,rationalComplex_T_eq,Nat.cast_one]
  rcases ht with ht|ht
  · exact ⟨T*A,by rwa [hT],t,hact⟩
  · refine ⟨S*(T*A),by rwa [hST],t,?_⟩
    intro w
    change integralComplexMatrix (rationalEmbedding (ModularGroup.S^2)*((T*A:levelTwo):SL(2,Eis))) • w=_
    rw [map_mul,mul_smul]
    change rationalComplex (ModularGroup.S^2) • (integralComplexMatrix ((T*A:levelTwo):SL(2,Eis)) • w)=_
    rw [rationalComplex_S_sq_action,hact]

end CubicEisenstein

namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma matrix_mul_upper_first_column (A T:SL(2,Eis)) (hT:T 1 0=0) (i:Fin 2) :
    (A*T) i 0=A i 0*T 0 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,hT,mul_zero,add_zero]

namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}

def right_upper (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    CubeCuspData (A*T) p q where
  exponent:=d.exponent
  matrix:=d.matrix*T
  first:=by
    simp only [matrix_mul_upper_first_column _ T hT]
    linear_combination d.first*(T 0 0)
  second:=by
    simp only [matrix_mul_upper_first_column _ T hT]
    linear_combination d.second*(T 0 0)
  congruent:=by
    have he:(d.matrix*T)*(A*T)⁻¹=d.matrix*A⁻¹:=by group
    rw [he]
    exact d.congruent

lemma right_upper_exponent (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    (d.right_upper T hT).exponent=d.exponent := rfl

lemma right_upper_character (d:CubeCuspData A p q) (T:SL(2,Eis)) (hT:T 1 0=0) :
    complexCharacter ⟨(d.right_upper T hT).matrix*(A*T)⁻¹,(d.right_upper T hT).congruent⟩=
      complexCharacter ⟨d.matrix*A⁻¹,d.congruent⟩ := by
  apply congrArg complexCharacter
  apply Subtype.ext
  change (d.matrix*T)*(A*T)⁻¹=d.matrix*A⁻¹
  group

end CubeCuspData
end CubicKubota
end

namespace CubicEisenstein

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeAverage_continuous (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F) :
    Continuous (cubeAverage p hp F) := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  unfold cubeAverage
  simp only [tsum_fintype]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro r hr
  exact hF.comp (continuous_const_smul _)

lemma cubeAverage_cusp_integral (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ) (hF:Continuous F)
    (M:SL(2,Eis)) (b:Eis) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp F
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv))=
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      ∑' r:Eis⧸Ideal.span {p^3}, ∫z in periodDomain,
        F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv)) := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  let:Fintype (Eis⧸Ideal.span {p^3}):=Fintype.ofFinite _
  let c:ℂ→UpperCoordinates:=fun z=>⟨(3*(eisEmbedding b*z),v),hv⟩
  have hc:Continuous c:=by
    apply Continuous.subtype_mk
    exact (continuous_const.mul (continuous_const.mul continuous_id)).prodMk continuous_const
  have hi (r:Eis⧸Ideal.span {p^3}):IntegrableOn (fun z=>
        F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv))) periodDomain:=by
    apply periodDomain_integrable_of_continuous
    have hh:=(continuous_translatedUpperCoordinates
      (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r)*integralComplexMatrix M)).comp hc
    simpa only [Function.comp_def,c,mul_smul] using hF.comp hh
  unfold cubeAverage
  simp only [tsum_fintype]
  rw [integral_const_mul]
  congr 1
  exact integral_finsetSum _ (fun r _=>hi r)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace

theorem kernelSourceProjection_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelSourceProjection F)=
      kernelSourceProjection (kernelVariationalResolvent F) := by
  rw [kernelSourceProjection_apply,kernelSourceProjection_apply,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact kernelSource_variationalResolvent _ F

theorem kernelSourceProjection_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F,G)∈kernelEnergyLaplacian.graph) :
    (kernelSourceProjection F,kernelSourceProjection G)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hFG ⊢
  rw [←map_add,kernelSourceProjection_variationalResolvent,hFG]

theorem kernelSourceProjection_eigenvector (F : KernelQuotientL2)
    (eigenvalue : ℂ) (hF : (F,eigenvalue • F)∈kernelEnergyLaplacian.graph) :
    (kernelSourceProjection F,eigenvalue • kernelSourceProjection F)∈kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelSourceProjection_operatorGraph F (eigenvalue • F) hF

theorem kernelSourceProjection_cubicEisensteinResidue_eigenvector :
    (kernelSourceProjection cubicEisensteinResidue,
      (8/9:ℂ) • kernelSourceProjection cubicEisensteinResidue)∈kernelEnergyLaplacian.graph :=
  kernelSourceProjection_eigenvector _ _ cubicEisensteinResidue_eigenvector

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

def sourceCuspLeadingCoefficient (M : SL(2,ActualEisensteinCubic.O)) : ℂ :=
  sourceCuspConstant M / ((9*Real.sqrt 3/2:ℝ):ℂ)

def sourceCuspRemainder (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) : ℂ :=
  cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
    sourceCuspLeadingCoefficient M*(v:ℂ)^(2/3:ℂ)

lemma sourceCuspLeadingCoefficient_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo)
    (j : Fin 3) (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0)
    (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspLeadingCoefficient M=
      levelTwoComplexCharacter G*sourceCuspLeadingCoefficient (cuspRepresentative j) := by
  unfold sourceCuspLeadingCoefficient
  rw [hM,sourceCuspConstant_upper_right _ T hT,sourceCuspConstant_left]
  ring

lemma sourceCuspRemainder_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo)
    (j : Fin 3) (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0)
    (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspRemainder M z v hv=
      levelTwoComplexCharacter G*sourceCuspRemainder (cuspRepresentative j)
        (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv := by
  have hF : cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          upperPoint (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy,
      integral_upper_triangular_action T hT]
  unfold sourceCuspRemainder
  rw [hF,sourceCuspLeadingCoefficient_decomposition M G j T hT hM]
  ring

theorem sourceCuspRemainder_bound_all (K a : ℝ)
    (hK : ∀j : Fin 3,∀z : ℂ,∀v : ℝ,∀hv : 0<v,a≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hav : a≤v) :
    ‖sourceCuspRemainder M z v hv‖≤K/v^3 := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  rw [sourceCuspRemainder_decomposition M G j T hT hM z v hv,norm_mul,
    norm_levelTwoComplexCharacter,one_mul]
  exact hK j _ v hv hav

lemma sourceCuspConstant_one : sourceCuspConstant (1:SL(2,ActualEisensteinCubic.O))=sourcePrincipalCuspConstant := by
  have h := sourceCuspRepresentative_average (0:Fin 3) 1 (by norm_num)
  simpa only [sourceCuspConstant,cuspRepresentative,cuspParameter,lowerCuspMatrix_zero,
    ite_true,Complex.ofReal_one,Complex.one_cpow,mul_one] using h

lemma sourceCuspLeadingCoefficient_one :
    sourceCuspLeadingCoefficient (1:SL(2,ActualEisensteinCubic.O))=(3*(Real.pi:ℂ))*constantArithmeticResidue := by
  rw [sourceCuspLeadingCoefficient,sourceCuspConstant_one,sourcePrincipalCuspConstant]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (show (9*Real.sqrt 3/2:ℝ)≠0 by positivity))

lemma sourceCuspRemainder_one (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspRemainder (1:SL(2,ActualEisensteinCubic.O)) z v hv=
      sourceBesselCoefficients.fullFunction 0 (upperPoint z v hv) := by
  rw [sourceCuspRemainder,sourceCuspLeadingCoefficient_one,map_one,one_smul,
    cubicSourceResidualFunction_eq_bessel]
  simp only [sourceBesselFunction,SubexponentialBesselCoefficients.fullFunction,
    hyperbolicHeight_upperPoint,zero_mul,zero_add]
  ring

theorem sourceCuspRemainder_principal_cubic_decay (a : ℝ) (ha : 0<a) :
    ∃K : ℝ,0≤K ∧ ∀z : ℂ,∀v : ℝ,∀hv : 0<v,a≤v→
      ‖sourceCuspRemainder (1:SL(2,ActualEisensteinCubic.O)) z v hv‖≤K/v^3 := by
  obtain ⟨K,hK,hbound⟩ := sourceBesselCoefficients.fullFunction_zero_cubic_decay a ha
  refine ⟨K,hK,?_⟩
  intro z v hv hav
  rw [sourceCuspRemainder_one]
  exact hbound v hv z hav

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma integralCoverDomain_projection_measurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    MeasurePreserving (integralOrbitProjection H)
      (hyperbolicVolume.restrict (integralCoverDomain H K)) (integralQuotientVolume H) :=
  ⟨measurable_integralOrbitProjection H,integralQuotientVolume_independent H (hHK.trans hK) _
    (integralCoverDomain_isFundamentalDomain hHK hK)⟩

lemma integralCoverSheet_measurePreserving (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) :
    MeasurePreserving (fun w : HyperbolicSpace=>integralCoverRep H K q•w)
      (hyperbolicVolume.restrict (integralCoverSheet H K q))
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet K)) :=
  (measurePreserving_smul (integralCoverRep H K q) hyperbolicVolume).restrict_preimage
    (hyperbolicFundamentalSet_measurable K)

lemma integralCoverFiberPoint_rep_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K q (integralCoverRep H K q•w)=integralOrbitProjection H w := by
  rw [integralCoverFiberPoint_rep,inv_smul_smul]

lemma integralCoverFiber_integrable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : Integrable f (integralQuotientVolume H)) (q : IntegralCoverCosets H K) :
    IntegrableOn (fun w=>f (integralCoverFiberPoint H K q w))
      (hyperbolicFundamentalSet K) hyperbolicVolume := by
  have hD := (integralCoverDomain_projection_measurePreserving hHK hK).integrable_comp_of_integrable hf
  have hS : IntegrableOn (fun w=>f (integralOrbitProjection H w))
      (integralCoverSheet H K q) hyperbolicVolume :=
    IntegrableOn.mono_set hD (Set.subset_iUnion (integralCoverSheet H K) q)
  apply ((integralCoverSheet_measurePreserving H K q).integrable_comp
    (hmeas.comp (integralCoverFiberPoint_measurable H K q)).aestronglyMeasurable).mp
  simpa only [IntegrableOn,Function.comp_def,integralCoverFiberPoint_rep_smul] using hS

theorem integralCoverTraceFunction_integrable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : Integrable f (integralQuotientVolume H)) :
    Integrable (integralCoverTraceFunction H K f) (integralQuotientVolume K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply ((quotient_projection_measurePreserving K).integrable_comp
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable).mp
  change Integrable (fun w=>∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)) _
  exact integrable_finsetSum Finset.univ (fun q _=>integralCoverFiber_integrable hHK hK f hmeas hf q)

lemma integralCoverFiber_integral (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (f : IntegralOrbitQuotient H→ℂ) :
    (∫w in hyperbolicFundamentalSet K,f (integralCoverFiberPoint H K q w)∂hyperbolicVolume)=
      ∫w in integralCoverSheet H K q,f (integralOrbitProjection H w)∂hyperbolicVolume := by
  have hh := (measurePreserving_smul (integralCoverRep H K q) hyperbolicVolume).setIntegral_preimage_emb
    (measurableEmbedding_const_smul (integralCoverRep H K q))
    (fun w=>f (integralCoverFiberPoint H K q w)) (hyperbolicFundamentalSet K)
  simpa only [integralCoverSheet,integralCoverFiberPoint_rep_smul] using hh.symm

theorem integralCoverTraceFunction_integral {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : Integrable f (integralQuotientVolume H)) :
    (∫q,integralCoverTraceFunction H K f q∂integralQuotientVolume K)=
      ∫q,f q∂integralQuotientVolume H := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hD := (integralCoverDomain_projection_measurePreserving hHK hK).integrable_comp_of_integrable hf
  have hS (q : IntegralCoverCosets H K) : IntegrableOn (fun w=>f (integralOrbitProjection H w))
      (integralCoverSheet H K q) hyperbolicVolume :=
    IntegrableOn.mono_set hD (Set.subset_iUnion (integralCoverSheet H K) q)
  rw [integralQuotientVolume_integral K _
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable]
  change (∫w in hyperbolicFundamentalSet K,
    ∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)∂hyperbolicVolume)=_
  rw [integral_finsetSum Finset.univ (fun q _=>integralCoverFiber_integrable hHK hK f hmeas hf q)]
  simp_rw [integralCoverFiber_integral H K]
  rw [←integral_iUnion_fintype (integralCoverSheet_measurable H K)
    (integralCoverSheet_pairwiseDisjoint H K hK) hS]
  change (∫w in integralCoverDomain H K,f (integralOrbitProjection H w)∂hyperbolicVolume)=_
  rw [←(integralCoverDomain_projection_measurePreserving hHK hK).map_eq]
  exact (integral_map (measurable_integralOrbitProjection H).aemeasurable hmeas.aestronglyMeasurable).symm

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverFiber_memLp {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) (q : IntegralCoverCosets H K) :
    MemLp (fun w=>f (integralCoverFiberPoint H K q w)) 2
      (hyperbolicVolume.restrict (hyperbolicFundamentalSet K)) := by
  have hD := hf.comp_measurePreserving (integralCoverDomain_projection_measurePreserving hHK hK)
  have hS := MemLp.mono_measure
    (Measure.restrict_mono_set hyperbolicVolume (Set.subset_iUnion (integralCoverSheet H K) q)) hD
  have hm := integralCoverSheet_measurePreserving H K q
  have hi := memLp_map_measure_iff (p:=2)
    (hmeas.comp (integralCoverFiberPoint_measurable H K q)).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  simpa only [Function.comp_def,integralCoverFiberPoint_rep_smul] using hS

theorem integralCoverTraceFunction_memLp {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) :
    MemLp (integralCoverTraceFunction H K f) 2 (integralQuotientVolume K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hm := quotient_projection_measurePreserving K
  have hi := memLp_map_measure_iff (p:=2)
    (integralCoverTraceFunction_measurable H K f hmeas).aestronglyMeasurable hm.aemeasurable
  rw [hm.map_eq] at hi
  apply hi.mpr
  change MemLp (fun w=>∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)) 2 _
  exact memLp_finsetSum Finset.univ (fun q _=>integralCoverFiber_memLp hHK hK f hmeas hf q)

lemma integralCoverMap_fiberPoint {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverMap hHK (integralCoverFiberPoint H K q w)=integralOrbitProjection K w := by
  rw [integralCoverFiberPoint_rep,integralCoverMap_projection,integralSubgroup_smul,
    integralOrbitProjection_eq]

lemma integralCoverTraceFunction_pairing {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (F : IntegralOrbitQuotient K→ℂ)
    (f : IntegralOrbitQuotient H→ℂ) (q : IntegralOrbitQuotient K) :
    integralCoverTraceFunction H K (fun r=>inner ℂ (F (integralCoverMap hHK r)) (f r)) q=
      inner ℂ (F q) (integralCoverTraceFunction H K f q) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,inner ℂ
      (F (integralCoverMap hHK (integralCoverFiberPoint H K r w)))
      (f (integralCoverFiberPoint H K r w)))=
      inner ℂ (F (integralOrbitProjection K w)) (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))
    simp only [integralCoverMap_fiberPoint,inner_sum]

theorem integralCoverTrace_toLp_ae {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hf : MemLp f 2 (integralQuotientVolume H)) :
    integralCoverTrace hHK hK (hf.toLp f)=ᵐ[integralQuotientVolume K]
      integralCoverTraceFunction H K f := by
  let htr := integralCoverTraceFunction_memLp hHK hK f hmeas hf
  let Tf : IntegralQuotientL2 K := htr.toLp (integralCoverTraceFunction H K f)
  have he : Tf=integralCoverTrace hHK hK (hf.toLp f) := by
    apply ext_inner_left ℂ
    intro F
    let pair : IntegralOrbitQuotient H→ℂ := fun r=>inner ℂ (F (integralCoverMap hHK r)) (f r)
    have hpm : Measurable pair := by
      have hFm : Measurable (fun r=>F (integralCoverMap hHK r)) :=
        (Lp.stronglyMeasurable F).measurable.comp (integralCoverMap_measurable hHK)
      have hstar : Measurable (fun r=>star (F (integralCoverMap hHK r))) :=
        continuous_star.measurable.comp hFm
      have hm := hmeas.mul hstar
      change Measurable (fun r=>f r*star (F (integralCoverMap hHK r))) at hm
      simpa only [pair,RCLike.inner_apply,starRingEnd_apply] using hm
    have hae : (fun r=>inner ℂ (integralCoverPullback hHK hK F r) (hf.toLp f r))
        =ᵐ[integralQuotientVolume H]pair := by
      filter_upwards [integralCoverPullback_ae hHK hK F,hf.coeFn_toLp] with r hr hfR
      dsimp [pair]
      rw [hr,hfR]
    have hpi : Integrable pair (integralQuotientVolume H) :=
      (L2.integrable_inner (integralCoverPullback hHK hK F) (hf.toLp f)).congr hae
    calc
      inner ℂ F Tf = ∫q,inner ℂ (F q) (integralCoverTraceFunction H K f q)∂integralQuotientVolume K := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [htr.coeFn_toLp] with q hq
        change inner ℂ (F q) (htr.toLp (integralCoverTraceFunction H K f) q)=_
        rw [hq]
      _ = ∫q,integralCoverTraceFunction H K pair q∂integralQuotientVolume K := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun q=>(integralCoverTraceFunction_pairing hHK F f q).symm)
      _ = ∫r,pair r∂integralQuotientVolume H :=
        integralCoverTraceFunction_integral hHK hK pair hpm hpi
      _ = inner ℂ (integralCoverPullback hHK hK F) (hf.toLp f) :=
        (integral_congr_ae hae).symm
      _ = inner ℂ F (integralCoverTrace hHK hK (hf.toLp f)) :=
        (integralCoverTrace_pairing hHK hK F (hf.toLp f)).symm
  rw [←he]
  exact htr.coeFn_toLp

theorem integralCoverTrace_representative {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (G : IntegralQuotientL2 H) (f : IntegralOrbitQuotient H→ℂ) (hmeas : Measurable f)
    (hrep : G=ᵐ[integralQuotientVolume H]f) :
    integralCoverTrace hHK hK G=ᵐ[integralQuotientVolume K]integralCoverTraceFunction H K f := by
  have hf : MemLp f 2 (integralQuotientVolume H) := (memLp_congr_ae hrep).mp (Lp.memLp G)
  have he : G=hf.toLp f := Lp.ext (hrep.trans hf.coeFn_toLp.symm)
  rw [he]
  exact integralCoverTrace_toLp_ae hHK hK f hmeas hf

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def primaryDenominatorShift (a:PrimaryLower) (m:Eis) : PrimaryCoprimeDenominator a≃PrimaryCoprimeDenominator a where
  toFun d:=⟨⟨d.val.val+3*a.val*m,by
    convert (preTransparency := .instances) dvd_add d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
      exact (isCoprime_right_congr_of_dvd a.val (d.val.val+3*a.val*m) d.val.val ⟨3*m,by ring⟩).mpr d.2⟩
  invFun d:=⟨⟨d.val.val-3*a.val*m,by
    convert (preTransparency := .instances) dvd_sub d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
      exact (isCoprime_right_congr_of_dvd a.val (d.val.val-3*a.val*m) d.val.val ⟨-(3*m),by ring⟩).mpr d.2⟩
  left_inv d:=by apply Subtype.ext;apply Subtype.ext;dsimp;ring
  right_inv d:=by apply Subtype.ext;apply Subtype.ext;dsimp;ring

def unitLowerDataShift (m:Eis) : UnitLowerData≃UnitLowerData :=
  Equiv.sigmaCongrRight (fun a=>primaryDenominatorShift a m)

lemma affineCusp_term_weighted_period (h q r:Eis) (j n:ℕ) (a d:PrimaryLower) (m:Eis)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (z:ℂ) (v:ℝ) (s:ℂ) :
    affineLowerTerm q r z v s a.val (d.val+3*a.val*(q*m))*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
      affineLowerTerm q r (z+3*eisEmbedding m) v s a.val d.val*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m)) := by
  have hd:(3:Eis)∣d.val-a.val:=by simpa only [sub_sub_sub_cancel_right] using dvd_sub d.2 a.2
  obtain ⟨x,hx⟩:=hd
  have hdx:d.val=a.val+3*x:=by linear_combination hx
  have hb:(3:Eis)∣h+ramifiedAffineParameter j n*q*a.val:=by
    convert (preTransparency := .instances) dvd_add hbase (a.2.mul_left (ramifiedAffineParameter j n*q)) using 1 ;ring
  obtain ⟨ell,hell⟩:=hb
  have he:=affineCusp_general_weighted_translate h q r a.val ell x (q*m) j n
    (primaryLower_primary a) hq hr hell.symm z v s
  have hqm:Ideal.Quotient.mk (Ideal.span {q}) (q*m)=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_mul_right q m))
  rw [hqm,AddChar.map_zero_eq_one,one_mul] at he
  have hshift:3*eisEmbedding (q*m)/eisEmbedding q=3*eisEmbedding m:=by
    rw [map_mul]
    field_simp [eisEmbedding_ne_zero hq]
  rw [hshift] at he
  rw [hdx,show a.val+3*x+3*a.val*(q*m)=a.val+3*(x+a.val*(q*m)) by ring]
  exact he

def affineCuspBlock (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) : ℂ :=
  ∑'p:UnitLowerData,affineLowerTerm q r z v s p.1.val p.2.val.val

lemma affineCuspBlock_weighted_periodic (h q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (v:ℝ) (s:ℂ) (m:Eis) (z:ℂ) :
    affineCuspBlock q r (z+3*eisEmbedding m) v s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
      affineCuspBlock q r z v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  rw [affineCuspBlock,affineCuspBlock,←tsum_mul_right,←tsum_mul_right]
  calc
    _ = ∑'p:UnitLowerData,affineLowerTerm q r z v s
      ((unitLowerDataShift (q*m) p).1.val) ((unitLowerDataShift (q*m) p).2.val.val)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
      apply tsum_congr
      intro p
      exact (affineCusp_term_weighted_period h q r j n p.1 p.2.val m hq hr hbase z v s).symm
    _ = _ := (unitLowerDataShift (q*m)).tsum_eq
      (fun p:UnitLowerData=>affineLowerTerm q r z v s p.1.val p.2.val.val*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))

lemma period_integral_twisted_translation (f:ℂ→ℂ) (freq:ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)*ShortDraftTrace.breveE (-freq*(z+3*eisEmbedding n))=
      f z*ShortDraftTrace.breveE (-freq*z)) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-freq*z))=
      ShortDraftTrace.breveE (freq*b)*∫z in periodDomain,f z*ShortDraftTrace.breveE (-freq*z) := by
  let g:ℂ→ℂ:=fun z=>f z*ShortDraftTrace.breveE (-freq*z)
  have he (z:ℂ):f (z+b)*ShortDraftTrace.breveE (-freq*z)=ShortDraftTrace.breveE (freq*b)*g (b+z):=by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1;ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hp b]

end
section

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma diagonal_unit_weighted_periodic (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s:ℂ) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  simpa only [diagonal_unit_eisenstein_rows,affineCuspBlock] using
    affineCuspBlock_weighted_periodic h (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) j 0 t.ne_zero
      (by simpa using hr) hbase v s m z

lemma diagonal_once_block_expansion (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s=
    ∑l:Fin 3,affineCuspBlock (onceCuspScale t*omega^l.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) z v s := by
  have hsum:=(diagonalOnceCuspIndex u t).summable_iff.mpr
    (summable_summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s hs)
  have ht:Summable (fun p:OnceRamifiedData=>affineLowerTerm (onceCuspScale t*omega^p.1.val)
      ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val):=
    hsum.congr (fun p=>diagonal_once_summand u t z v hv s p)
  rw [mul_assoc,diagonal_once_eisenstein_rows,ht.tsum_prod,tsum_fintype]
  rfl

lemma diagonal_once_weighted_periodic (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (m:Eis) (z:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection (z+3*eisEmbedding m) v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding m))=
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  rw [diagonal_once_block_expansion u t _ v hv s hs,diagonal_once_block_expansion u t _ v hv s hs,
    Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  exact affineCuspBlock_weighted_periodic h (onceCuspScale t*omega^l.val)
    ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)) (onceCuspRayIndex u t l).val 1
      (mul_ne_zero (onceCusp_scale_ne_zero t) (pow_ne_zero _ (omega_primitive.isUnit (by decide)).ne_zero))
      (by simpa only [pow_one] using onceCuspRayIndex_spec u t l)
      (onceCusp_period_congruence t l h _ hfreq) v s m z

lemma diagonal_unit_fourier_shift (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s b:ℂ) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_unit_weighted_periodic u t j h hr hbase v hv s) b

lemma diagonal_once_fourier_shift (u t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (v:ℝ) (hv:0<v) (s b:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection (z+b) v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
            ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation
    (fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s)
    (ninthCuspFrequency h) (diagonal_once_weighted_periodic u t h hfreq v hv s hs) b

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspRoot (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else ramifiedOmegaUnit

def ramifiedCuspScaleUnit (b:Bool) : Eisˣ := if b then ramifiedOmegaUnit^2 else -ramifiedOmegaUnit

def ramifiedCuspDirectIndex (b:Bool) : ℕ := if b then 2 else 1

def ramifiedCuspOppositeIndex (b:Bool) : ℕ := if b then 1 else 2

lemma ramified_omega_four : omega^4=omega := by
  rw [show (4:ℕ)=3+1 from rfl,pow_add,omega_primitive.pow_eq_one,pow_one,one_mul]

lemma ramifiedCuspRoot_val (b:Bool) : (ramifiedCuspRoot b:Eis)=omega^(ramifiedCuspDirectIndex b) := by
  cases b <;>simp [ramifiedCuspRoot,ramifiedCuspDirectIndex,ramifiedOmegaUnit_val]

lemma ramifiedCuspRoot_cube (b:Bool) : (ramifiedCuspRoot b:Eis)^3=1 := by
  rw [ramifiedCuspRoot_val,←pow_mul,Nat.mul_comm,pow_mul,omega_primitive.pow_eq_one,one_pow]

lemma ramifiedCuspRoot_primitive (b:Bool) :
    (ramifiedCuspRoot b:Eis)^2+(ramifiedCuspRoot b:Eis)+1=0 := by
  cases b
  · simpa [ramifiedCuspRoot,ramifiedOmegaUnit_val] using ramified_omega_relation
  · simp only [ramifiedCuspRoot,ite_true,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,←pow_mul]
    rw [show 2*2=4 from rfl,ramified_omega_four]
    linear_combination ramified_omega_relation

lemma ramifiedCuspScaleUnit_spec (b:Bool) :
    -(ramifiedCuspRoot b:Eis)*(1+2*(ramifiedCuspRoot b:Eis))=onceCuspScale (ramifiedCuspScaleUnit b) := by
  cases b
  · simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedTraceLambda,ramifiedOmegaUnit_val]
  · simp only [ramifiedCuspRoot,ramifiedCuspScaleUnit,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val,
      ramifiedTraceLambda]
    linear_combination -(2*omega^2)*ramified_omega_relation

lemma ramifiedCusp_neg_inv_square (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2=(ramifiedCuspRoot b:Eis) := by
  have hi:(↑(-(ramifiedCuspRoot b))⁻¹:Eis)=-(ramifiedCuspRoot b:Eis)^2:=by
    apply (-(ramifiedCuspRoot b)).inv_eq_of_mul_eq_one_right
    change -(ramifiedCuspRoot b:Eis)*(-(ramifiedCuspRoot b:Eis)^2)=1
    convert (preTransparency := .instances) ramifiedCuspRoot_cube b using 1 ;ring
  rw [hi]
  linear_combination (ramifiedCuspRoot b:Eis)*ramifiedCuspRoot_cube b

lemma ramifiedCusp_opposite_character (b:Bool) :
    (↑(-(ramifiedCuspRoot b))⁻¹:Eis)^2*(-(ramifiedCuspRoot b:Eis))=
      -(omega^(ramifiedCuspOppositeIndex b)) := by
  rw [ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  cases b
  · simp [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,pow_two]
  · simp only [ramifiedCuspDirectIndex,ramifiedCuspOppositeIndex,ite_true,pow_one]
    rw [mul_neg,←pow_add,show 2+2=4 from rfl,ramified_omega_four]

lemma ramifiedCusp_direct_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  cases b
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨ramifiedTraceLambda*omega^2,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspDirectIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_opposite_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  cases b
  · refine ⟨-(omega*ramifiedTraceLambda),?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring
  · refine ⟨0,?_⟩
    simp [ramifiedCuspRoot,ramifiedCuspScaleUnit,onceCuspScale,ramifiedCuspOppositeIndex,
      ramifiedAffineParameter,ramifiedOmegaUnit_val]
    ring

lemma ramifiedCusp_unit_period_constant (b:Bool) :
    (3:Eis)∣onceCuspScale (ramifiedCuspScaleUnit b)+
      ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  cases b
  · refine ⟨-omega^2,?_⟩
    simp [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,onceCuspScale,Units.val_neg,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_one,one_mul,sub_zero,
      ramifiedTraceLambda]
    linear_combination ramified_omega_relation
  · refine ⟨-omega^2,?_⟩
    simp only [ramifiedCuspScaleUnit,ramifiedCuspDirectIndex,ite_true,onceCuspScale,Units.val_pow_eq_pow_val,
      ramifiedOmegaUnit_val,ramifiedAffineParameter,Nat.cast_ofNat,Nat.cast_zero,sub_zero,
      ramifiedTraceLambda]
    linear_combination (2*omega+2)*ramified_omega_relation

end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspGaussSeries (u t:Eisˣ) (h:Eis) (s:ℂ) : ℂ :=
  ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
    unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h))

lemma unitCusp_eisenstein_fourier_base (u t:Eisˣ) (j:ℕ) (h:Eis)
    (hr:(↑u⁻¹:Eis)^2*(t:Eis)=omega^j ∨ (↑u⁻¹:Eis)^2*(t:Eis)=-(omega^j))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j 0*(t:Eis))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*unitCuspGaussSeries u t h s := by
  have hh:h=(t:Eis)*((↑t⁻¹:Eis)*h):=by simp [←mul_assoc]
  have hf:(3:Eis)∣(↑t⁻¹:Eis)*h+ramifiedAffineParameter j 0:=by
    have he:(↑t⁻¹:Eis)*(h+ramifiedAffineParameter j 0*(t:Eis))=
        (↑t⁻¹:Eis)*h+ramifiedAffineParameter j 0:=by
      rw [mul_add]
      congr 1
      calc
        _ = ((↑t⁻¹:Eis)*(t:Eis))*ramifiedAffineParameter j 0 := by ring
        _ = _ := by simp
    rw [←he]
    exact hbase.mul_left _
  rw [diagonal_unit_eisenstein_fourier u t j h ((↑t⁻¹:Eis)*h) hr hh hf v hv s hs,
    unitCuspGaussSeries]
  ring

lemma unitCuspDiagonal_one : unitCuspDiagonal (1:Eisˣ)=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;>fin_cases j <;>simp [unitCuspDiagonal]

lemma ramifiedCusp_direct_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*(ramifiedCuspRoot b:Eis) := by
  convert (preTransparency := .instances) dvd_add hf (ramifiedCusp_direct_period_constant b) using 1 ;ring

lemma ramifiedCusp_opposite_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspOppositeIndex b) 0*(-(ramifiedCuspRoot b:Eis)) := by
  convert (preTransparency := .instances) dvd_add hf (ramifiedCusp_opposite_period_constant b) using 1 ;ring

lemma ramifiedCusp_unit_base (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) :
    (3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0 := by
  convert (preTransparency := .instances) dvd_add hf (ramifiedCusp_unit_period_constant b) using 1 ;ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicKubota
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma cubeKernelLeftGlobal_injective (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Function.Injective (cubeKernelLeftGlobal p) := by
  intro x y hxy
  apply (cubeKernel_finite_covers p hp).1
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

lemma cubeKernelRightGlobal_injective (p : ActualEisensteinCubic.O) (hp : p≠0) :
    Function.Injective (cubeKernelRightGlobal p hp) := by
  intro x y hxy
  apply (cubeKernel_finite_covers p hp).2.1
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

def cubeKernelRangeEquiv (p : ActualEisensteinCubic.O) (hp : p≠0) :
    (cubeKernelLeftGlobal p).range≃*(cubeKernelRightGlobal p hp).range :=
  (MonoidHom.ofInjective (cubeKernelLeftGlobal_injective p hp)).symm.trans
    (MonoidHom.ofInjective (cubeKernelRightGlobal_injective p hp))

end CubicKubota

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeAverageMatrix_translate_lattice (p:Eis) (hp:p≠0) (q n:Eis) :
    cubeAverageMatrix p hp q*complexTranslation (3*eisEmbedding n)=cubeAverageMatrix p hp (q+n) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, cubeAverageMatrix_entries, cubeAverageMatrix_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, complexTranslation, map_add]
  ring

lemma cubeAverage_period_three (p:Eis) (hp:p≠0) (F:HyperbolicSpace→ℂ)
    (hF:∀n:Eis,∀w:HyperbolicSpace,F (complexTranslation (3*eisEmbedding n) • w)=F w)
    (n:Eis) (w:HyperbolicSpace) :
    cubeAverage p hp F (complexTranslation (3*eisEmbedding n) • w)=cubeAverage p hp F w := by
  let a:(Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}):=
    { toFun:=fun r=>r+Ideal.Quotient.mk _ n
      invFun:=fun r=>r-Ideal.Quotient.mk _ n
      left_inv:=fun r=>add_sub_cancel_right r _
      right_inv:=fun r=>sub_add_cancel r _ }
  let f (r:Eis⧸Ideal.span {p^3}):=
    F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) • w)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      F (cubeAverageMatrix p hp (GaussianShiftedPartition.representative (p^3) r) •
        (complexTranslation (3*eisEmbedding n) • w))=f (a r) := by
    rw [←mul_smul,cubeAverageMatrix_translate_lattice]
    apply cubeAverage_summand_congr p hp F hF
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    rw [map_add,GaussianShiftedPartition.representative_spec,
      GaussianShiftedPartition.representative_spec]
    rfl
  unfold cubeAverage
  congr 1
  calc
    _ = ∑' r,f (a r):=tsum_congr hpoint
    _ = ∑' r,f r:=a.tsum_eq f

end

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSource_period_three (n:Eis) (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation (3*eisEmbedding n) • w)=
      cubicSourceResidualFunction w := by
  obtain ⟨z,v,hv,rfl⟩:=upperPoint_surjective w
  rw [complexTranslation_action]
  simp only [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselFunction_period v hv z n

lemma cubicSource_period_one (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation 1 • w)=cubicSourceResidualFunction w := by
  have h:=cubicSourceResidualFunction_rational_invariant ModularGroup.T w
  change cubicSourceResidualFunction (rationalComplex ModularGroup.T • w)=_ at h
  rwa [rationalComplex_T_eq] at h

lemma cubicSource_period_finTwo (t:Fin 2) (w:HyperbolicSpace) :
    cubicSourceResidualFunction (complexTranslation (t.val:ℂ) • w)=cubicSourceResidualFunction w := by
  fin_cases t
  · have hz:complexTranslation 0=1:=by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [complexTranslation]
    simp only [Nat.cast_zero,hz,one_smul]
  · simpa using cubicSource_period_one w

lemma cubicSource_cube_period_finTwo (p:Eis) (hp:p≠0) (hprimary:lambda^2∣p-1)
    (t:Fin 2) (w:HyperbolicSpace) :
    cubeAverage p hp cubicSourceResidualFunction (complexTranslation (t.val:ℂ) • w)=
      cubeAverage p hp cubicSourceResidualFunction w := by
  fin_cases t
  · have hz:complexTranslation 0=1:=by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [complexTranslation]
    simp only [Nat.cast_zero,hz,one_smul]
  · simpa using cubeAverage_period_one p hp hprimary cubicSourceResidualFunction
      cubicSource_period_three cubicSource_period_one w

theorem cubeSource_summand_average {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (cubeAverageMatrix p hp q •
        (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=
      complexCharacter ⟨d.matrix*M⁻¹,d.congruent⟩*sourceCuspConstant M*
        (v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  have hpoint (z:ℂ):cubeAverageMatrix p hp q •
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)=
        integralComplexMatrix d.matrix •
          (cubeCuspTriangular d hp • upperPoint (3*(eisEmbedding (p^3)*z)) v hv):=by
    rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul]
  simp_rw [hpoint]
  rw [sourceCusp_average_complex_upper d.matrix (cubeCuspTriangular d hp)
    (cubeCuspTriangular_entries d hp).2.1 (p^3) (p^(2*d.exponent.val))
    (pow_ne_zero _ hp) (cubeCuspTriangular_integral_scale d hp) v hv,
    cubeCuspTriangular_height d hp v hv,sourceCuspConstant_congruent M d.matrix d.congruent]
  ring

theorem cubeSource_average_zero (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hM:sourceCuspConstant M=0) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=0 := by
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous M (p^3) v hv]
  have hz (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=0:=by
    rw [cubeSource_summand_average
      (actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary)
      hp.ne_zero v hv,hM]
    ring
  simp_rw [hz]
  simp

theorem cubeSource_primary_upper_average (A:levelTwo) (T:SL(2,Eis)) (hT:T 1 0=0)
    (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ) := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous ((A:SL(2,Eis))*T) (p^3) v hv]
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv)))=
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent:=by
    rw [cubeSource_summand_average ((d r).right_upper T hT) hp.ne_zero v hv,
      CubeCuspData.right_upper_character,CubeCuspData.right_upper_exponent]
  simp_rw [hpoint]
  have hsum:(∑' r:Eis⧸Ideal.span {p^3},
      complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩*
        sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p (d r).exponent)=
      (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
        actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p):=by
    unfold actualCubeCuspPhaseSum
    rw [←tsum_mul_left]
    apply tsum_congr
    intro r
    change _=(sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ))*
      (cubeCuspHeightWeight p (d r).exponent*complexCharacter
        ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩)
    ring
  rw [hsum]
  calc
    _=((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*
      actualCubeCuspPhaseSum A p hp hprimary (cubeCuspHeightWeight p))*
        (sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ)):=by ring
    _=_:=by rw [actualCubeCuspPhaseSum_normalized A p hp hprimary hA];ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

theorem cubeSource_levelTwo_upper_average (A:levelTwo) (T:SL(2,Eis)) (hT:T 1 0=0)
    (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix ((A:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant ((A:SL(2,Eis))*T)*(v:ℂ)^(2/3:ℂ) := by
  obtain ⟨B,hB,t,ht⟩:=exists_primary_cusp_shift A
  have hm (w:HyperbolicSpace):integralComplexMatrix ((B:SL(2,Eis))*T) • w=
      complexTranslation (t.val:ℂ) • (integralComplexMatrix ((A:SL(2,Eis))*T) • w):=by
    simp only [map_mul,mul_smul]
    exact ht (integralComplexMatrix T • w)
  have hc:sourceCuspConstant ((B:SL(2,Eis))*T)=sourceCuspConstant ((A:SL(2,Eis))*T):=by
    unfold sourceCuspConstant
    apply integral_congr_ae
    filter_upwards [] with z
    rw [hm,cubicSource_period_finTwo]
  calc
    _=∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
        (integralComplexMatrix ((B:SL(2,Eis))*T) • upperPoint (3*(eisEmbedding (p^3)*z)) v hv):=by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hm,cubicSource_cube_period_finTwo p hp.ne_zero hprimary]
    _=_:=by rw [cubeSource_primary_upper_average B T hT p hp hprimary hB v hv,hc]

theorem cubeSource_average_all_cusps (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (v:ℝ) (hv:0<v) :
    (∫z in periodDomain,cubeAverage p hp.ne_zero cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) v hv))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  by_cases hz:sourceCuspConstant M=0
  · rw [cubeSource_average_zero M p hp hprimary hz v hv,hz]
    ring
  · obtain ⟨G,j,T,hT,_,_,hM⟩:=three_cusp_decomposition M
    have hj:j=0:=by
      by_contra h
      exact hz ((sourceCuspConstant_zero_iff M G j T hT hM).mpr h)
    have he:M=(G:SL(2,Eis))*T:=by
      simpa [hj,cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using hM
    rw [he]
    exact cubeSource_levelTwo_upper_average G T hT p hp hprimary v hv

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverFiberPoint_continuous (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) : Continuous (integralCoverFiberPoint H K q) := by
  have he : integralCoverFiberPoint H K q=fun w=>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) :=
    funext (integralCoverFiberPoint_rep H K q)
  rw [he]
  exact (continuous_integralOrbitProjection H).comp
    (continuous_hyperbolic_action (integralComplexMatrix ((integralCoverRep H K q)⁻¹:SL(2,ActualEisensteinCubic.O))))

lemma integralCoverMap_fiber {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K)
    (w : HyperbolicSpace) :
    (integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w}=
      Set.range (fun q : IntegralCoverCosets H K=>integralCoverFiberPoint H K q w) := by
  ext u
  constructor
  · intro hu
    induction u using Quotient.inductionOn with
    | _ z =>
      have he : integralOrbitProjection K z=integralOrbitProjection K w := hu
      obtain ⟨k,hk⟩ := Quotient.exact he
      refine ⟨(k : IntegralCoverCosets H K),?_⟩
      change integralCoverFiberPoint H K (k : IntegralCoverCosets H K) w=integralOrbitProjection H z
      rw [integralCoverFiberPoint_mk]
      congr 1
      rw [←hk]
      exact inv_smul_smul k z
  · rintro ⟨q,rfl⟩
    exact integralCoverMap_fiberPoint hHK q w

lemma integralCoverMap_preimage_image {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (S : Set (IntegralOrbitQuotient H)) :
    (integralOrbitProjection K) ⁻¹' (integralCoverMap hHK '' S)=
      ⋃q : IntegralCoverCosets H K,(integralCoverFiberPoint H K q) ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨u,hu,huw⟩
    have hh : u∈(integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w} := huw
    rw [integralCoverMap_fiber hHK w] at hh
    obtain ⟨q,rfl⟩ := hh
    exact Set.mem_iUnion.mpr ⟨q,hu⟩
  · intro hw
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hw
    exact ⟨integralCoverFiberPoint H K q w,hq,integralCoverMap_fiberPoint hHK q w⟩

theorem integralCoverMap_isClosedMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsClosedMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  intro S hS
  have hq : Topology.IsQuotientMap (integralOrbitProjection K) := isQuotientMap_quotient_mk'
  apply hq.isCoinducing.isClosed_preimage.mp
  rw [integralCoverMap_preimage_image]
  exact isClosed_iUnion_of_finite (fun q=>hS.preimage (integralCoverFiberPoint_continuous H K q))

theorem integralCoverMap_isProperMap {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] : IsProperMap (integralCoverMap hHK) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨integralCoverMap_continuous hHK,integralCoverMap_isClosedMap hHK,?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change IsCompact ((integralCoverMap hHK) ⁻¹' {integralOrbitProjection K w})
    rw [integralCoverMap_fiber hHK w]
    exact (Set.finite_range _).isCompact

theorem integralCoverMap_compact_preimage {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K]
    (S : Set (IntegralOrbitQuotient K)) (hS : IsCompact S) :
    IsCompact ((integralCoverMap hHK) ⁻¹' S) :=
  (integralCoverMap_isProperMap hHK).isCompact_preimage hS

end

section

open MeasureTheory
open scoped Classical MatrixGroups BigOperators

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubeCuspTriangular_norm_sq_pos {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) : 0<‖cubeCuspTriangular d hp 1 1‖^2 := by
  rw [cubeCuspTriangular_norm_sq]
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hp)) _

def cubeReducedRemainder {M:SL(2,Eis)} {p q:Eis} (d:CubeCuspData M p q) (hp:p≠0)
    (z:ℂ) (v:ℝ) (hv:0<v) : ℂ :=
  sourceCuspRemainder d.matrix
    ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/‖cubeCuspTriangular d hp 1 1‖^2) (div_pos hv (cubeCuspTriangular_norm_sq_pos d hp))

lemma cubeSource_remainder_summand {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubicSourceResidualFunction (cubeAverageMatrix p hp q • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder d hp z v hv+
        sourceCuspLeadingCoefficient d.matrix*(v:ℂ)^(2/3:ℂ)*cubeCuspHeightWeight p d.exponent := by
  rw [←mul_smul,cubeCuspTriangular_factor d hp,mul_smul,
    complex_upper_triangular_action (cubeCuspTriangular d hp) (cubeCuspTriangular_entries d hp).2.1]
  unfold cubeReducedRemainder sourceCuspRemainder
  rw [cubeCuspTriangular_height d hp v hv]
  ring

lemma cubeSource_leading_sum (M:SL(2,Eis)) (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},
        let d:=actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
        sourceCuspLeadingCoefficient d.matrix*cubeCuspHeightWeight p d.exponent)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspLeadingCoefficient M := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have h:=cubeSource_average_all_cusps M p hp hprimary 1 (by norm_num)
  rw [cubeAverage_cusp_integral p hp.ne_zero cubicSourceResidualFunction
    cubicSourceResidualFunction_continuous M (p^3) 1 (by norm_num)] at h
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      (∫z in periodDomain,cubicSourceResidualFunction
        (cubeAverageMatrix p hp.ne_zero (GaussianShiftedPartition.representative (p^3) r) •
          (integralComplexMatrix M • upperPoint (3*(eisEmbedding (p^3)*z)) 1 (by norm_num))))=
      sourceCuspConstant (d r).matrix*cubeCuspHeightWeight p (d r).exponent:=by
    rw [cubeSource_summand_average (d r) hp.ne_zero 1 (by norm_num),
      ←sourceCuspConstant_congruent M (d r).matrix (d r).congruent]
    simp only [Complex.ofReal_one,Complex.one_cpow,mul_one]
  rw [tsum_congr hpoint] at h
  simp only [Complex.ofReal_one,Complex.one_cpow,mul_one] at h
  change (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3}, sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)=_
  unfold sourceCuspLeadingCoefficient
  simp_rw [div_mul_eq_mul_div]
  rw [tsum_div_const]
  calc
    _=((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},sourceCuspConstant (d r).matrix*cubeCuspHeightWeight p (d r).exponent)) /
        ((9*Real.sqrt 3/2:ℝ):ℂ):=by ring
    _=_:=by rw [h];ring

theorem cubeSource_difference_eq_remainders (M:SL(2,Eis)) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (z:ℂ) (v:ℝ) (hv:0<v) :
    cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
    (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
      (∑' r:Eis⧸Ideal.span {p^3},
        let d:=actualCubeCuspData M p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
        cubeReducedRemainder d hp.ne_zero z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp.ne_zero)
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      cubicSourceResidualFunction (cubeAverageMatrix p hp.ne_zero
        (GaussianShiftedPartition.representative (p^3) r) • (integralComplexMatrix M • upperPoint z v hv))=
      cubeReducedRemainder (d r) hp.ne_zero z v hv+(v:ℂ)^(2/3:ℂ)*
        (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent):=by
    rw [cubeSource_remainder_summand (d r) hp.ne_zero z v hv]
    ring
  have hu:cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
        (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspLeadingCoefficient M*(v:ℂ)^(2/3:ℂ):=by
    unfold cubeAverage
    have hs1:Summable (fun r:Eis⧸Ideal.span {p^3}=>cubeReducedRemainder (d r) hp.ne_zero z v hv):=Summable.of_finite
    have hs2:Summable (fun r:Eis⧸Ideal.span {p^3}=>(v:ℂ)^(2/3:ℂ)*
      (sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=Summable.of_finite
    rw [tsum_congr hpoint,hs1.tsum_add hs2,tsum_mul_left]
    calc
      _=(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},cubeReducedRemainder (d r) hp.ne_zero z v hv)+
        (v:ℂ)^(2/3:ℂ)*((Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3 *
          (∑' r:Eis⧸Ideal.span {p^3},sourceCuspLeadingCoefficient (d r).matrix*cubeCuspHeightWeight p (d r).exponent)):=by ring
      _=_:=by rw [cubeSource_leading_sum M p hp hprimary];ring
  rw [hu]
  unfold sourceCuspRemainder
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubePrime_norm_ge_one (p:Eis) (hp:p≠0) : 1≤‖eisEmbedding p‖ := by
  have hn:1≤‖eisEmbedding p‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    have hq:Ideal.absNorm (Ideal.span {p})≠0:=
      (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  nlinarith [norm_nonneg (eisEmbedding p)]

lemma cubeReducedRemainder_bound {M:SL(2,Eis)} {p q:Eis}
    (d:CubeCuspData M p q) (hp:p≠0) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeReducedRemainder d hp z v hv‖≤K*‖eisEmbedding p‖^9/v^3 := by
  let D:=‖cubeCuspTriangular d hp 1 1‖^2
  have hD:0<D:=cubeCuspTriangular_norm_sq_pos d hp
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp
  have hd:D≤‖eisEmbedding p‖^3:=by
    rw [show D=‖eisEmbedding p‖^(3-2*(d.exponent.val:ℝ)) from cubeCuspTriangular_norm_sq d hp]
    rw [←Real.rpow_natCast ‖eisEmbedding p‖ 3]
    apply Real.rpow_le_rpow_of_exponent_le hr1
    norm_num only [Nat.cast_ofNat]
    have hj:0≤(d.exponent.val:ℝ):=Nat.cast_nonneg _
    linarith
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v/D:=by
    apply (le_div_iff₀ hD).mpr
    calc
      _≤(‖eisEmbedding p‖^3)⁻¹*‖eisEmbedding p‖^3:=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (pow_nonneg hr.le 3))
      _=1:=inv_mul_cancel₀ (pow_ne_zero 3 hr.ne')
      _≤v:=hv1
  have hb:=sourceCuspRemainder_bound_all K (‖eisEmbedding p‖^3)⁻¹ hrep
    d.matrix ((cubeCuspTriangular d hp 0 0*z+cubeCuspTriangular d hp 0 1)/cubeCuspTriangular d hp 1 1)
    (v/D) (div_pos hv hD) ha
  change ‖cubeReducedRemainder d hp z v hv‖≤K/(v/D)^3 at hb
  refine hb.trans ?_
  have hd3:D^3≤‖eisEmbedding p‖^9:=by
    calc
      _≤(‖eisEmbedding p‖^3)^3:=pow_le_pow_left₀ hD.le hd 3
      _=_:=by ring
  calc
    K/(v/D)^3=K*D^3/v^3:=by field_simp
    _≤K*‖eisEmbedding p‖^9/v^3:=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd3 hK) (pow_nonneg hv.le 3)

lemma cube_normalized_sum_bound (p:Eis) (hp:p≠0)
    (f:(Eis⧸Ideal.span {p^3})→ℂ) (B:ℝ) (_hB:0≤B) (hf:∀r,‖f r‖≤B) :
    ‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹^3*(∑' r,f r)‖≤B := by
  let:Finite (Eis⧸Ideal.span {p^3}):=finite_quotient_span (pow_ne_zero 3 hp)
  have hqN:Ideal.absNorm (Ideal.span {p})≠0:=
    (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
  have hq:(Ideal.absNorm (Ideal.span {p}):ℝ)≠0:=by exact_mod_cast hqN
  have hs:‖∑' r,f r‖≤(Ideal.absNorm (Ideal.span {p}):ℝ)^3*B:=by
    calc
      _≤∑' r,‖f r‖:=norm_tsum_le_tsum_norm (Summable.of_finite)
      _≤∑' (_:Eis⧸Ideal.span {p^3}),B:=(Summable.of_finite).tsum_le_tsum hf Summable.of_finite
      _=_:=by
        rw [tsum_const,nsmul_eq_mul]
        change (Ideal.absNorm (Ideal.span {p^3}):ℝ)*B=_
        rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rw [norm_mul,norm_pow,norm_inv,Complex.norm_natCast]
  calc
    _≤(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹^3*((Ideal.absNorm (Ideal.span {p}):ℝ)^3*B):=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 3)
    _=B:=by field_simp

theorem cubeSource_difference_decay_from_representatives (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (K:ℝ) (hK:0≤K)
    (hrep:∀j:Fin 3,∀z:ℂ,∀v:ℝ,∀hv:0<v,(‖eisEmbedding p‖^3)⁻¹≤v→
      ‖sourceCuspRemainder (cuspRepresentative j) z v hv‖≤K/v^3)
    (M:SL(2,Eis)) (z:ℂ) (v:ℝ) (hv:0<v) (hv1:1≤v) :
    ‖cubeAverage p hp.ne_zero cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)-
      (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*cubicSourceResidualFunction (integralComplexMatrix M • upperPoint z v hv)‖≤
    (K*(‖eisEmbedding p‖^9+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹))/v^3 := by
  have hr:0<‖eisEmbedding p‖:=norm_pos_iff.mpr (eisEmbedding_ne_zero hp.ne_zero)
  have hr1:1≤‖eisEmbedding p‖:=cubePrime_norm_ge_one p hp.ne_zero
  have ha:(‖eisEmbedding p‖^3)⁻¹≤v:=by
    calc
      _≤1:=inv_le_one_of_one_le₀ (one_le_pow₀ hr1)
      _≤v:=hv1
  have hbase:=sourceCuspRemainder_bound_all K _ hrep M z v hv ha
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData M p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hsum:=cube_normalized_sum_bound p hp.ne_zero
    (fun r=>cubeReducedRemainder (d r) hp.ne_zero z v hv) (K*‖eisEmbedding p‖^9/v^3)
    (by positivity) (fun r=>cubeReducedRemainder_bound (d r) hp.ne_zero K hK hrep z v hv hv1)
  have hrest:‖(Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹*sourceCuspRemainder M z v hv‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=by
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Nat.cast_nonneg _))
  rw [cubeSource_difference_eq_remainders M p hp hprimary z v hv]
  refine (norm_sub_le _ _).trans ?_
  calc
    _≤K*‖eisEmbedding p‖^9/v^3+(Ideal.absNorm (Ideal.span {p}):ℝ)⁻¹*(K/v^3):=
      add_le_add hsum hrest
    _=_:=by ring

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverMap_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient K→ℂ)
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun q=>f (integralCoverMap hHK q)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (integralCoverMap_compact_preimage hHK (tsupport f) hf.isCompact)
  intro q hq
  exact subset_tsupport f hq

lemma integralCoverTraceFunction_hasCompactSupport {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) [H.IsFiniteRelIndex K] (f : IntegralOrbitQuotient H→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (integralCoverTraceFunction H K f) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply HasCompactSupport.of_support_subset_isCompact
    (hf.isCompact.image (integralCoverMap_continuous hHK))
  intro q hq
  induction q using Quotient.inductionOn with
  | _ w =>
    change (∑r : IntegralCoverCosets H K,f (integralCoverFiberPoint H K r w))≠0 at hq
    obtain ⟨r,_,hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    exact ⟨integralCoverFiberPoint H K r w,subset_tsupport f hr,
      integralCoverMap_fiberPoint hHK r w⟩

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceFunction (f : KernelQuotient→ℂ) : KernelQuotient→ℂ :=
  integralCoverTraceFunction H globalKubotaKernel
    (fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q)))

omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_lift (f : KernelQuotient→ℂ) (w : HyperbolicSpace) :
    kernelCorrespondenceFunction hJK e g he f (integralOrbitProjection globalKubotaKernel w)=
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑q : IntegralCoverCosets H globalKubotaKernel,
        f (integralOrbitProjection globalKubotaKernel
          ((g*integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹:
              globalKubotaKernel):SL(2,ActualEisensteinCubic.O)))•w)) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change (∑q : IntegralCoverCosets H globalKubotaKernel,
    f (integralCoverMap hJK (integralConjugateMap e g he
      (integralCoverFiberPoint H globalKubotaKernel q w))))=_
  apply Finset.sum_congr rfl
  intro q _
  rw [integralCoverFiberPoint_rep,integralSubgroup_smul,
    integralConjugateMap_projection,integralCoverMap_projection,mul_smul]

include hHK in
lemma kernelCorrespondenceFunction_hasCompactSupport (f : KernelQuotient→ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (kernelCorrespondenceFunction hJK e g he f) := by
  apply integralCoverTraceFunction_hasCompactSupport hHK
  exact (integralCoverMap_hasCompactSupport hJK f hf).comp_homeomorph
    (integralConjugateHomeomorph e g he)

omit [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondenceFunction_contMDiff (f : KernelQuotient→ℂ)
    (hf : ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ f) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℂ) ∞ (kernelCorrespondenceFunction hJK e g he f) := by
  let : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  apply kernel_contMDiff_of_lift
  simp_rw [kernelCorrespondenceFunction_lift]
  apply ContMDiff.sum
  intro q _
  exact (hf.comp kernelProjection_contMDiff).comp
    (hyperbolicAction_contMDiff (g*integralComplexMatrix
      (((integralCoverRep H globalKubotaKernel q)⁻¹:globalKubotaKernel):SL(2,ActualEisensteinCubic.O))))

def kernelCorrespondenceTest (f : kernelSmoothTests) : kernelSmoothTests :=
  ⟨kernelCorrespondenceFunction hJK e g he f.1,
    kernelCorrespondenceFunction_contMDiff hJK e g he f.1 f.2.1,
    kernelCorrespondenceFunction_hasCompactSupport hHK hJK e g he f.1 f.2.2⟩

end CubicEisenstein

end

end OAI
end

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma integralCoverMap_quasiMeasurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    Measure.QuasiMeasurePreserving (integralCoverMap hHK)
      (integralQuotientVolume H) (integralQuotientVolume K) := by
  refine ⟨integralCoverMap_measurable hHK,?_⟩
  rw [integralCoverMap_measure hHK hK]
  exact Measure.smul_absolutelyContinuous

variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceL2 : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  (integralCoverTrace hHK globalKubotaKernel_le_levelThree).comp
    ((integralConjugatePullback e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).toContinuousLinearMap.comp
      (integralCoverPullback hJK globalKubotaKernel_le_levelThree))

lemma kernelCorrespondenceL2_representative (F : KernelQuotientL2)
    (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel]f) :
    kernelCorrespondenceL2 hHK hJK e g he F=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCorrespondenceFunction hJK e g he f := by
  have hcover := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK
      globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  have hconj := (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree)
      (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hcover)
  exact integralCoverTrace_representative hHK globalKubotaKernel_le_levelThree _ _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

lemma kernelCorrespondenceTest_mass (f : kernelSmoothTests) :
    kernelSmoothTestsToL2 (kernelCorrespondenceTest hHK hJK e g he f)=
      kernelCorrespondenceL2 hHK hJK e g he (kernelSmoothTestsToL2 f) := by
  apply Lp.ext
  exact (kernelSmoothTests_memLp (kernelCorrespondenceTest hHK hJK e g he f)).coeFn_toLp.trans
    (kernelCorrespondenceL2_representative hHK hJK e g he _ f.1
      f.2.1.continuous.measurable (kernelSmoothTests_memLp f).coeFn_toLp).symm

include hHK in
lemma kernelCorrespondenceFunction_integrable (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    Integrable (kernelCorrespondenceFunction hJK e g he f)
      (integralQuotientVolume globalKubotaKernel) := by
  have hcover := (integralCoverMap_measurePreserving hJK
    globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hconj := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hcover
  exact integralCoverTraceFunction_integrable hHK globalKubotaKernel_le_levelThree _
    ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj

include hHK in
lemma kernelCorrespondenceFunction_integral (f : KernelQuotient→ℂ) (hf : Measurable f)
    (hi : Integrable f (integralQuotientVolume globalKubotaKernel)) :
    (∫q,kernelCorrespondenceFunction hJK e g he f q∂integralQuotientVolume globalKubotaKernel)=
      (J.relIndex globalKubotaKernel:ℂ)*(∫q,f q∂integralQuotientVolume globalKubotaKernel) := by
  have hcover := (integralCoverMap_measurePreserving hJK
    globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    (hi.smul_measure (c:=(J.relIndex globalKubotaKernel:ℝ≥0∞)) (by simp))
  have hconj := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hcover
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree)
    (hJK.trans globalKubotaKernel_le_levelThree)
  change Integrable (fun q=>f (integralCoverMap hJK (integralConjugateMap e g he q))) _ at hconj
  calc
    _ = ∫q,f (integralCoverMap hJK (integralConjugateMap e g he q))∂integralQuotientVolume H :=
      integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
        ((hf.comp (integralCoverMap_measurable hJK)).comp (integralConjugateMap_measurable e g he)) hconj
    _ = ∫q,f (integralCoverMap hJK q)∂integralQuotientVolume J := by
      have hh := integral_map («μ»:=integralQuotientVolume H) hm.measurable.aemeasurable
        (hf.comp (integralCoverMap_measurable hJK)).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = ∫q,f q∂Measure.map (integralCoverMap hJK) (integralQuotientVolume J) :=
      (integral_map (integralCoverMap_measurable hJK).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by
      rw [integralCoverMap_measure hJK globalKubotaKernel_le_levelThree,
        integral_smul_measure]
      simp only [ENNReal.toReal_natCast,Complex.real_smul,Complex.ofReal_natCast]

end

def coverEnergyDensity (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℝ :=
  euclideanScalarDirichletDensity (fun x=>(F x).re) p+
    euclideanScalarDirichletDensity (fun x=>(F x).im) p

def coverGradientAt (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial) :
    EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun j=>(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))

lemma coverGradientAt_norm_sq (F : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (hF : DifferentiableAt ℝ F p) :
    ‖coverGradientAt F p‖^2=coverEnergyDensity F p := by
  have hr := (Complex.reCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp p hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun x=>(F x).re) p=_ at hr
  change fderiv ℝ (fun x=>(F x).im) p=_ at hi
  unfold coverEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑j:Fin 3,‖(p 2:ℂ)*fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change ‖fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2=
    (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).re^2+
      (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j)).im^2
  simpa only [Complex.normSq_apply,pow_two] using
    (Complex.normSq_eq_norm_sq (fderiv ℝ F p (EuclideanSpace.basisFun (Fin 3) ℝ j))).symm

lemma coverEnergyDensity_comp (g : SL(2,ℂ)) (F : EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hp : 0<p 2)
    (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    coverEnergyDensity (F ∘ euclideanAction g) p=coverEnergyDensity F (euclideanAction g p) := by
  have hr := hyperbolic_cotangent_energy_comp g (fun p=>(F p).re) p hp
    (Complex.reCLM.differentiableAt.comp _ hF)
  have hi := hyperbolic_cotangent_energy_comp g (fun p=>(F p).im) p hp
    (Complex.imCLM.differentiableAt.comp _ hF)
  exact congrArg₂ (fun x y : ℝ=>x+y) hr hi

lemma coverGradientAt_sum {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverGradientAt (fun x=>∑i∈s,F i x) p=∑i∈s,coverGradientAt (F i) p := by
  apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
  funext j
  simp only [coverGradientAt,fderiv_fun_sum hF,_root_.sum_apply,
    WithLp.equiv_apply,Finset.mul_sum,WithLp.ofLp_sum,Finset.sum_apply]

lemma norm_sum_sq_le_card {ι E : Type*} [NormedAddCommGroup E]
    (s : Finset ι) (f : ι→E) :
    ‖∑i∈s,f i‖^2≤(s.card:ℝ)*∑i∈s,‖f i‖^2 := by
  calc
    _ ≤ (∑i∈s,‖f i‖)^2 := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mpr
      (norm_sum_le _ _)
    _ ≤ _ := by
      simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq s (fun _=> (1:ℝ)) (fun i=>‖f i‖))

lemma coverEnergyDensity_sum_le {ι : Type*} (s : Finset ι) (F : ι→EuclideanSpatial→ℂ)
    (p : EuclideanSpatial) (hF : ∀i∈s,DifferentiableAt ℝ (F i) p) :
    coverEnergyDensity (fun x=>∑i∈s,F i x) p≤(s.card:ℝ)*∑i∈s,coverEnergyDensity (F i) p := by
  rw [←coverGradientAt_norm_sq _ _ (DifferentiableAt.fun_sum hF),coverGradientAt_sum s F p hF]
  have hh := norm_sum_sq_le_card s (fun i=>coverGradientAt (F i) p)
  calc
    _ ≤ _ := hh
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact coverGradientAt_norm_sq (F i) p (hF i hi)

lemma kernelTestEnergyDensity_eq_cover (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=coverEnergyDensity (kernelTestField f) (hyperbolicEuclideanCoordinates w) := rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rational_unipotent_upper (n:ℕ) :
    rationalEmbedding (ModularGroup.T^n)=unitCuspUpper (n:Eis) := by
  rw [←rationalUnipotent_nat]
  apply Subtype.ext
  change ( !![(1 : ℤ), (n : ℤ); 0, 1]).map (Int.castRingHom Eis) =
    !![1, (n : Eis); 0, 1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

lemma rational_cusp_lower_section (u:Eisˣ) (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
      integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv=
      integralComplexMatrix (unitCuspDiagonal (-u))*
        integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis))))*
          upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv := by
  have hm:=congrArg integralComplexMatrix (rational_cusp_lower_factor u (n:ℤ))
  simp only [map_mul,Int.cast_natCast] at hm
  have hu:integralComplexMatrix (unitCuspUpper (n:Eis))=rationalComplex (ModularGroup.T^n):=by
    rw [←rational_unipotent_upper]
    rfl
  rw [hu] at hm
  change rationalComplex ModularGroup.S*rationalComplex (ModularGroup.T^n)*
    integralComplexMatrix (lowerCuspMatrix (u:Eis))=_ at hm
  rw [hm,mul_assoc,unitCuspUpper_section]

lemma hyperbolicEisenstein_fixed_upper (g:SL(2,ℂ)) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    hyperbolicEisenstein s (g • upperPoint z v hv)=eisenstein (g*upperSection z v hv) s:=rfl

theorem sourceEisenstein_unit_lower (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        ∑n:Fin 3,eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)*(1+(n.val:Eis)*(u:Eis))))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_four_cusps]
  simp only [←mul_smul,hyperbolicEisenstein_fixed_upper]
  apply congrArg (fun c:ℂ=>(4:ℂ)⁻¹*(eisenstein
    (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+c))
  apply Finset.sum_congr rfl
  intro n hn
  rw [←mul_assoc,rational_cusp_lower_section]

theorem sourceEisenstein_primitive_lower_four (u t:Eisˣ)
    (hu:(u:Eis)^2+(u:Eis)+1=0)
    (ht:-(u:Eis)*(1+2*(u:Eis))=onceCuspScale t)
    (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    sourceEisenstein s (integralComplexMatrix (lowerCuspMatrix (u:Eis)) • upperPoint z v hv)=
      (4:ℂ)⁻¹*(eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (-(u:Eis)))*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s+
        eisenstein (integralComplexMatrix (unitCuspDiagonal (-u))*
          integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*
            upperSection (z+eisEmbedding (↑u⁻¹:Eis)) v hv) s) := by
  rw [sourceEisenstein_unit_lower,Fin.sum_univ_three]
  have h1:-(u:Eis)*(1+1*(u:Eis))=1:=by linear_combination -hu
  simp only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
    zero_mul,add_zero,mul_one,h1,ht]
  ring

lemma continuous_fixed_left_Eisenstein (g:SL(2,ℂ)) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (b:ℂ) :
    Continuous (fun z:ℂ=>eisenstein (g*upperSection (z+b) v hv) s) := by
  have hc:Continuous (fun z:ℂ=>(⟨(z+b,v),hv⟩:UpperCoordinates)):=by fun_prop
  have he : Continuous (fun z:ℂ=>hyperbolicEisenstein s (g • upperPoint (z+b) v hv)) := by
    simpa only [Function.comp_def] using
      ((hyperbolicEisenstein_continuous s hs).comp (continuous_translatedUpperCoordinates g)).comp hc
  simpa only [hyperbolicEisenstein_fixed_upper] using he

lemma integrable_fixed_left_Eisenstein_fourier (g:SL(2,ℂ)) (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (b freq:ℂ) :
    IntegrableOn (fun z:ℂ=>eisenstein (g*upperSection (z+b) v hv) s*ShortDraftTrace.breveE (-freq*z)) periodDomain := by
  apply periodDomain_integrable_of_continuous
  apply (continuous_fixed_left_Eisenstein g v hv s hs b).mul
  change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
  fun_prop

end

section
open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedCuspGaussSeries (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b)) (s:ℂ) : ℂ :=
  (4:ℂ)⁻¹*(unitCuspGaussSeries 1 (ramifiedCuspRoot b) h s+
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (↑(ramifiedCuspRoot b)⁻¹:Eis))*
      (unitCuspGaussSeries (-(ramifiedCuspRoot b)) (-(ramifiedCuspRoot b)) h s+
        unitCuspGaussSeries (-(ramifiedCuspRoot b)) 1 h s+
          onceCuspGaussSeries (-(ramifiedCuspRoot b)) (ramifiedCuspScaleUnit b) h hf s))

theorem ramifiedSourceEisenstein_fourier (b:Bool) (h:Eis)
    (hf:(3:Eis)∣h-onceCuspScale (ramifiedCuspScaleUnit b))
    (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) :
    (∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot b:Eis)) • upperPoint z v hv)*
        ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*ramifiedCuspGaussSeries b h hf s := by
  let t:=ramifiedCuspRoot b
  let shift:=eisEmbedding (↑t⁻¹:Eis)
  let arch:=(v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v)
  let f0:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (lowerCuspMatrix (t:Eis))*upperSection z v hv) s*
    ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f1:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (-(t:Eis)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f2:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix 1)*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  let f3:ℂ→ℂ:=fun z=>eisenstein (integralComplexMatrix (unitCuspDiagonal (-t))*
    integralComplexMatrix (lowerCuspMatrix (onceCuspScale (ramifiedCuspScaleUnit b)))*upperSection (z+shift) v hv) s*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)
  have hi0:IntegrableOn f0 periodDomain:=by
    simpa only [f0,add_zero] using integrable_fixed_left_Eisenstein_fourier
      (integralComplexMatrix (lowerCuspMatrix (t:Eis))) v hv s hs 0 (ninthCuspFrequency h)
  have hi1:IntegrableOn f1 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi2:IntegrableOn f2 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have hi3:IntegrableOn f3 periodDomain:=integrable_fixed_left_Eisenstein_fourier _ v hv s hs shift _
  have heq:(∫z in periodDomain,sourceEisenstein s
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)) • upperPoint z v hv)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      (4:ℂ)⁻¹*((∫z in periodDomain,f0 z)+(∫z in periodDomain,f1 z)+
        (∫z in periodDomain,f2 z)+(∫z in periodDomain,f3 z)):=by
    calc
      _ = ∫z in periodDomain,(4:ℂ)⁻¹*(f0 z+f1 z+f2 z+f3 z) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z=>by
          dsimp only
          rw [sourceEisenstein_primitive_lower_four t (ramifiedCuspScaleUnit b)
            (ramifiedCuspRoot_primitive b) (ramifiedCuspScaleUnit_spec b)]
          dsimp only [f0,f1,f2,f3,shift]
          ring)
      _ = _ := by
        rw [integral_const_mul]
        rw [integral_add (f:=fun z=>f0 z+f1 z+f2 z) (g:=f3) ((hi0.add hi1).add hi2) hi3,
          integral_add (f:=fun z=>f0 z+f1 z) (g:=f2) (hi0.add hi1) hi2,
          integral_add (f:=f0) (g:=f1) hi0 hi1]
  have hr0:(↑(1:Eisˣ)⁻¹:Eis)^2*(t:Eis)=omega^(ramifiedCuspDirectIndex b):=by
    simpa [t] using ramifiedCuspRoot_val b
  have hr1:(↑(-t)⁻¹:Eis)^2*((-t:Eisˣ):Eis)=-(omega^(ramifiedCuspOppositeIndex b)):=
    ramifiedCusp_opposite_character b
  have hr2:(↑(-t)⁻¹:Eis)^2*((1:Eisˣ):Eis)=omega^(ramifiedCuspDirectIndex b):=by
    rw [Units.val_one,mul_one,ramifiedCusp_neg_inv_square,ramifiedCuspRoot_val]
  have hb2:(3:Eis)∣h+ramifiedAffineParameter (ramifiedCuspDirectIndex b) 0*((1:Eisˣ):Eis):=by
    simpa using ramifiedCusp_unit_base b h hf
  have h0:(∫z in periodDomain,f0 z)=arch*unitCuspGaussSeries 1 t h s:=by
    simpa only [unitCuspDiagonal_one,map_one,one_mul,f0,arch] using
      unitCusp_eisenstein_fourier_base 1 t (ramifiedCuspDirectIndex b) h (Or.inl hr0)
        (ramifiedCusp_direct_base b h hf) v hv s hs
  have h1:(∫z in periodDomain,f1 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) (-t) h s):=by
    have he:=diagonal_unit_fourier_shift (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
      (ramifiedCusp_opposite_base b h hf) v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) (-t) (ramifiedCuspOppositeIndex b) h (Or.inr hr1)
        (ramifiedCusp_opposite_base b h hf) v hv s hs] at he
    simpa only [f1,Units.val_neg,arch] using he
  have h2:(∫z in periodDomain,f2 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*unitCuspGaussSeries (-t) 1 h s):=by
    have he:=diagonal_unit_fourier_shift (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
      hb2 v hv s shift
    rw [unitCusp_eisenstein_fourier_base (-t) 1 (ramifiedCuspDirectIndex b) h (Or.inl hr2)
        hb2 v hv s hs] at he
    simpa only [f2,Units.val_one,arch] using he
  have h3:(∫z in periodDomain,f3 z)=ShortDraftTrace.breveE (ninthCuspFrequency h*shift)*
      (arch*onceCuspGaussSeries (-t) (ramifiedCuspScaleUnit b) h hf s):=by
    dsimp only [f3]
    rw [diagonal_once_fourier_shift (-t) (ramifiedCuspScaleUnit b) h hf v hv s shift hs,
      onceCusp_eisenstein_fourier (-t) (ramifiedCuspScaleUnit b) h hf v hv s hs]
  rw [heq,h0,h1,h2,h3]
  dsimp only [ramifiedCuspGaussSeries,arch,shift,t]
  ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

local notation "Eis" => ActualEisensteinCubic.O

theorem finite_unramified_residue {ι:Type*} [Fintype ι] [DecidableEq ι]
    (index:ι→Eis) (coefficient:ι→ℂ→ℂ)
    (hc:∀i s,1<s.re→AnalyticAt ℂ (coefficient i) s)
    (f:ℂ→ℂ) (R:ℂ)
    (hf:∀s,1<s.re→0<s.im→AnalyticAt ℂ f s)
    (hlim:Tendsto (fun s:ℂ=>(s-4/3)*f s) (𝓝[≠] (4/3:ℂ)) (𝓝 R))
    (hinit:∀s:ℂ,4<s.re→0<s.im→
      f s=∑i,coefficient i s*unramifiedCubicGaussSeries s (index i)) :
    R=∑i,coefficient i (4/3)*unramifiedGaussResidue (index i) := by
  let H:ι→ℂ→ℂ:=fun i s=>cuspWhittakerHeightFactor s (3*index i)
  let G:ι→ℂ→ℂ:=fun i s=>translatedCuspFamily (3*index i) oppositeSource 2 3
    (by norm_num) (by norm_num) s
  let D:ℂ→ℂ:=fun s=>∏i,H i s
  let E:ι→ℂ→ℂ:=fun i s=>∏j∈Finset.univ.erase i,H j s
  have hH:∀i s,1<s.re→AnalyticAt ℂ (H i) s:=fun i s hs=>
    cuspWhittakerHeightFactor_analyticAt (3*index i) s hs
  have hD:∀s,1<s.re→AnalyticAt ℂ D s:=fun s hs=>
    Finset.analyticAt_fun_prod _ (fun i hi=>hH i s hs)
  have hE:∀i s,1<s.re→AnalyticAt ℂ (E i) s:=fun i s hs=>
    Finset.analyticAt_fun_prod _ (fun j hj=>hH j s hs)
  have hprod (i:ι) (s:ℂ):H i s*E i s=D s:=by
    exact Finset.mul_prod_erase Finset.univ (fun j=>H j s) (Finset.mem_univ i)
  let domain:Set ℂ:={s|1<s.re∧0<s.im}
  have hconvex:Convex ℝ domain:=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have ha:AnalyticOnNhd ℂ (fun s=>f s*D s) domain:=fun s hs=>(hf s hs.1 hs.2).mul (hD s hs.1)
  have hb:AnalyticOnNhd ℂ (fun s=>∑i,coefficient i s*G i s*E i s) domain:=by
    intro s hs
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact ((hc i s hs.1).mul (translatedCuspFamily_analyticAt_nonreal (3*index i)
      oppositeSource 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')).mul (hE i s hs.1)
  have hopen:IsOpen {s:ℂ|4<s.re∧0<s.im}:=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev:(fun s=>f s*D s)=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>∑i,coefficient i s*G i s*E i s):=by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [hinit s hs.1 hs.2,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [G]
    rw [translatedCuspFamily_opposite_initial (index i) s hs.1 hs.2]
    change coefficient i s*unramifiedCubicGaussSeries s (index i)*D s=
      coefficient i s*(unramifiedCubicGaussSeries s (index i)*H i s)*E i s
    rw [←hprod i s]
    ring
  have heq:=ha.eqOn_of_preconnected_of_eventuallyEq hb hconvex.isPreconnected
    (show (5+Complex.I:ℂ)∈domain by norm_num [domain]) hev
  have hDc:Tendsto D (𝓝[≠] (4/3:ℂ)) (𝓝 (D (4/3))):=
    (hD (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl:=(hlim.mul hDc).comp upperVertical_tendsto_cubic_punctured
  have hg:∀i,Tendsto (fun s:ℂ=>coefficient i s*((s-4/3)*G i s)*E i s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
        cubicEisensteinResidue*E i (4/3))):=by
    intro i
    exact (((hc i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      (translatedCuspFamily_residue_limit (3*index i) oppositeSource 2 3
        (by norm_num) (by norm_num))).mul
          ((hE i (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hr:=(tendsto_finsetSum Finset.univ (fun i hi=>hg i)).comp upperVertical_tendsto_cubic_punctured
  have hel:(fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*f ((4/3:ℂ)+(t:ℂ)*Complex.I))*
      D ((4/3:ℂ)+(t:ℂ)*Complex.I))=ᶠ[𝓝[>] (0:ℝ)]
      (fun t:ℝ=>∑i,coefficient i ((4/3:ℂ)+(t:ℂ)*Complex.I)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*G i ((4/3:ℂ)+(t:ℂ)*Complex.I))*
          E i ((4/3:ℂ)+(t:ℂ)*Complex.I)):=by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0:0<t:=ht
    have he:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
      constructor
      · norm_num
      · simpa using ht0)
    dsimp only at he
    rw [mul_assoc,he,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hres:=tendsto_nhds_unique_of_eventuallyEq hl hr hel
  have hDn:D (4/3)≠0:=Finset.prod_ne_zero_iff.mpr (fun i hi=>
    cuspWhittakerHeightFactor_center_ne_zero (3*index i))
  apply mul_right_cancel₀ hDn
  rw [Finset.sum_mul]
  refine hres.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  change coefficient i (4/3)*translatedCuspFourier (3*index i) oppositeSource
    cubicEisensteinResidue*E i (4/3)=coefficient i (4/3)*
      (translatedCuspFourier (3*index i) oppositeSource cubicEisensteinResidue/H i (4/3))*D (4/3)
  rw [←hprod i (4/3)]
  field_simp [show H i (4/3)≠0 from cuspWhittakerHeightFactor_center_ne_zero (3*index i)]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota

lemma cuspStrip_integrable_continuous (a b:ℝ) (ha:0<a)
    (f:HyperbolicSpace→ℂ) (hf:Continuous f) :
    IntegrableOn f (cuspPeriodStrip a b) hyperbolicVolume :=
  (hf.continuousOn.integrableOn_compact (cuspHeightCompact_isCompact a b ha)).mono_set
    (cuspPeriodStrip_subset_heightCompact a b ha)

def sourceArbitraryHeightFamily (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) :ℂ :=
  (24:ℂ)⁻¹*∑i:RationalBruhatIndex,arbitraryCuspHeightFamily
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq s

def sourceArbitraryHeightFourier (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (24:ℂ)⁻¹ • ∑i:RationalBruhatIndex,arbitraryCuspHeightFourier
    (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq

lemma sourceArbitraryHeightFamily_analyticAt (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:1<s.re) (hi:0<s.im) :
    AnalyticAt ℂ (sourceArbitraryHeightFamily M a b ha ρ freq) s := by
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro i hi'
  exact arbitraryCuspHeightFamily_analyticAt _ a b ha ρ freq s hs.ne' hi.ne'

lemma sourceArbitraryHeightFamily_residue_limit (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    Tendsto (fun s:ℂ=>(s-4/3)*sourceArbitraryHeightFamily M a b ha ρ freq s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (sourceArbitraryHeightFourier M a b ha ρ freq cubicEisensteinResidue)) := by
  have he:=(tendsto_finsetSum Finset.univ (fun i hi=>
    arbitraryCuspHeightFamily_residue_limit (rationalComplex (rationalBruhatRep i)*M) a b ha ρ freq)).const_mul ((24:ℂ)⁻¹)
  convert (preTransparency := .instances) he using 1
  · funext s
    rw [sourceArbitraryHeightFamily,←Finset.mul_sum]
    ring
  · simp only [sourceArbitraryHeightFourier,_root_.smul_apply,
      _root_.sum_apply,smul_eq_mul]

lemma sourceProjection_integral (f:HyperbolicSpace→ℂ) (hf:Continuous f)
    (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a) (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    (∫w in cuspPeriodStrip a b,sourceProjection f (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume)=
      (24:ℂ)⁻¹*∑i:RationalBruhatIndex,∫w in cuspPeriodStrip a b,
        f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  have hi (i:RationalBruhatIndex) : IntegrableOn
      (fun w=>f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w)
      (cuspPeriodStrip a b) hyperbolicVolume :=
    cuspStrip_integrable_continuous a b ha _ ((hf.comp (continuous_hyperbolic_action _)).mul
      (arbitraryCuspWeightedPhase_continuous ρ freq))
  calc
    _ = ∫w in cuspPeriodStrip a b,(24:ℂ)⁻¹*∑i:RationalBruhatIndex,
        f ((rationalComplex (rationalBruhatRep i)*M)•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun w=>by
        dsimp only
        rw [sourceProjection_eq_twentyFour]
        simp only [rationalComplex,MonoidHom.comp_apply,mul_smul]
        rw [←Finset.sum_mul]
        ring)
    _ = _ := by rw [integral_const_mul,integral_finsetSum _ (fun i hi'=>hi i)]

lemma sourceArbitraryHeightFamily_initial (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq s:ℂ) (hs:4<s.re) (hi:0<s.im) :
    sourceArbitraryHeightFamily M a b ha ρ freq s=
      ∫w in cuspPeriodStrip a b,sourceEisenstein s (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [sourceEisenstein,sourceProjection_integral _ (hyperbolicEisenstein_continuous s (by linarith)) M a b ha ρ freq]
  unfold sourceArbitraryHeightFamily
  congr 1
  apply Finset.sum_congr rfl
  intro i hi'
  exact arbitraryCuspHeightFamily_initial _ a b ha ρ freq s hs hi

lemma arbitraryCuspHeightFourier_residue_integral (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    arbitraryCuspHeightFourier M a b ha ρ freq cubicEisensteinResidue=
      ∫w in cuspPeriodStrip a b,cubicResidualFunction (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFourier_integral]
  have he:=(measurePreserving_smul M hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp
    cubicEisensteinResidue_continuous_representative
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae he] with w hw
  exact congrArg (fun c:ℂ=>c*arbitraryCuspWeightedPhase ρ freq w) hw

lemma sourceArbitraryHeightFourier_residue_integral (M:SL(2,ℂ)) (a b:ℝ) (ha:0<a)
    (ρ:BoundedContinuousFunction ℝ ℂ) (freq:ℂ) :
    sourceArbitraryHeightFourier M a b ha ρ freq cubicEisensteinResidue=
      ∫w in cuspPeriodStrip a b,cubicSourceResidualFunction (M•w)*arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [cubicSourceResidualFunction,sourceProjection_integral _ cubicResidualFunction_continuous M a b ha ρ freq]
  simp only [sourceArbitraryHeightFourier,_root_.smul_apply,
    _root_.sum_apply,smul_eq_mul,arbitraryCuspHeightFourier_residue_integral]

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedClosed (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  1+(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j -
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)*ramifiedClosed p hp hg eta a rho x w z j

end SevenEighths.ProbeEuler
end

end OAI
end


