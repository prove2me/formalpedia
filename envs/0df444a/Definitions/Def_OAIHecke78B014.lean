-- Prove2me | Definitions.Def_OAIHecke78B014
-- name    : OAIHecke78B014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T00:36:33.924561+00:00
-- url     : https://prove2.me/theorems/32b44de5-8768-4693-9b78-482692861a52
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 15 of 29
-- statement:
--   Definitions bundle 15 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B013` of this split, and through them their definitions.
--
--   Modules: `Eisenstein.OppositeCusp`, `Eisenstein.ResidualFourierExpansion`, `Eisenstein.ArbitraryCuspPullback`, `Eisenstein.RationalTranslations`, `Eisenstein.CuspAverage`, `Eisenstein.BesselMellinTransform`, `Eisenstein.ResidualCuspDecay`, `Eisenstein.ConjugateCuspProfiles`, `Eisenstein.CuspDilation`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_OAIHecke78B013

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B014

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.OppositeCusp
  Eisenstein.ResidualFourierExpansion
  Eisenstein.ArbitraryCuspPullback
  Eisenstein.RationalTranslations
  Eisenstein.CuspAverage
  Eisenstein.BesselMellinTransform
  Eisenstein.ResidualCuspDecay
  Eisenstein.ConjugateCuspProfiles
  Eisenstein.CuspDilation
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

open scoped BigOperators Classical MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev PrimaryLower:={c:Eis//(3:Eis)∣c-1}
abbrev OppositeData:=Σc:PrimaryLower,{x:Eis//IsCoprime c.val x}

lemma primaryLower_primary (c:PrimaryLower):lambda^2∣c.val-1:=lambda_sq_dvd_three.trans c.2
lemma primaryLower_ne_zero (c:PrimaryLower):c.val≠0:=primary_ne_zero c.val (primaryLower_primary c)

def oppositeDataToPrimitive (p:OppositeData):PrimitiveRow:=
  ⟨![-3*p.2.val,p.1.val],by
    change IsCoprime (-3*p.2.val) p.1.val ∧ (3:Eis)∣-3*p.2.val ∧ (3:Eis)∣p.1.val-1
    refine ⟨?_,⟨-p.2.val,by ring⟩,p.1.2⟩
    simpa only [neg_mul] using
      ((primary_coprime_three p.1.val (primaryLower_primary p.1)).mul_right p.2.2).symm.neg_left⟩

lemma oppositeDataToPrimitive_bijective:Function.Bijective oppositeDataToPrimitive:=by
  constructor
  · rintro ⟨c,x,hx⟩ ⟨d,y,hy⟩ h
    have hrow:=congrArg Subtype.val h
    have hcd:c=d:=by
      apply Subtype.ext
      exact congrFun hrow 1
    subst d
    have hxy:x=y:=by
      have he:-(3:Eis)*x=-(3:Eis)*y:=congrFun hrow 0
      exact mul_left_cancel₀ (by norm_num : -(3:Eis)≠0) he
    subst y
    rfl
  · intro r
    obtain ⟨t,ht⟩:=r.2.2.1
    let c:PrimaryLower:=⟨r.1 1,r.2.2.2⟩
    have hx:IsCoprime c.val (-t):=by
      have hh:IsCoprime c.val (3*t):=by simpa only [c,ht] using r.2.1.symm
      exact (hh.of_isCoprime_of_dvd_right (dvd_mul_left t 3)).neg_right
    refine ⟨⟨c,-t,hx⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change -3*(-t)=r.1 0
      rw [ht]
      ring
    · rfl

def oppositeDataEquiv:OppositeData≃PrimitiveRow:=
  Equiv.ofBijective oppositeDataToPrimitive oppositeDataToPrimitive_bijective

def oppositeMatrix:SL(2,ℂ):=⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma rowOperator_opposite (v:Fin 2→ℂ):rowOperator oppositeMatrix v=![v 1,-v 0]:=by
  rw [rowOperator_apply]
  funext i
  fin_cases i <;> simp [oppositeMatrix,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

def oppositeEisenstein (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ):ℂ:=
  eisenstein (oppositeMatrix*upperSection z v hv) s

lemma rowHeight_eq_shiftedHeightKernel (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c d:Eis) (hc:c≠0):
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s=
      ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        shiftedHeightKernel v s (eisEmbedding d/eisEmbedding c) z:=by
  have hc':=eisEmbedding_ne_zero hc
  have hnorm:0<‖eisEmbedding c‖^2:=sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac:eisEmbedding c*z+eisEmbedding d=eisEmbedding c*(z+eisEmbedding d/eisEmbedding c):=by field_simp
  have heq:v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2)=
      ((‖eisEmbedding c‖^2*v)*(1+‖(z+eisEmbedding d/eisEmbedding c)/(v:ℂ)‖^2))⁻¹:=by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ;ring
  unfold shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity),←Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring

def oppositeTerm (z:ℂ) (v:ℝ) (s:ℂ) (c x:Eis):ℂ:=
  eisEmbedding (symbol (3*x) c)*
    ((v/(‖eisEmbedding c*z+eisEmbedding (3*x)‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s

lemma oppositeTerm_eq_shifted (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ)
    (c x:Eis) (hc:c≠0):
    oppositeTerm z v s c x=
      (eisEmbedding (symbol (3*x) c)*((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s))*
        shiftedHeightKernel v s (eisEmbedding (3*x)/eisEmbedding c) z:=by
  rw [oppositeTerm,rowHeight_eq_shiftedHeightKernel z v hv s c (3*x) hc]
  ring

lemma opposite_summand (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OppositeData):
    summand (oppositeMatrix*upperSection z v hv) s
      (primitiveRowEquiv.symm (oppositeDataEquiv p))=
      oppositeTerm z v s p.1.val p.2.val:=by
  let r:Fin 2→ℂ:=![eisEmbedding p.1.val,eisEmbedding (3*p.2.val)]
  have hr:rowOperator oppositeMatrix
      (embeddedRow (primitiveRowEquiv.symm (oppositeDataEquiv p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_opposite]
    funext i
    fin_cases i <;>
      simp [oppositeDataEquiv, Equiv.ofBijective_apply, oppositeDataToPrimitive, r, map_mul]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 0
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.1) he
  have hp:0<heightDenominator z v r:=heightDenominator_pos z v hv r hr0
  have hphase:(cosetCharacter (primitiveRowEquiv.symm (oppositeDataEquiv p)))⁻¹=
      eisEmbedding (symbol (3*p.2.val) p.1.val):=by
    rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (-3*p.2.val) p.1.val)=_
    rw [neg_mul,symbol_neg_numerator _ _ (primaryLower_primary p.1)]
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,hphase]
  change _=eisEmbedding (symbol (3*p.2.val) p.1.val)*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

def primaryLowerIdealEquiv:PrimaryLower≃GoodIdeal where
  toFun c:=⟨Ideal.span {c.val},by rw [primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c)];exact primaryLower_ne_zero c⟩
  invFun I:=⟨primaryGenerator I.val,three_dvd_primary_sub_one _ (primaryGenerator_spec I.val I.2).2⟩
  left_inv c:=Subtype.ext (primaryGenerator_span c.val (primaryLower_ne_zero c) (primaryLower_primary c))
  right_inv I:=Subtype.ext (primaryGenerator_spec I.val I.2).1

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

abbrev CoprimeElement (c:Eis):={x:Eis//IsCoprime c x}

def cubicResidueElementMap (c:Eis) (p:CubicUnitResidue c×Eis):CoprimeElement c:=
  ⟨GaussianShiftedPartition.representative c p.1.val+c*p.2,by
    apply (isUnit_quotient_span_iff c _).mp
    have hc:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [map_add,map_mul,hc,zero_mul,add_zero,
      GaussianShiftedPartition.representative_spec] using p.1.2⟩

lemma cubicResidueElementMap_bijective (c:Eis) (hc:c≠0):
    Function.Bijective (cubicResidueElementMap c):=by
  have hmod (r:CubicUnitResidue c) (n:Eis):
      Ideal.Quotient.mk (Ideal.span {c})
        (GaussianShiftedPartition.representative c r.val+c*n)=r.val:=by
    have hzero:Ideal.Quotient.mk (Ideal.span {c}) c=0:=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add,map_mul,hzero,zero_mul,add_zero,GaussianShiftedPartition.representative_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ h
    have he:=congrArg Subtype.val h
    change GaussianShiftedPartition.representative c r.val+c*n=
      GaussianShiftedPartition.representative c t.val+c*m at he
    have hrt:r=t:=Subtype.ext (by
      simpa only [hmod] using congrArg (Ideal.Quotient.mk (Ideal.span {c})) he)
    subst t
    have hnm:n=m:=mul_left_cancel₀ hc (add_left_cancel he)
    subst m
    rfl
  · intro x
    let r:CubicUnitResidue c:=⟨Ideal.Quotient.mk (Ideal.span {c}) x.val,
      (isUnit_quotient_span_iff c x.val).mpr x.2⟩
    have hdiv:c∣x.val-GaussianShiftedPartition.representative c r.val:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact (GaussianShiftedPartition.representative_spec c r.val).symm
    obtain ⟨n,hn⟩:=hdiv
    refine ⟨(r,n),Subtype.ext ?_⟩
    change GaussianShiftedPartition.representative c r.val+c*n=x.val
    linear_combination -hn

def cubicResidueElementEquiv (c:Eis) (hc:c≠0):
    CubicUnitResidue c×Eis≃CoprimeElement c:=
  Equiv.ofBijective (cubicResidueElementMap c) (cubicResidueElementMap_bijective c hc)

lemma oppositeTerm_shift (z:ℂ) (v:ℝ) (s:ℂ) (c x n:Eis):
    oppositeTerm z v s c (x+c*n)=oppositeTerm (z+3*eisEmbedding n) v s c x:=by
  have hsym:symbol (3*(x+c*n)) c=symbol (3*x) c:=symbol_congr ⟨3*n,by ring⟩
  have harg:eisEmbedding c*z+eisEmbedding (3*(x+c*n))=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding (3*x):=by
    simp only [map_mul,map_add,map_ofNat]
    ring
  rw [oppositeTerm,oppositeTerm,hsym,harg]

def oppositeGaussSum (h c:Eis):ℂ:=
  ∑'r:CubicUnitResidue c,
    eisEmbedding (symbol (3*GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive h c (3*GaussianShiftedPartition.representative c r.val)

theorem oppositeGaussSum_eq (h:Eis) (c:PrimaryLower):
    oppositeGaussSum h c.val=cubicUnitGaussSum (9*h) c.val:=by
  have hp:=primaryLower_primary c
  have hc:=primaryLower_ne_zero c
  have he:oppositeGaussSum h c.val=
      eisEmbedding (symbol 3 c.val)*cubicUnitGaussSum h c.val:=by
    rw [oppositeGaussSum,cubicUnitGaussSum,←tsum_mul_left]
    apply tsum_congr
    intro r
    rw [symbol_mul_numerator _ _ _ hp,map_mul]
    have hadd:residueAdditive h c.val (3*GaussianShiftedPartition.representative c.val r.val)=
        residueAdditive (3*h) c.val (GaussianShiftedPartition.representative c.val r.val):=by
      unfold residueAdditive cuspFrequency
      simp only [map_mul,map_ofNat]
      congr 1
      ring
    rw [hadd]
    ring
  rw [he]
  have hs:=cubicUnitGaussSum_phase_shift h 1 c.val hc hp (by
    simpa only [mul_one] using (primary_coprime_three c.val hp).symm)
  simpa only [symbol_one_numerator c.val hp,map_one,one_mul,mul_one,mul_comm h 9] using hs

def oppositeArithmeticSeries (s:ℂ) (h:Eis):ℂ:=
  ∑'c:PrimaryLower,((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val

theorem oppositeArithmeticSeries_eq (s:ℂ) (h:Eis):
    oppositeArithmeticSeries s h=unramifiedCubicGaussSeries s (9*h):=by
  rw [oppositeArithmeticSeries,←primaryLowerIdealEquiv.symm.tsum_eq,unramifiedCubicGaussSeries]
  apply tsum_congr
  intro I
  rw [oppositeGaussSum_eq]
  change ((‖eisEmbedding (primaryGenerator I.val)‖^2:ℝ):ℂ)^(-s)*
    cubicUnitGaussSum (9*h) (primaryGenerator I.val)=_
  rw [eisEmbedding_norm_sq_eq_absNorm_span,(primaryGenerator_spec I.val I.2).1,
    Complex.ofReal_natCast]

end

section

open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix
open ActualEisensteinCubic ConcreteTraceCRT

lemma continuous_inverse_fixed_left_operator (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    Continuous (fun z:ℂ=>rowOperator (a*upperSection z v hv)⁻¹):=by
  have he (z:ℂ):rowOperator (a*upperSection z v hv)⁻¹=
      (rowOperator a⁻¹).comp (rowOperator (upperSection z v hv)⁻¹):=by
    ext u
    simp only [mul_inv_rev,ContinuousLinearMap.comp_apply,rowOperator_mul]
  simp_rw [he]
  exact continuous_const.clm_comp (continuous_inverse_upper_operator v hv)

lemma exists_fixed_left_rowBound (a:SL(2,ℂ)) (v:ℝ) (hv:0<v):
    ∃C:ℝ,0<C ∧ ∀z∈periodDomain,rowBound (a*upperSection z v hv)≤C:=by
  have hc:Continuous (fun z:ℂ=>rowBound (a*upperSection z v hv)):=
    continuous_const.mul (continuous_const.add (continuous_inverse_fixed_left_operator a v hv).norm)
  let R:ℝ:=∑i:Fin 2,‖periodBasis i‖
  obtain ⟨C,hC⟩:=(isCompact_closedBall (0:ℂ) R).bddAbove_image hc.continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩

lemma continuous_fixed_left_summand (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (x:CuspCosets):
    Continuous (fun z:ℂ=>summand (a*upperSection z v hv) s x):=by
  simp_rw [summand,←rowOperator_mul,rowEnergy_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    unfold heightDenominator
    fun_prop
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos (heightDenominator_pos z v hv _
      (rowOperator_ne_zero a _ (embeddedRow_ne_zero x))) hv

lemma fixed_left_summable_majorant (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s:ℂ) (hs:2<s.re):
    ∃M:CuspCosets→ℝ,Summable M ∧ (∀x,0≤M x) ∧
      ∀z∈periodDomain,∀x,‖summand (a*upperSection z v hv) s x‖≤M x:=by
  obtain ⟨C,hC,hbound⟩:=exists_fixed_left_rowBound a v hv
  refine ⟨fun x=>C ^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm:=summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj:Function.Injective (fun x:CuspCosets=>rowCoordinates (cosetRow x)):=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (a*upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

theorem hasSum_integral_fixed_left_Eisenstein (a:SL(2,ℂ)) (v:ℝ) (hv:0<v)
    (s freq:ℂ) (hs:2<s.re):
    HasSum (fun x:CuspCosets=>∫z in periodDomain,
      summand (a*upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (a*upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)):=by
  let:Countable CuspCosets:=(rowCoordinates_injective.comp cosetRow_injective).countable
  let:=periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩:=fixed_left_summable_majorant a v hv s hs
  have hchar:Continuous (fun z:ℂ=>ShortDraftTrace.breveE (-freq*z)):=by
    change Continuous (fun z:ℂ=>Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  exact hasSum_integral_of_dominated_convergence
    («μ»:=volume.restrict periodDomain)
    (fun (x:CuspCosets) (_:ℂ)=>M x)
    (fun x=>((continuous_fixed_left_summand a v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x=>(ae_restrict_mem periodDomain_measurable).mono fun z hz=>by
      simpa only [Pi.mul_apply,norm_mul,breveE_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _=>hM)
    (integrable_const (∑'x,M x))
    (Eventually.of_forall fun z=>(summable_summand (a*upperSection z v hv) s hs).hasSum.mul_right
      (ShortDraftTrace.breveE (-freq*z)))

end

section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def oppositeIntegral (v:ℝ) (s freq:ℂ) (c x:Eis):ℂ:=
  ∫z in periodDomain,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z)

theorem hasSum_oppositeIntegrals (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re):
    HasSum (fun p:OppositeData=>oppositeIntegral v s freq p.1.val p.2.val)
      (∫z in periodDomain,oppositeEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)):=by
  have hh:=(oppositeDataEquiv.trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein oppositeMatrix v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [Equiv.trans_apply]
    rw [opposite_summand]

lemma oppositeTerm_integrable (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (c x:Eis) (hc:c≠0):Integrable (fun z=>oppositeTerm z v s c x):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma oppositeIntegral_sum_translate (v:ℝ) (hv:0<v) (s:ℂ) (hs:1<s.re)
    (h c x:Eis) (hc:c≠0):
    (∑'n:Eis,oppositeIntegral v s (cuspFrequency h) c (x+c*n))=
      ∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-cuspFrequency h*z):=by
  have hint:=trace_mul_integrable (fun z=>oppositeTerm z v s c x)
    (oppositeTerm_integrable v hv s hs c x hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z=>by
    dsimp only [oppositeIntegral]
    rw [oppositeTerm_shift,cuspFrequency_negative_period]

lemma oppositeTerm_fourier_integral (v:ℝ) (hv:0<v) (s freq:ℂ)
    (c x:Eis) (hc:c≠0):
    (∫z:ℂ,oppositeTerm z v s c x*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        (eisEmbedding (symbol (3*x) c)*
          ShortDraftTrace.breveE (freq*eisEmbedding (3*x)/eisEmbedding c)):=by
  simp_rw [oppositeTerm_eq_shifted _ v hv s c x hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding (3*x)/eisEmbedding c) freq]
  ring_nf

lemma oppositeDenominator_integral_formula (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re)
    (h:Eis) (c:PrimaryLower):
    (∑'x:CoprimeElement c.val,oppositeIntegral v s (cuspFrequency h) c.val x.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val:=by
  have hf:Summable (fun x:CoprimeElement c.val=>oppositeIntegral v s (cuspFrequency h) c.val x.val):=
    (hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  have hsum:=(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue c.val×Eis=>
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2)) at hsum
  rw [←(cubicResidueElementEquiv c.val (primaryLower_ne_zero c)).tsum_eq]
  change (∑'q:CubicUnitResidue c.val×Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val q.1.val+c.val*q.2))=_
  rw [hsum.tsum_prod]
  change (∑'r:CubicUnitResidue c.val,∑'n:Eis,
    oppositeIntegral v s (cuspFrequency h) c.val
      (GaussianShiftedPartition.representative c.val r.val+c.val*n))=_
  simp_rw [oppositeIntegral_sum_translate v hv s (by linarith) h c.val _ (primaryLower_ne_zero c),
    oppositeTerm_fourier_integral v hv s (cuspFrequency h) c.val _ (primaryLower_ne_zero c)]
  exact tsum_mul_left

lemma unramifiedCubicGaussSeries_twentySeven (s:ℂ) (h:Eis):
    unramifiedCubicGaussSeries s (27*h)=unramifiedCubicGaussSeries s h:=by
  apply tsum_congr
  intro I
  congr 1
  have hp:lambda^2∣primaryGenerator I.val-1:=(primaryGenerator_spec I.val I.2).2
  simpa only [show (3:Eis)^3=27 by norm_num,mul_comm h 27] using
    cubicUnitGaussSum_cube_shift h (primaryGenerator I.val) 3 I.2 hp
      (primary_coprime_three _ hp)

theorem oppositeEisenstein_fourier (v:ℝ) (hv:0<v) (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫z in periodDomain,oppositeEisenstein z v hv s*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        unramifiedCubicGaussSeries s (9*h):=by
  have hh:=hasSum_oppositeIntegrals v hv s (cuspFrequency h) hs
  rw [←hh.tsum_eq,hh.summable.tsum_sigma]
  simp_rw [oppositeDenominator_integral_formula v hv s hs h]
  rw [←oppositeArithmeticSeries_eq s h,oppositeArithmeticSeries]
  have he (c:PrimaryLower):
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*
        ((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        (((‖eisEmbedding c.val‖^2:ℝ):ℂ)^(-s)*oppositeGaussSum h c.val):=by ring
  simp_rw [he]
  exact tsum_mul_left

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local instance instMeasureSpaceUnitAddCircle_solutions_1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureUnitAddCircleVolume_solutions_1_rc877c1_1 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_1_rc877c1_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
abbrev PeriodTorusL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

def periodIocCube : Set (Fin 2→ℝ) := {x | ∀i,x i∈Set.Ioc 0 (0+1)}

def periodCovolumeDensity : ℝ≥0∞ := ENNReal.ofReal (2/(9*Real.sqrt 3))

lemma periodCovolumeDensity_ne_zero : periodCovolumeDensity≠0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))

lemma periodIocCube_measurable : MeasurableSet periodIocCube :=
  MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)

lemma periodIocCube_ae : periodCube=ᵐ[volume]periodIocCube := by
  simpa only [periodIocCube,zero_add] using periodCube_ae_Ioc

def periodSection (t : UnitAddTorus (Fin 2)) : ℂ :=
  periodVector ((UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ)) t).val)

lemma periodSection_measurableEmbedding : MeasurableEmbedding periodSection :=
  periodVector.toHomeomorph.toMeasurableEquiv.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).measurableEmbedding)

lemma periodTorus_measurable : Measurable periodTorus := by
  apply measurable_pi_iff.mpr
  intro i
  exact AddCircle.measurable_mk'.comp
    ((measurable_pi_apply i).comp periodBasis.equivFunL.continuous.measurable)

lemma periodTorus_section (t : UnitAddTorus (Fin 2)) : periodTorus (periodSection t)=t := by
  rw [periodSection,periodTorus_periodVector]
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0:ℝ))).symm_apply_apply t

lemma periodVector_Ioc_measurePreserving :
    MeasurePreserving periodVector (volume.restrict periodIocCube)
      (periodCovolumeDensity • volume.restrict periodDomain) := by
  refine ⟨periodVector.continuous.measurable,?_⟩
  rw [←Measure.restrict_congr_set periodIocCube_ae,←periodVector_preimage_domain,
    ←Measure.restrict_map periodVector.continuous.measurable periodDomain_measurable,
    periodVector_map_volume,Measure.restrict_smul]
  rfl

lemma periodSection_measurePreserving :
    MeasurePreserving periodSection volume
      (periodCovolumeDensity • volume.restrict periodDomain) :=
  periodVector_Ioc_measurePreserving.comp
    ((measurePreserving_subtype_coe periodIocCube_measurable).comp
      (UnitAddTorus.measurePreserving_equivPiIoc (fun _ : Fin 2 => (0:ℝ))))

lemma periodTorus_measurePreserving :
    MeasurePreserving periodTorus (periodCovolumeDensity • volume.restrict periodDomain) volume := by
  refine ⟨periodTorus_measurable,?_⟩
  rw [←periodSection_measurePreserving.map_eq,
    Measure.map_map periodTorus_measurable periodSection_measurableEmbedding.measurable]
  have he : periodTorus ∘ periodSection=id := funext periodTorus_section
  rw [he,Measure.map_id]

lemma periodSection_torus_ae :
    (fun z => periodSection (periodTorus z))=ᵐ[volume.restrict periodDomain] (fun z : ℂ => z) := by
  apply (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp
  rw [←periodSection_measurePreserving.map_eq]
  apply periodSection_measurableEmbedding.ae_map_iff.mpr
  exact Eventually.of_forall (fun t => by dsimp only; rw [periodTorus_section])

lemma periodSection_memLp (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    MemLp (f ∘ periodSection) 2 volume :=
  (hf.smul_measure (by simp [periodCovolumeDensity])).comp_measurePreserving
    periodSection_measurePreserving

def periodTorusL2Lift (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) : PeriodTorusL2 :=
  (periodSection_memLp f hf).toLp (f ∘ periodSection)

lemma periodTorusL2Lift_ae (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    periodTorusL2Lift f hf=ᵐ[volume]f ∘ periodSection :=
  MemLp.coeFn_toLp (periodSection_memLp f hf)

lemma periodTorusL2Lift_pullback (f : ℂ→ℂ) (hf : MemLp f 2 (volume.restrict periodDomain)) :
    (fun z => periodTorusL2Lift f hf (periodTorus z))=ᵐ[volume.restrict periodDomain]f := by
  have he := periodTorus_measurePreserving.quasiMeasurePreserving.ae_eq_comp (periodTorusL2Lift_ae f hf)
  have he' := (Measure.ae_ennreal_smul_measure_iff periodCovolumeDensity_ne_zero).mp he
  filter_upwards [he',periodSection_torus_ae] with z hz hsec
  change periodTorusL2Lift f hf (periodTorus z)=f (periodSection (periodTorus z)) at hz
  rw [hsec] at hz
  exact hz

lemma periodTorusL2Lift_frequency_integral (f : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain)) (h : ActualEisensteinCubic.O) :
    (∫z in periodDomain,periodTorusL2Lift f hf (periodTorus z)*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
    ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  apply integral_congr_ae
  filter_upwards [periodTorusL2Lift_pullback f hf] with z hz
  rw [hz]

theorem periodDomain_L2_ext (f g : ℂ→ℂ)
    (hf : MemLp f 2 (volume.restrict periodDomain))
    (hg : MemLp g 2 (volume.restrict periodDomain))
    (h : ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ∫z in periodDomain,g z*ShortDraftTrace.breveE (-cuspFrequency h*z)) :
    f=ᵐ[volume.restrict periodDomain]g := by
  have he : periodTorusL2Lift f hf=periodTorusL2Lift g hg := by
    apply periodTorus_L2_ext
    intro hfreq
    rw [periodTorusL2Lift_frequency_integral,periodTorusL2Lift_frequency_integral,h]
  filter_upwards [periodTorusL2Lift_pullback f hf,periodTorusL2Lift_pullback g hg] with z hz hz'
  rw [←hz,←hz',he]

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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma cubicResidualFullMode_density_integrable (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    IntegrableOn (fun v : ℝ => cubicResidualFullModeAmplitude v h/(v:ℂ)^3)
      (Set.Icc a b) volume := by
  by_cases hh : h=0
  · subst h
    have hi : IntegrableOn (fun v : ℝ =>
        (3*(Real.pi:ℂ))*constantArithmeticResidue*(v:ℂ)^(-(7/3:ℂ)))
        (Set.Icc a b) volume := by
      apply ContinuousOn.integrableOn_Icc
      intro v hv
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const v
        (-(7/3:ℂ)) (Or.inr (ha.trans_le hv.1).ne'))).continuousWithinAt
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_zero_density v (ha.trans_le hv.1)).symm
  · apply ((cubicBesselHeight_integrable a b ha h hh).const_mul
      (cubicResidualFourierCoefficient h)).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (cubicResidualFullModeAmplitude_nonzero_density v (ha.trans_le hv.1) h hh).symm

lemma cubicEisensteinResidue_slice_coefficient_ae (a b : ℝ) (ha : 0<a) (h : ActualEisensteinCubic.O) :
    kernelCuspSliceCoefficient cubicEisensteinResidue h =ᵐ[volume.restrict (Set.Icc a b)]
      (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3)) := by
  apply interval_ae_eq_of_boundedContinuous_height_tests a b _ _
    (kernelCuspSliceCoefficient_integrable a b ha h cubicEisensteinResidue)
    ((cubicResidualFullMode_density_integrable a b ha h).const_mul _)
  intro ρ
  rw [←kernelCuspHeightFourier_eq_slice_integral a b ha ρ h cubicEisensteinResidue,
    kernelCuspHeightFourier_residue_full a b ha ρ h,←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by ring)

lemma cubicEisensteinResidue_all_slice_coefficients_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      kernelCuspSliceCoefficient cubicEisensteinResidue h v =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicResidualFullModeAmplitude v h/(v:ℂ)^3) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  exact ae_all_iff.mpr (fun h => cubicEisensteinResidue_slice_coefficient_ae a b ha h)

lemma cubicEisensteinResidue_all_fourier_integrals_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b), ∀h : ActualEisensteinCubic.O,
      (∫z in periodDomain,
        cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z)))*
          ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFullModeAmplitude v h := by
  filter_upwards [cubicEisensteinResidue_all_slice_coefficients_ae a b ha,
    ae_restrict_mem measurableSet_Icc] with v hv hvmem
  intro h
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ha.trans_le hvmem.1).ne'
  have he := hv h
  unfold kernelCuspSliceCoefficient at he
  rw [←mul_div_assoc] at he
  exact (div_left_inj' (pow_ne_zero 3 hv0)).mp he

end

local notation "O" => ActualEisensteinCubic.O

lemma cubicResidualFunction_fourier_full (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualFunction (upperPoint z v hv)*
      ShortDraftTrace.breveE (-cuspFrequency h*z)) =
        ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualFullModeAmplitude v h := by
  rw [cubicResidualFunction_fourier v hv h]
  congr 1
  by_cases hh : h=0
  · simp only [hh,cubicResidualFullModeAmplitude,ite_true]
  · simp only [hh,cubicResidualFullModeAmplitude,cubicResidualModeAmplitude,ite_false]

lemma cubicResidualFunction_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => cubicResidualFunction (upperPoint z v hv)) := by
  have hc := cubicResidualNonzeroSeries_height_continuous v hv
  simp only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  fun_prop

lemma cubicResidualFunction_height_memLp (v : ℝ) (hv : 0<v) :
    MemLp (fun z : ℂ => cubicResidualFunction (cuspCoordinateLift (v,z))) 2
      (volume.restrict periodDomain) := by
  simp_rw [cuspCoordinateLift_positive v _ hv]
  have hc := cubicResidualFunction_height_continuous v hv
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  have hn : Continuous (fun z : ℂ => ‖cubicResidualFunction (upperPoint z v hv)‖^2) := by
    fun_prop
  apply (hn.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

theorem cubicEisensteinResidue_cell_slices_ae (a b : ℝ) (ha : 0<a) :
    ∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z : ℂ => cubicEisensteinResidue
        (integralOrbitProjection globalKubotaKernel (cuspCoordinateLift (v,z))))
      =ᵐ[volume.restrict periodDomain]
        (fun z => cubicResidualFunction (cuspCoordinateLift (v,z))) := by
  filter_upwards [cubicEisensteinResidue_all_fourier_integrals_ae a b ha,
    kernelCuspSections_memLp a b ha cubicEisensteinResidue,
    ae_restrict_mem measurableSet_Icc] with v hfour hL hv
  have hpos : 0<v := ha.trans_le hv.1
  apply periodDomain_L2_ext _ _ hL (cubicResidualFunction_height_memLp v hpos)
  intro h
  rw [hfour h]
  symm
  simpa only [cuspCoordinateLift_positive v _ hpos] using
    cubicResidualFunction_fourier_full v hpos h

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal Pointwise MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

open ActualEisensteinCubic ConcreteTraceCRT CubicKubota

lemma periodDomain_memLp_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict periodDomain) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
  apply (((hf.norm.pow 2).continuousOn).integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz

lemma upperTranslation_mem_kernel (n : ActualEisensteinCubic.O) :
    (upperTranslation n : SL(2,ActualEisensteinCubic.O))∈globalKubotaKernel := by
  exact (globalKubotaKernel_mem _).mpr
    ⟨(upperTranslation n).property,complexCharacter_upperTranslation n⟩

lemma kernelProjection_upper_period (v : ℝ) (hv : 0<v) (z : ℂ) (n : ActualEisensteinCubic.O) :
    integralOrbitProjection globalKubotaKernel (upperPoint (z+3*eisEmbedding n) v hv)=
      integralOrbitProjection globalKubotaKernel (upperPoint z v hv) := by
  let M : globalKubotaKernel := ⟨upperTranslation n,upperTranslation_mem_kernel n⟩
  have ha : integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • upperPoint z v hv=
      upperPoint (z+3*eisEmbedding n) v hv := by
    change (QuotientGroup.mk (complexMatrix (upperTranslation n)*upperSection z v hv) : HyperbolicSpace)=_
    rw [upperTranslation_section]
    rfl
  rw [←ha,integralOrbitProjection_eq]

lemma ae_eq_of_periodDomain_eq (f g : ℂ→ℂ)
    (hf : ∀(n : ActualEisensteinCubic.O)(z : ℂ),f (z+3*eisEmbedding n)=f z)
    (hg : ∀(n : ActualEisensteinCubic.O)(z : ℂ),g (z+3*eisEmbedding n)=g z)
    (he : f=ᵐ[volume.restrict periodDomain]g) : f=ᵐ[volume]g := by
  have hp (p : periodLattice) (z : ℂ) : f (p+ᵥz)=f z ∧ g (p+ᵥz)=g z := by
    obtain ⟨n,rfl⟩ := periodEquiv.surjective p
    change f (3*eisEmbedding n+z)=f z ∧ g (3*eisEmbedding n+z)=g z
    rw [add_comm]
    exact ⟨hf n z,hg n z⟩
  have hi : ∀p : periodLattice,p+ᵥ{z : ℂ | f z≠g z}={z : ℂ | f z≠g z} := by
    intro p
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change (f ((-p)+ᵥz)≠g ((-p)+ᵥz)) ↔ f z≠g z
    rw [(hp (-p) z).1,(hp (-p) z).2]
  have hz : volume ({z : ℂ | f z≠g z}∩periodDomain)=0 := by
    change ∀ᵐz ∂volume.restrict periodDomain,f z=g z at he
    rw [ae_restrict_iff' periodDomain_measurable] at he
    rw [ae_iff] at he
    have hs : {z : ℂ | f z≠g z}∩periodDomain =
        {z : ℂ | ¬(z∈periodDomain → f z=g z)} := by
      ext z
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff]
      tauto
    rw [hs]
    exact he
  change ∀ᵐz ∂volume,f z=g z
  rw [ae_iff]
  exact periodDomain_fundamental.measure_zero_of_invariant _ hi hz

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

lemma positive_height_interval_cover :
    Set.Ioi (0:ℝ) = ⋃n : ℕ,Set.Icc (1/((n:ℝ)+1)) ((n:ℝ)+1) := by
  ext v
  constructor
  · intro hv
    obtain ⟨n,hn⟩ := exists_nat_gt (max v (1/v))
    have hN : 0<(n:ℝ)+1 := by positivity
    have hvp : 0<v := hv
    have hvN : v≤(n:ℝ)+1 := by linarith [le_max_left v (1/v)]
    have hinv : 1/v≤(n:ℝ)+1 := by linarith [le_max_right v (1/v)]
    have hlow : 1/((n:ℝ)+1)≤v := by
      apply (div_le_iff₀ hN).mpr
      have hh := (div_le_iff₀ hvp).mp hinv
      nlinarith
    exact Set.mem_iUnion.mpr ⟨n,hlow,hvN⟩
  · intro hv
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
    exact lt_of_lt_of_le (by positivity : 0<(1:ℝ)/((n:ℝ)+1)) hn.1

lemma hyperbolic_ae_of_coordinate_ae (f g : HyperbolicSpace→ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (he : ∀ᵐq ∂(volume.restrict (Set.Ioi (0:ℝ))).prod (volume : Measure ℂ),
      f (cuspCoordinateLift q)=g (cuspCoordinateLift q)) : f=ᵐ[hyperbolicVolume]g := by
  have hm := spatialComplexSplit_preserves_volume.restrict_preimage
    (s := Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℂ)) (measurableSet_Ioi.prod MeasurableSet.univ)
  have htarget : (volume : Measure (ℝ × ℂ)).restrict (Set.Ioi 0 ×ˢ (Set.univ : Set ℂ)) =
      (volume.restrict (Set.Ioi (0:ℝ))).prod (volume : Measure ℂ) := by
    rw [Measure.volume_eq_prod,←Measure.prod_restrict,Measure.restrict_univ]
  have hsource : spatialComplexSplit ⁻¹' (Set.Ioi (0:ℝ) ×ˢ (Set.univ : Set ℂ)) = euclideanUpperHalf := by
    ext p
    simp only [Set.mem_preimage,Set.mem_prod,Set.mem_univ,and_true,Set.mem_Ioi,
      spatialComplexSplit_fst,euclideanUpperHalf,Set.mem_ofPred_eq]
  rw [htarget,hsource] at hm
  have heuc := hm.quasiMeasurePreserving.ae he
  have heuc' : ∀ᵐp ∂volume.restrict euclideanUpperHalf,
      f (euclideanToHyperbolic p)=g (euclideanToHyperbolic p) := by
    simpa only [cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using heuc
  have hweighted : ∀ᵐp ∂hyperbolicEuclideanVolume,
      f (euclideanToHyperbolic p)=g (euclideanToHyperbolic p) :=
    heuc'.filter_mono (withDensity_absolutelyContinuous
      (volume.restrict euclideanUpperHalf) hyperbolicDensity).ae_le
  change ∀ᵐw ∂Measure.map euclideanToHyperbolic hyperbolicEuclideanVolume,f w=g w
  exact (ae_map_iff euclideanToHyperbolic_measurable.aemeasurable (measurableSet_eq_fun hf hg)).mpr hweighted

lemma hyperbolic_eq_ae_of_period_cells (f g : HyperbolicSpace→ℂ)
    (hf : Measurable f) (hg : Measurable g)
    (hfp : ∀(v : ℝ)(hv : 0<v)(z : ℂ)(n : ActualEisensteinCubic.O),
      f (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=f (upperPoint z v hv))
    (hgp : ∀(v : ℝ)(hv : 0<v)(z : ℂ)(n : ActualEisensteinCubic.O),
      g (upperPoint (z+3*ConcreteTraceCRT.eisEmbedding n) v hv)=g (upperPoint z v hv))
    (he : ∀(a b : ℝ)(_ha : 0<a),∀ᵐv ∂volume.restrict (Set.Icc a b),
      (fun z => f (cuspCoordinateLift (v,z)))=ᵐ[volume.restrict periodDomain]
        (fun z => g (cuspCoordinateLift (v,z)))) : f=ᵐ[hyperbolicVolume]g := by
  have hplanes (a b : ℝ) (ha : 0<a) : ∀ᵐv ∂volume.restrict (Set.Icc a b),
      ∀ᵐz ∂volume,f (cuspCoordinateLift (v,z))=g (cuspCoordinateLift (v,z)) := by
    filter_upwards [he a b ha,ae_restrict_mem measurableSet_Icc] with v hv hvm
    have hvp : 0<v := ha.trans_le hvm.1
    apply ae_eq_of_periodDomain_eq _ _ _ _ hv
    · intro n z
      simpa only [cuspCoordinateLift_positive v _ hvp] using hfp v hvp z n
    · intro n z
      simpa only [cuspCoordinateLift_positive v _ hvp] using hgp v hvp z n
  have hheights : ∀ᵐv ∂volume.restrict (Set.Ioi (0:ℝ)),
      ∀ᵐz ∂volume,f (cuspCoordinateLift (v,z))=g (cuspCoordinateLift (v,z)) := by
    rw [positive_height_interval_cover,ae_restrict_iUnion_iff]
    intro n
    exact hplanes _ _ (by positivity)
  apply hyperbolic_ae_of_coordinate_ae f g hf hg
  exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (hf.comp cuspCoordinateLift_measurable) (hg.comp cuspCoordinateLift_measurable))).mpr hheights

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

theorem cubicEisensteinResidue_continuous_representative :
    (fun w => cubicEisensteinResidue (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicResidualFunction := by
  apply hyperbolic_eq_ae_of_period_cells _ _
    ((MeasureTheory.Lp.stronglyMeasurable cubicEisensteinResidue).measurable.comp
      (measurable_integralOrbitProjection _)) cubicResidualFunction_continuous.measurable
  · intro v hv z n
    exact congrArg cubicEisensteinResidue (kernelProjection_upper_period v hv z n)
  · exact cubicResidualFunction_period
  · exact cubicEisensteinResidue_cell_slices_ae

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

lemma kernelProjection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      hyperbolicVolume (integralQuotientVolume globalKubotaKernel) := by
  let proj := integralOrbitProjection globalKubotaKernel
  have hp : Measurable proj := measurable_integralOrbitProjection _
  refine ⟨hp,Measure.AbsolutelyContinuous.mk fun S hS hzero => ?_⟩
  rw [Measure.map_apply hp hS]
  have hd : hyperbolicVolume ((proj ⁻¹' S)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
    simpa only [integralQuotientVolume,proj,
      Measure.map_apply (measurable_integralOrbitProjection _) hS,
      Measure.restrict_apply ((measurable_integralOrbitProjection _) hS)] using hzero
  have hinv : ∀M : globalKubotaKernel,M • (proj ⁻¹' S)=proj ⁻¹' S := by
    intro M
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      change proj (M • u)∈S
      change proj u∈S at hu
      rwa [show proj (M • u)=proj u from integralOrbitProjection_eq _ M u]
    · intro hw
      refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
      change proj (M⁻¹ • w)∈S
      rwa [show proj (M⁻¹ • w)=proj w from integralOrbitProjection_eq _ M⁻¹ w]
  exact globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (proj ⁻¹' S) hinv hd

lemma kernelLevel_character_ae_on_hyperbolic (F : KernelQuotientL2)
    (M : CubicKubota.levelThree)
    (hchar : kernelLevelPullback M F=CubicKubota.complexCharacter M • F) :
    (fun w : HyperbolicSpace => F (integralOrbitProjection globalKubotaKernel
      (complexMatrix M • w))) =ᵐ[hyperbolicVolume]
      (fun w => CubicKubota.complexCharacter M*
        F (integralOrbitProjection globalKubotaKernel w)) := by
  have he : (fun q => F (kernelLevelAction M q))
      =ᵐ[integralQuotientVolume globalKubotaKernel]
        (fun q => CubicKubota.complexCharacter M*F q) := by
    filter_upwards [kernelLevelPullback_ae_eq M F,
      Lp.coeFn_smul (CubicKubota.complexCharacter M) F] with q hq hs
    rw [hchar] at hq
    exact hq.symm.trans hs
  have hl := kernelProjection_quasiMeasurePreserving.ae_eq_comp he
  simpa only [Function.comp_def,kernelLevelAction_mk] using hl

lemma kernelLevel_character_continuous_representative (F : KernelQuotientL2)
    (f : HyperbolicSpace→ℂ) (hf : Continuous f)
    (hrep : (fun w => F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] f)
    (M : CubicKubota.levelThree)
    (hchar : kernelLevelPullback M F=CubicKubota.complexCharacter M • F)
    (w : HyperbolicSpace) :
    f (complexMatrix M • w)=CubicKubota.complexCharacter M*f w := by
  have hcomp := (measurePreserving_smul (complexMatrix M)
    hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp hrep
  have he : (fun p : HyperbolicSpace => f (complexMatrix M • p))
      =ᵐ[hyperbolicVolume] (fun p => CubicKubota.complexCharacter M*f p) := by
    filter_upwards [hcomp,kernelLevel_character_ae_on_hyperbolic F M hchar,hrep] with p hp hc hr
    exact hp.symm.trans (hc.trans (congrArg (fun z => CubicKubota.complexCharacter M*z) hr))
  have hfun := Measure.eq_of_ae_eq he
    (hf.comp (continuous_hyperbolic_action (complexMatrix M)))
    (continuous_const.mul hf)
  exact congrFun hfun w

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

theorem cubicResidualFunction_automorphy (M : CubicKubota.levelThree) (w : HyperbolicSpace) :
    cubicResidualFunction (complexMatrix M • w)=
      CubicKubota.complexCharacter M*cubicResidualFunction w :=
  kernelLevel_character_continuous_representative cubicEisensteinResidue
    cubicResidualFunction cubicResidualFunction_continuous
    cubicEisensteinResidue_continuous_representative M (cubicEisensteinResidue_character M) w

open CubicKubota

lemma sourceProjection_continuous (f : HyperbolicSpace→ℂ) (hf : Continuous f) :
    Continuous (sourceProjection f) := by
  unfold sourceProjection
  apply continuous_const.mul
  apply continuous_finsetSum
  intro q hq
  exact hf.comp (continuous_hyperbolic_action _)

lemma sourceProjection_congr_ae (f g : HyperbolicSpace→ℂ)
    (h : f=ᵐ[hyperbolicVolume]g) : sourceProjection f=ᵐ[hyperbolicVolume]sourceProjection g := by
  have htrans (q : levelTwo ⧸ levelThreeInTwo) :
      (fun w => f (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w))
        =ᵐ[hyperbolicVolume]
      (fun w => g (integralComplexMatrix (rationalEmbedding (sourceRationalSection q)) • w)) :=
    (measurePreserving_smul _ hyperbolicVolume).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [ae_all_iff.mpr htrans] with w hw
  unfold sourceProjection
  congr 1
  exact Finset.sum_congr rfl (fun q _ => hw q)

lemma kernelSourceProjection_hyperbolic_representative (F : KernelQuotientL2)
    (f : HyperbolicSpace→ℂ)
    (hrep : (fun w => F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] f) :
    (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] sourceProjection f := by
  have he := kernelProjection_quasiMeasurePreserving.ae_eq_comp
    (kernelSourceProjection_ae_eq F)
  change (fun w => kernelSourceProjection F (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume]
      sourceProjection (fun w => F (integralOrbitProjection globalKubotaKernel w)) at he
  exact he.trans (sourceProjection_congr_ae _ _ hrep)

def cubicSourceResidualFunction : HyperbolicSpace→ℂ := sourceProjection cubicResidualFunction

lemma cubicSourceResidualFunction_continuous : Continuous cubicSourceResidualFunction :=
  sourceProjection_continuous cubicResidualFunction cubicResidualFunction_continuous

theorem cubicSourceResidualFunction_automorphy (M : levelTwo) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (M:SL(2,ActualEisensteinCubic.O)) • w)=
      levelTwoComplexCharacter M*cubicSourceResidualFunction w :=
  sourceProjection_automorphy cubicResidualFunction cubicResidualFunction_automorphy M w

lemma cubicSourceResidualFunction_rational_invariant (M : SL(2,ℤ)) (w : HyperbolicSpace) :
    cubicSourceResidualFunction (integralComplexMatrix (rationalEmbedding M) • w)=
      cubicSourceResidualFunction w := by
  have he := cubicSourceResidualFunction_automorphy (rationalLift M) w
  rw [levelTwoComplexCharacter_rationalLift,one_mul] at he
  exact he

theorem cubicSourceResidualFunction_represents_projection :
    (fun w => kernelSourceProjection cubicEisensteinResidue
      (integralOrbitProjection globalKubotaKernel w))
      =ᵐ[hyperbolicVolume] cubicSourceResidualFunction :=
  kernelSourceProjection_hyperbolic_representative cubicEisensteinResidue
    cubicResidualFunction cubicEisensteinResidue_continuous_representative

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalUnipotent (t : ℤ) : SL(2,ℤ) :=
  ⟨!![1,t;0,1],by simp [Matrix.det_fin_two]⟩

lemma rationalUnipotent_add (a b : ℤ) :
    rationalUnipotent (a+b)=rationalUnipotent a*rationalUnipotent b := by
  apply Subtype.ext
  change (!![1,a+b;0,1] : Matrix (Fin 2) (Fin 2) ℤ) =
    (!![1,a;0,1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,b;0,1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]

lemma rationalUnipotent_zero : rationalUnipotent 0=1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rationalUnipotent]

lemma rationalUnipotent_one : rationalUnipotent 1=ModularGroup.T := rfl

lemma row_unipotent_conjugate (t : ℤ) (M : levelThree) :
    row (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M)=
      Matrix.vecMul (row M) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  have hmap (u : ℤ) :
      (rationalEmbedding (rationalUnipotent u) : Matrix (Fin 2) (Fin 2) O) =
        !![1,(u : O);0,1] := by
    apply Matrix.ext
    intro i j
    change (Int.castRingHom O) ((!![1,u;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j) = _
    fin_cases i <;> fin_cases j <;> simp
  change ((rationalEmbedding (rationalUnipotent (-t)) * (M : SL(2,O)) *
      (rationalEmbedding (rationalUnipotent (-t)))⁻¹ : SL(2,O)) : Matrix (Fin 2) (Fin 2) O) 1 =
    Matrix.vecMul ((M : SL(2,O)) 1)
      (rationalEmbedding (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) O)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    hmap, Matrix.adjugate_fin_two]
  funext j
  fin_cases j <;> simp [Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]

def cuspUnipotentTranslate (t : ℤ) : CuspCosets→CuspCosets :=
  Quotient.map (fun M => levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M) (by
    intro M N h
    change row (levelThreeConjugate _ M)=row (levelThreeConjugate _ N)
    rw [row_unipotent_conjugate,row_unipotent_conjugate,show row M=row N from h])

lemma cuspUnipotentTranslate_inverse (t : ℤ) (x : CuspCosets) :
    cuspUnipotentTranslate (-t) (cuspUnipotentTranslate t x)=x := by
  induction x using Quotient.inductionOn with
  | _ M =>
    change cosetOf (levelThreeConjugate (rationalEmbedding (rationalUnipotent (- -t)))
      (levelThreeConjugate (rationalEmbedding (rationalUnipotent (-t))) M))=cosetOf M
    rw [←levelThreeConjugate_mul,←map_mul,←rationalUnipotent_add]
    simp only [neg_neg,add_neg_cancel,rationalUnipotent_zero,map_one,levelThreeConjugate_one]

def cuspUnipotentEquiv (t : ℤ) : CuspCosets≃CuspCosets where
  toFun := cuspUnipotentTranslate t
  invFun := cuspUnipotentTranslate (-t)
  left_inv := cuspUnipotentTranslate_inverse t
  right_inv x := by simpa only [neg_neg] using cuspUnipotentTranslate_inverse (-t) x

lemma cosetRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (cosetRow x) (rationalEmbedding (rationalUnipotent t):SL(2,ActualEisensteinCubic.O)) := by
  induction x using Quotient.inductionOn with
  | _ M => exact row_unipotent_conjugate t M

lemma cosetCharacter_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    cosetCharacter (cuspUnipotentEquiv t x)=cosetCharacter x := by
  induction x using Quotient.inductionOn with
  | _ M => exact complexCharacter_conjugate_rational (rationalUnipotent (-t)) M

lemma embeddedRow_cuspUnipotentEquiv (t : ℤ) (x : CuspCosets) :
    embeddedRow (cuspUnipotentEquiv t x)=
      Matrix.vecMul (embeddedRow x) (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)):SL(2,ℂ)) := by
  funext j
  simp only [embeddedRow,Function.comp_def,cosetRow_cuspUnipotentEquiv,
    Matrix.vecMul,dotProduct,map_sum,map_mul,integralComplexMatrix_apply]

lemma summand_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) (x : CuspCosets) :
    summand (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s x=
      summand g s (cuspUnipotentEquiv t x) := by
  rw [summand,summand,cosetCharacter_cuspUnipotentEquiv,
    embeddedRow_cuspUnipotentEquiv,←rowOperator_apply,rowOperator_mul]

theorem eisenstein_unipotent (t : ℤ) (g : SL(2,ℂ)) (s : ℂ) :
    eisenstein (integralComplexMatrix (rationalEmbedding (rationalUnipotent t))*g) s=eisenstein g s := by
  unfold eisenstein
  simp_rw [summand_unipotent]
  exact (cuspUnipotentEquiv t).tsum_eq _

theorem hyperbolicEisenstein_unipotent (t : ℤ) (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (integralComplexMatrix (rationalEmbedding (rationalUnipotent t)) • w)=
      hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g => exact eisenstein_unipotent t g s

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
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_omega_relation : omega^2+omega+1=(0:Eis) := by
  apply eisEmbedding_injective
  simp only [map_add,map_pow,map_one,map_zero,eisEmbedding_omega_actual]
  exact EisensteinEmbedding.omega3_sq

def lowerCuspMatrix (t : Eis) : SL(2,Eis) :=
  ⟨!![1,0;t,1],by simp [Matrix.det_fin_two]⟩

def ramifiedParabolic (t x : Eis) : levelThree := by
  let M : SL(2,Eis) := ⟨!![1-3*t*x,3*x;-3*t^2*x,1+3*t*x],by
    rw [Matrix.det_fin_two]
    change (1-3*t*x)*(1+3*t*x)-(3*x)*(-3*t^2*x)=1
    ring⟩
  refine ⟨M,levelThree_of_entries M ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨-t*x,by change 1-3*t*x-1=3*(-t*x);ring⟩
  · exact ⟨x,by change 3*x-0=3*x;ring⟩
  · exact ⟨-t^2*x,by change -3*t^2*x-0=3*(-t^2*x);ring⟩
  · exact ⟨t*x,by change 1+3*t*x-1=3*(t*x);ring⟩

lemma ramifiedParabolic_mul_lower (t x : Eis) :
    (ramifiedParabolic t x : SL(2,Eis))*lowerCuspMatrix t=
      lowerCuspMatrix t*(upperTranslation x : SL(2,Eis)) := by
  apply Subtype.ext
  change (ramifiedParabolic t x : Matrix (Fin 2) (Fin 2) Eis) *
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) =
    (lowerCuspMatrix t : Matrix (Fin 2) (Fin 2) Eis) *
      (upperTranslation x : Matrix (Fin 2) (Fin 2) Eis)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [ramifiedParabolic,lowerCuspMatrix,upperTranslation,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

lemma ramifiedParabolic_character (t x : Eis) :
    complexCharacter (ramifiedParabolic t x)=
      eisEmbedding (symbol (-t) (1-3*t*x)) := by
  simp only [complexCharacter,MonoidHom.comp_apply,character,ramifiedParabolic]
  apply congrArg eisEmbedding
  apply symbol_congr
  refine ⟨t,?_⟩
  change (-3*t^2*x)-(-t)=(1-3*t*x)*t
  ring

lemma ramifiedParabolic_omega_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic omega (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (A+B)) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega*ActualEisensteinCoordinates.eval A B=primaryCoord B (B-A) := by
    rw [primaryCoord_eq]
    change 1-3*omega*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*(B:Eis)*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  congr 2
  ring

lemma ramifiedParabolic_omega_sq_value (A B : ℤ) :
    complexCharacter (ramifiedParabolic (omega^2) (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding (cubicExp (-(A+B))) := by
  rw [ramifiedParabolic_character]
  have hd : 1-3*omega^2*ActualEisensteinCoordinates.eval A B=primaryCoord (A-B) A := by
    rw [primaryCoord_eq]
    change 1-3*omega^2*((A:Eis)+(B:Eis)*omega)=_
    push_cast
    linear_combination -3*((A:Eis)+(B:Eis)*omega-(B:Eis))*ramified_omega_relation
  rw [hd,symbol_neg_numerator _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) 2,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),linearRay_primaryCoord]
  have he : cubicExp (2*((A-B)*2+(-1)*A))=cubicExp (-(A+B)) := by
    apply cubicExp_eq_of_dvd_sub
    exact ⟨A-B,by ring⟩
  have hs : cubicExp ((A-B)*2+(-1)*A)^2=cubicExp (2*((A-B)*2+(-1)*A)) := by
    rw [pow_two,←cubicExp_add]
    congr 1
    ring
  convert (preTransparency := .instances) congrArg eisEmbedding (hs.trans he) using 1 ; congr 2 ; ring_nf

def ramifiedSourceFunction (t : Eis) (w : HyperbolicSpace) : ℂ :=
  cubicSourceResidualFunction (integralComplexMatrix (lowerCuspMatrix t) • w)

lemma ramifiedSourceFunction_continuous (t : Eis) : Continuous (ramifiedSourceFunction t) :=
  cubicSourceResidualFunction_continuous.comp (continuous_const_smul _)

lemma ramifiedSourceFunction_translate (t x : Eis) (w : HyperbolicSpace) :
    ramifiedSourceFunction t (complexMatrix (upperTranslation x) • w)=
      eisEmbedding (symbol (-t) (1-3*t*x))*ramifiedSourceFunction t w := by
  have he := cubicSourceResidualFunction_automorphy
    (sourceLevelInclusion (ramifiedParabolic t x))
    (integralComplexMatrix (lowerCuspMatrix t) • w)
  rw [sourceLevelInclusion_character,ramifiedParabolic_character] at he
  change cubicSourceResidualFunction
    (integralComplexMatrix (ramifiedParabolic t x : SL(2,Eis)) •
      (integralComplexMatrix (lowerCuspMatrix t) • w))=_ at he
  rw [←mul_smul,←map_mul,ramifiedParabolic_mul_lower,map_mul,mul_smul] at he
  exact he

lemma ramifiedSourceFunction_omega_translate (A B : ℤ) (w : HyperbolicSpace) :
    ramifiedSourceFunction omega
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (A+B))*ramifiedSourceFunction omega w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_value]

lemma ramifiedSourceFunction_omega_sq_translate (A B : ℤ) (w : HyperbolicSpace) :
    ramifiedSourceFunction (omega^2)
      (complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • w)=
      eisEmbedding (cubicExp (-(A+B)))*ramifiedSourceFunction (omega^2) w := by
  rw [ramifiedSourceFunction_translate]
  rw [←ramifiedParabolic_character,ramifiedParabolic_omega_sq_value]

end

section
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
open EisensteinEmbedding (omega3)
local notation "Eis" => ActualEisensteinCubic.O

lemma embedding_cubicExp (n : ℤ) :
    eisEmbedding (cubicExp n)=Complex.exp (2*Real.pi*Complex.I*(n:ℂ)/3) := by
  have hw : omega3=Complex.exp (2*Real.pi*Complex.I/3) := by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    exact ⟨-1,by push_cast;ring⟩
  rw [cubicExp,map_pow,eisEmbedding_omega_actual,hw,←Complex.exp_nat_mul]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-(n/3),?_⟩
  have hn : (n%3).toNat=(n%3) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hnc : ((n%3).toNat:ℂ)=((n%3:ℤ):ℂ) := by exact_mod_cast hn
  have he : ((n%3:ℤ):ℂ)=(n:ℂ)-3*((n/3:ℤ):ℂ) := by
    have he0 : n%3=n-3*(n/3) := by omega
    exact_mod_cast he0
  rw [hnc,he]
  push_cast
  ring

def ramifiedShift10 : ℂ := eisEmbedding (omega-1)/(9*eisLam)

def ramifiedShift19 : ℂ := eisEmbedding (-2-omega)/(9*eisLam)

lemma ramifiedShift10_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (A+B)) := by
  have he : ramifiedShift10*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((omega-1)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift10,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((omega-1)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((omega-1)*ActualEisensteinCoordinates.eval A B)).2=A-2*B := by
    have hw : omega-1=ActualEisensteinCoordinates.eval (-1) 1 := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,one_mul]
      change omega-1=-1+omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,←embedding_cubicExp]
  exact congrArg eisEmbedding (cubicExp_eq_of_dvd_sub ⟨-B,by ring⟩)

lemma ramifiedShift19_period (A B : ℤ) :
    ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B)))=
      eisEmbedding (cubicExp (-(A+B))) := by
  have he : ramifiedShift19*(3*eisEmbedding (ActualEisensteinCoordinates.eval A B))=
      eisEmbedding ((-2-omega)*ActualEisensteinCoordinates.eval A B)/eisLam/3 := by
    rw [ramifiedShift19,map_mul]
    ring
  have ht := breveE_real_trace_of_O (3:ℝ) ((-2-omega)*ActualEisensteinCoordinates.eval A B)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [he,ht]
  have hcoords : (ActualEisensteinCoordinates.coords
      ((-2-omega)*ActualEisensteinCoordinates.eval A B)).2=-(A+B) := by
    have hw : -2-omega=ActualEisensteinCoordinates.eval (-2) (-1) := by
      simp only [ActualEisensteinCoordinates.eval,Int.cast_neg,Int.cast_one,Int.cast_ofNat,neg_mul,one_mul]
      change -2-omega=-2+-omega
      ring
    rw [hw,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
    ring
  rw [hcoords,embedding_cubicExp]

lemma ramifiedSourceFunction_upper_shift10 (x : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction omega (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift10*(3*eisEmbedding x))*
        ramifiedSourceFunction omega (upperPoint z v hv) := by
  let A := (ActualEisensteinCoordinates.coords x).1
  let B := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval A B := (ActualEisensteinCoordinates.eval_coords x).symm
  rw [hx,ramifiedShift10_period]
  have he : upperPoint (z+3*eisEmbedding (ActualEisensteinCoordinates.eval A B)) v hv=
      complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace))
      (upperTranslation_section (ActualEisensteinCoordinates.eval A B) z v hv).symm
  rw [he,ramifiedSourceFunction_omega_translate]

lemma ramifiedSourceFunction_upper_shift19 (x : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    ramifiedSourceFunction (omega^2) (upperPoint (z+3*eisEmbedding x) v hv)=
      ShortDraftTrace.breveE (ramifiedShift19*(3*eisEmbedding x))*
        ramifiedSourceFunction (omega^2) (upperPoint z v hv) := by
  let A := (ActualEisensteinCoordinates.coords x).1
  let B := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval A B := (ActualEisensteinCoordinates.eval_coords x).symm
  rw [hx,ramifiedShift19_period]
  have he : upperPoint (z+3*eisEmbedding (ActualEisensteinCoordinates.eval A B)) v hv=
      complexMatrix (upperTranslation (ActualEisensteinCoordinates.eval A B)) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace))
      (upperTranslation_section (ActualEisensteinCoordinates.eval A B) z v hv).symm
  rw [he,ramifiedSourceFunction_omega_sq_translate]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups ENNReal

def arbitraryCuspCompact (M : SL(2,ℂ)) (a b : ℝ) : Set HyperbolicSpace :=
  (M • ·) '' cuspHeightCompact a b

lemma arbitraryCuspCompact_isCompact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    IsCompact (arbitraryCuspCompact M a b) :=
  (cuspHeightCompact_isCompact a b ha).image (continuous_const_smul M)

lemma arbitraryCusp_image_restrict_le (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)≤
      (1:ℝ≥0∞) • hyperbolicVolume.restrict (arbitraryCuspCompact M a b) := by
  simpa only [one_smul,arbitraryCuspCompact] using Measure.restrict_mono_set hyperbolicVolume
    (Set.image_mono (cuspPeriodStrip_subset_heightCompact a b ha))

lemma arbitraryCusp_smul_measurePreserving (M : SL(2,ℂ)) (a b : ℝ) :
    MeasurePreserving (M • ·) (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b)) :=
  (measurePreserving_smul M hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul M) _

def arbitraryCuspPullback (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    KernelQuotientL2→L[ℂ]CuspHeightStripL2 a b :=
  (Lp.compMeasurePreservingₗᵢ ℂ (M • ·) (arbitraryCusp_smul_measurePreserving M a b)).toContinuousLinearMap.comp
    ((dominatedComplexL2 (by simp : (1:ℝ≥0∞)≠⊤)
      (arbitraryCusp_image_restrict_le M a b ha)).comp
      (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha)))

lemma arbitraryCuspPullback_ae (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (F : KernelQuotientL2) :
    arbitraryCuspPullback M a b ha F=ᵐ[hyperbolicVolume.restrict (cuspPeriodStrip a b)]
      fun w => F (integralOrbitProjection globalKubotaKernel (M • w)) := by
  have h1 := dominatedComplexL2_ae (by simp : (1:ℝ≥0∞)≠⊤)
    (arbitraryCusp_image_restrict_le M a b ha)
    (kernelCompactPullbackCLM (arbitraryCuspCompact M a b)
      (arbitraryCuspCompact_isCompact M a b ha) F)
  have h2 := (Measure.absolutelyContinuous_of_le_smul
    (arbitraryCusp_image_restrict_le M a b ha)).ae_eq
      (kernelCompactPullbackCLM_ae (arbitraryCuspCompact M a b)
        (arbitraryCuspCompact_isCompact M a b ha) F)
  exact (Lp.coeFn_compMeasurePreserving _ (arbitraryCusp_smul_measurePreserving M a b)).trans
    ((arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving.ae_eq_comp (h1.trans h2))

lemma arbitraryCusp_quasiMeasurePreserving (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    Measure.QuasiMeasurePreserving
      (fun w => integralOrbitProjection globalKubotaKernel (M • w))
      (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) := by
  have hcompact : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict (arbitraryCuspCompact M a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨measurable_integralOrbitProjection _,Measure.absolutelyContinuous_of_le_smul
      (kernelCompactMultiplicity_spec _ (arbitraryCuspCompact_isCompact M a b ha))⟩
  have himage : Measure.QuasiMeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict ((M • ·) '' cuspPeriodStrip a b))
      (integralQuotientVolume globalKubotaKernel) :=
    ⟨hcompact.measurable,((Measure.absolutelyContinuous_of_le_smul
      (arbitraryCusp_image_restrict_le M a b ha)).map
        (measurable_integralOrbitProjection _)).trans hcompact.absolutelyContinuous⟩
  exact himage.comp (arbitraryCusp_smul_measurePreserving M a b).quasiMeasurePreserving

def arbitraryCuspQuotientCompact (M : SL(2,ℂ)) (a b : ℝ) : Set KernelQuotient :=
  integralOrbitProjection globalKubotaKernel '' arbitraryCuspCompact M a b

lemma arbitraryCuspQuotientCompact_isCompact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a) :
    IsCompact (arbitraryCuspQuotientCompact M a b) :=
  (arbitraryCuspCompact_isCompact M a b ha).image (continuous_integralOrbitProjection _)

lemma arbitraryCusp_mem_compact (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (w : HyperbolicSpace) (hw : w∈cuspPeriodStrip a b) :
    integralOrbitProjection globalKubotaKernel (M • w)∈arbitraryCuspQuotientCompact M a b :=
  ⟨M • w,⟨w,cuspPeriodStrip_subset_heightCompact a b ha hw,rfl⟩,rfl⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace ENNReal

def arbitraryCuspWeightedPhase (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
    (w : HyperbolicSpace) : ℂ :=
  ρ (hyperbolicHeight w)*ShortDraftTrace.breveE (-freq*hyperbolicHorizontal w)

lemma arbitraryCuspWeightedPhase_continuous (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    Continuous (arbitraryCuspWeightedPhase ρ freq) := by
  unfold arbitraryCuspWeightedPhase
  apply (ρ.continuous.comp hyperbolicHeight_continuous).mul
  change Continuous (fun w : HyperbolicSpace =>
    Complex.exp (2*Real.pi*Complex.I*((-freq*hyperbolicHorizontal w)+
      starRingEnd ℂ (-freq*hyperbolicHorizontal w))))
  have hh := hyperbolicHorizontal_continuous
  fun_prop

lemma arbitraryCuspWeightedPhase_bound (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ)
    (w : HyperbolicSpace) : ‖arbitraryCuspWeightedPhase ρ freq w‖≤‖ρ‖ := by
  rw [arbitraryCuspWeightedPhase,norm_mul,breveE_norm,mul_one]
  exact ρ.norm_coe_le_norm _

lemma arbitraryCuspFourierTest_memLp (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    MemLp (fun w => star (arbitraryCuspWeightedPhase ρ freq w)) 2
      (hyperbolicVolume.restrict (cuspPeriodStrip a b)) := by
  let := cuspPeriodStripFiniteVolume a b ha
  apply MemLp.of_bound (arbitraryCuspWeightedPhase_continuous ρ freq).star.aestronglyMeasurable ‖ρ‖
  exact Eventually.of_forall (fun w => by rw [norm_star];exact arbitraryCuspWeightedPhase_bound ρ freq w)

def arbitraryCuspFourierTestL2 (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : CuspHeightStripL2 a b :=
  (arbitraryCuspFourierTest_memLp a b ha ρ freq).toLp
    (fun w => star (arbitraryCuspWeightedPhase ρ freq w))

def arbitraryCuspHeightFourier (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) : KernelQuotientL2→L[ℂ]ℂ :=
  (innerSL ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq)).comp
    (arbitraryCuspPullback M a b ha)

lemma arbitraryCuspHeightFourier_integral (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ freq F=
      ∫w in cuspPeriodStrip a b,
        F (integralOrbitProjection globalKubotaKernel (M • w))*
          arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  change inner ℂ (arbitraryCuspFourierTestL2 a b ha ρ freq) (arbitraryCuspPullback M a b ha F)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (arbitraryCuspFourierTest_memLp a b ha ρ freq),
    arbitraryCuspPullback_ae M a b ha F] with w hw hp
  rw [RCLike.inner_apply,arbitraryCuspFourierTestL2,hw,hp]
  simp only [starRingEnd_apply,star_star]

lemma arbitraryCuspHeightFourier_restrict (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (F : KernelQuotientL2) :
    arbitraryCuspHeightFourier M a b ha ρ freq
      (kernelMassRestrictionCLM (arbitraryCuspQuotientCompact M a b)
        (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)=
      arbitraryCuspHeightFourier M a b ha ρ freq F := by
  rw [arbitraryCuspHeightFourier_integral,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (kernelMassRestriction_coe (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha).measurableSet F)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  exact congrArg (fun z : ℂ => z*arbitraryCuspWeightedPhase ρ freq w)
    (hw.trans (Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm) _))

def arbitraryCuspHeightFamily (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) (s : ℂ) : ℂ :=
  arbitraryCuspHeightFourier M a b ha ρ freq
    (kernelLocalCorrectedSeed (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) 2 3 (by norm_num) (by norm_num) s)

lemma arbitraryCuspHeightFamily_analyticAt (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (arbitraryCuspHeightFamily M a b ha ρ freq) s :=
  (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (arbitraryCuspHeightFourier M a b ha ρ freq) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _
        (arbitraryCuspQuotientCompact_isCompact M a b ha)
        2 3 (by norm_num) (by norm_num) s hs hi) rfl

lemma arbitraryCuspHeightFamily_residue_limit (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq : ℂ) :
    Tendsto (fun s : ℂ => (s-4/3)*arbitraryCuspHeightFamily M a b ha ρ freq s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (arbitraryCuspHeightFourier M a b ha ρ freq cubicEisensteinResidue)) := by
  have hh := (arbitraryCuspHeightFourier M a b ha ρ freq).continuous.continuousAt.tendsto.comp
    (cubicEisensteinResidue_local_limit _ (arbitraryCuspQuotientCompact_isCompact M a b ha))
  simpa only [Function.comp_def,map_smul,smul_eq_mul,arbitraryCuspHeightFourier_restrict,
    arbitraryCuspHeightFamily] using hh

lemma arbitraryCuspHeightFamily_initial (M : SL(2,ℂ)) (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    arbitraryCuspHeightFamily M a b ha ρ freq s=
      ∫w in cuspPeriodStrip a b,hyperbolicEisenstein s (M • w)*
        arbitraryCuspWeightedPhase ρ freq w∂hyperbolicVolume := by
  rw [arbitraryCuspHeightFamily,arbitraryCuspHeightFourier_integral]
  have he := (arbitraryCusp_quasiMeasurePreserving M a b ha).ae_eq_comp
    (cubicEisensteinLocalFamily_initial_ae (arbitraryCuspQuotientCompact M a b)
      (arbitraryCuspQuotientCompact_isCompact M a b ha) s hs hi)
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable a b)] with w hw hwm
  dsimp only [Function.comp_def] at hw
  rw [hw,Set.indicator_of_mem (arbitraryCusp_mem_compact M a b ha w hwm),kernelQuotientEisenstein_mk]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

lemma inner_projection_sandwich {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : E →L[ℂ] G) (K : Submodule ℂ E) [K.HasOrthogonalProjection] (x y : G) :
    inner ℂ x (A (K.starProjection (A.adjoint y))) =
      inner ℂ (A (K.starProjection (A.adjoint x))) y := by
  rw [← A.adjoint_inner_left, ← A.adjoint_inner_right]
  exact (K.inner_starProjection_left_eq_right _ _).symm

lemma kernelThetaMassProjection_symmetric (F D : KernelQuotientL2) :
    inner ℂ F (kernelThetaMassProjection D)=inner ℂ (kernelThetaMassProjection F) D :=
  inner_projection_sandwich kernelEnergyMass kernelThetaNull F D

lemma kernelThetaMassProjection_eigenvector (F : KernelQuotientL2)
    (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    kernelThetaMassProjection F=(9/17:ℂ) • F := by
  let u : kernelEnergyLaplacian.domain := ⟨F,LinearPMap.mem_domain_of_mem_graph hF⟩
  have hu : kernelEnergyLaplacian u=(8/9:ℂ) • F :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph u) hF rfl
  let E : KernelEnergyGraph := kernelVariationalSolution (kernelEnergyLaplacian u+u)
  have hE : E∈kernelThetaNull := by
    change kernelSpectralFormOperator (8/9:ℂ) E=0
    dsimp only [E]
    rw [kernelSpectralFormOperator_of_domain,hu]
    change kernelVariationalSolution ((8/9:ℂ) • F-(8/9:ℂ) • F)=0
    rw [sub_self,map_zero]
  have hmass : kernelEnergyMass E=F := kernelEnergyLaplacian_resolvent_relation u
  have hscale : kernelEnergyMass.adjoint F=(9/17:ℂ) • E := by
    dsimp [E]
    rw [hu]
    change kernelVariationalSolution F=(9/17:ℂ) • kernelVariationalSolution ((8/9:ℂ) • F+F)
    rw [map_add,map_smul,smul_add,smul_smul]
    module
  change kernelEnergyMass (kernelThetaNull.starProjection (kernelEnergyMass.adjoint F))=_
  rw [hscale,map_smul,kernelThetaNull.starProjection_eq_self_iff.mpr hE,map_smul,hmass]

theorem kernelEisensteinResidueVector_pairing (a b : ℝ) (ha : 0<a) (hab : a<b)
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph) :
    inner ℂ F (kernelEisensteinResidueVector a b ha hab)=
      (3/2:ℂ)*inner ℂ F (kernelL2Defect a b ha hab (4/3)) := by
  rw [kernelEisensteinResidueVector,inner_smul_right,kernelThetaMassProjection_symmetric,
    kernelThetaMassProjection_eigenvector F hF,inner_smul_left]
  simp only [map_div₀,map_ofNat]
  ring

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

lemma kernelLocalCorrectedSeed_initial_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d)
    (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    kernelLocalCorrectedSeed S hS a b (by linarith) hab s=
      kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  have h1 := kernelLocalCorrectedSeed_ae_eq S hS a b (by linarith) hab s
  have h2 := kernelLocalCorrectedSeed_ae_eq S hS c d (by linarith) hcd s
  have h3 := kernelEisensteinL2Correction_initial_overlap a b ha hab s hs hi
  have h4 := kernelEisensteinL2Correction_initial_overlap c d hc hcd s hs hi
  apply Lp.ext
  filter_upwards [h1,h2,h3,h4] with q hq1 hq2 hq3 hq4
  rw [hq1,hq2]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed,hq3,hq4]
    ring
  · simp only [Set.indicator_of_notMem hq]

lemma kernelLocalCorrectedSeed_cutoff_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    ∀s∈cuspUpperParameterRegion,
      kernelLocalCorrectedSeed S hS a b (by linarith) hab s=
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd s := by
  have h1 : AnalyticOnNhd ℂ
      (kernelLocalCorrectedSeed S hS a b (by linarith) hab) cuspUpperParameterRegion := by
    intro s hs
    exact kernelLocalCorrectedSeed_analyticAt_nonreal S hS a b (by linarith) hab s
      (by linarith [hs.1]) hs.2.ne'
  have h2 : AnalyticOnNhd ℂ
      (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) cuspUpperParameterRegion := by
    intro s hs
    exact kernelLocalCorrectedSeed_analyticAt_nonreal S hS c d (by linarith) hcd s
      (by linarith [hs.1]) hs.2.ne'
  have hV : IsOpen {s : ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have he : (kernelLocalCorrectedSeed S hS a b (by linarith) hab)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (kernelLocalCorrectedSeed S hS c d (by linarith) hcd) := by
    filter_upwards [hV.mem_nhds (by norm_num)] with s hs
    exact kernelLocalCorrectedSeed_initial_eq S hS a b c d ha hab hc hcd s hs.1 hs.2
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 cuspUpperParameterRegion_convex.isPreconnected
    (by norm_num [cuspUpperParameterRegion]) he

lemma kernelEisensteinResidueVector_restrict_cutoff_eq
    (S : Set KernelQuotient) (hS : IsCompact S)
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector a b (by linarith) hab)=
      kernelMassRestrictionCLM S hS.measurableSet
        (kernelEisensteinResidueVector c d (by linarith) hcd) := by
  have h1 := (kernelLocalCorrectedSeed_residue_limit S hS a b (by linarith) hab).comp
    thetaApproach_tendsto_complex_punctured
  have h2 := (kernelLocalCorrectedSeed_residue_limit S hS c d (by linarith) hcd).comp
    thetaApproach_tendsto_complex_punctured
  have he : (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS a b (by linarith) hab
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t : ℝ =>
      ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I-4/3) •
        kernelLocalCorrectedSeed S hS c d (by linarith) hcd
          ((4/3:ℂ)+(t:ℂ)+(t:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    rw [kernelLocalCorrectedSeed_cutoff_eq S hS a b c d ha hab hc hcd _
      (by constructor <;> simp [] <;> linarith)]
  exact tendsto_nhds_unique h1 (h2.congr' he.symm)

lemma kernelL2_eq_of_compact_restrictions (F G : KernelQuotientL2)
    (h : ∀S : Set KernelQuotient, ∀hS : IsCompact S,
      kernelMassRestrictionCLM S hS.measurableSet F=
        kernelMassRestrictionCLM S hS.measurableSet G) : F=G := by
  let S : ℕ→Set KernelQuotient := fun n => {q | kernelQuotientBarrier 2 3 q≤n}
  have hS (n : ℕ) : IsCompact (S n) := kernelBarrier_sublevel_isCompact n
  have he (n : ℕ) : ∀ᵐq∂integralQuotientVolume globalKubotaKernel, q∈S n → F q=G q := by
    have hi := h (S n) (hS n)
    have hf := kernelMassRestriction_coe (S n) (hS n).measurableSet F
    have hg := kernelMassRestriction_coe (S n) (hS n).measurableSet G
    filter_upwards [hf,hg] with q hf hg hq
    rw [Set.indicator_of_mem hq] at hf hg
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet F q=F q at hf
    change kernelMassRestrictionCLM (S n) (hS n).measurableSet G q=G q at hg
    rw [hi] at hf
    exact hf.symm.trans hg
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with q hq
  obtain ⟨n,hn⟩ := exists_nat_ge (kernelQuotientBarrier 2 3 q)
  exact hq n hn

theorem kernelEisensteinResidueVector_cutoff_independent
    (a b c d : ℝ) (ha : 1<a) (hab : a<b) (hc : 1<c) (hcd : c<d) :
    kernelEisensteinResidueVector a b (by linarith) hab=
      kernelEisensteinResidueVector c d (by linarith) hcd := by
  apply kernelL2_eq_of_compact_restrictions
  intro S hS
  exact kernelEisensteinResidueVector_restrict_cutoff_eq S hS a b c d ha hab hc hcd

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
open scoped BigOperators Classical MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalComplex : SL(2,ℤ) →* SL(2,ℂ) := integralComplexMatrix.comp rationalEmbedding

lemma rationalUnipotent_nat (n : ℕ) : rationalUnipotent (n:ℤ)=ModularGroup.T^n := by
  induction n with
  | zero => simpa using rationalUnipotent_zero
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,rationalUnipotent_add,ih,rationalUnipotent_one,pow_succ]

lemma rationalComplex_S_sq_row (v : Fin 2→ℂ) :
    rowOperator (rationalComplex (ModularGroup.S^2)) v = -v := by
  have hS : ((ModularGroup.S ^ 2 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1,0;0,-1] := by decide
  have hC : (rationalComplex (ModularGroup.S ^ 2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![-1,0;0,-1] := by
    apply Matrix.ext
    intro i j
    change eisEmbedding ((Int.castRingHom O) ((ModularGroup.S ^ 2 : SL(2,ℤ)) i j)) = _
    rw [congrFun (congrFun hS i) j]
    fin_cases i <;> fin_cases j <;> simp
  rw [rowOperator_apply,hC]
  funext j
  fin_cases j <;> simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma hyperbolicEisenstein_S_sq (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^2) • w)=hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    change eisenstein (rationalComplex (ModularGroup.S^2)*g) s=eisenstein g s
    apply tsum_congr
    intro x
    unfold summand
    rw [←rowOperator_mul,rationalComplex_S_sq_row,map_neg]
    simp [rowEnergy]

lemma hyperbolicEisenstein_T_pow (s : ℂ) (n : ℕ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.T^n) • w)=hyperbolicEisenstein s w := by
  simpa only [rationalUnipotent_nat,rationalComplex,MonoidHom.comp_apply] using hyperbolicEisenstein_unipotent (n:ℤ) s w

lemma hyperbolicEisenstein_S_even (s : ℂ) (e : Fin 2) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^(2*e.val)) • w)=hyperbolicEisenstein s w := by
  fin_cases e
  · simp
  · exact hyperbolicEisenstein_S_sq s w

lemma hyperbolicEisenstein_bruhat (s : ℂ) (e : Fin 2) (a : Fin 3⊕(Fin 3×Fin 3)) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep (e,a)) • w)=
      match a with
      | Sum.inl _ => hyperbolicEisenstein s w
      | Sum.inr ab => hyperbolicEisenstein s
          (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^ab.2.val) • w)) := by
  simp only [rationalBruhatRep,map_mul,mul_smul,hyperbolicEisenstein_S_even]
  cases a with
  | inl a => exact hyperbolicEisenstein_T_pow s a.val w
  | inr ab => simp only [map_mul,mul_smul,hyperbolicEisenstein_T_pow]

theorem sourceEisenstein_four_cusps (s : ℂ) (w : HyperbolicSpace) :
    sourceEisenstein s w = (4:ℂ)⁻¹ * (hyperbolicEisenstein s w +
      ∑ b : Fin 3, hyperbolicEisenstein s
        (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^b.val) • w))) := by
  rw [sourceEisenstein,sourceProjection_eq_twentyFour]
  change (24:ℂ)⁻¹ * (∑ i : RationalBruhatIndex,
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep i) • w)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hyperbolicEisenstein_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  ring

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedCuspCompact (M:levelTwo):Set KernelQuotient:=
  kernelSourceAction M '' kernelCuspAverageCompact

lemma translatedCuspCompact_isCompact (M:levelTwo):IsCompact (translatedCuspCompact M):=
  kernelCuspAverageCompact_isCompact.image (kernelSourceAction_continuous M)

def translatedCuspFourier (h:Eis) (M:levelTwo):KernelQuotientL2→L[ℂ]ℂ:=
  (kernelCuspFourier h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedCuspFourier_integral (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M F=∫w in cuspPeriodStrip 5 6,
      F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,kernelCuspFourier_integral]
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelSourcePullback_ae_eq M F) (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w) hw

lemma translatedCuspFourier_restrict (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M
      (kernelMassRestrictionCLM (translatedCuspCompact M)
        (translatedCuspCompact_isCompact M).measurableSet F)=translatedCuspFourier h M F:=by
  rw [translatedCuspFourier_integral,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedCuspCompact M)
      (translatedCuspCompact_isCompact M).measurableSet F)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

def translatedCuspFamily (h:Eis) (M:levelTwo) (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):ℂ:=
  translatedCuspFourier h M
    (kernelLocalCorrectedSeed (translatedCuspCompact M) (translatedCuspCompact_isCompact M) a b ha hab s)

lemma translatedCuspFamily_analyticAt_nonreal (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0):
    AnalyticAt ℂ (translatedCuspFamily h M a b ha hab) s:=by
  exact (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedCuspFourier h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedCuspCompact_isCompact M)
        a b ha hab s hs hi) rfl

lemma translatedCuspFamily_residue_limit (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b):
    Tendsto (fun s:ℂ=>(s-4/3)*translatedCuspFamily h M a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (translatedCuspFourier h M (kernelEisensteinResidueVector a b ha hab))):=by
  have hh:=(translatedCuspFourier h M).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit _ (translatedCuspCompact_isCompact M) a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedCuspFourier_restrict,
    translatedCuspFamily] using hh

lemma translatedCuspFamily_actual_integral (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s
        (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
          cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFamily,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLocalCorrectedSeed_ae_eq _ (translatedCuspCompact_isCompact M) a b ha hab s)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

theorem translatedCuspFamily_initial (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (ha1:1<a) (s:ℂ) (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume:=by
  have hcorrected:kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith):=by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap a b ha1 hab s hs hi] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  rw [translatedCuspFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (by dsimp only [Function.comp_def];rw [kernelSourceAction_mk,kernelQuotientEisenstein_mk]))

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def oppositeSource:levelTwo:=rationalLift ModularGroup.S

lemma oppositeSource_matrix:sourceComplexMatrix oppositeSource=oppositeMatrix:=by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oppositeSource,sourceComplexMatrix,rationalLift,rationalEmbedding,
      integralComplexMatrix,Matrix.SpecialLinearGroup.map_apply_coe,ModularGroup.coe_S,oppositeMatrix]

lemma hyperbolicEisenstein_opposite_upper (s:ℂ) (z:ℂ) (v:ℝ) (hv:0<v):
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • upperPoint z v hv)=
      oppositeEisenstein z v hv s:=by
  rw [oppositeSource_matrix]
  rfl

theorem opposite_cusp_fourier_average (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspWhittakerHeightFactor s h:=by
  let g:HyperbolicSpace→ℂ:=fun w=>
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*cuspFourierPhase h w
  have hg:Continuous g:=((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable g hg)]
  have heq:(∫v in Set.Icc (5:ℝ) 6,
      (∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,unramifiedCubicGaussSeries s (9*h)*
        ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)):=by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0:0<v:=by linarith [hv.1]
    have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
    have hslice:(∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
          unramifiedCubicGaussSeries s (9*h):=by
      simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
        cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      exact oppositeEisenstein_fourier v hv0 s hs h
    have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3:=by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hslice,hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma translatedCuspFamily_opposite_initial (h:Eis) (s:ℂ)
    (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num) s=
      unramifiedCubicGaussSeries s h*cuspWhittakerHeightFactor s (3*h):=by
  rw [translatedCuspFamily_initial (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num) (by norm_num) s hs hi,
    opposite_cusp_fourier_average s (by linarith),
    show (9:Eis)*(3*h)=27*h by ring,unramifiedCubicGaussSeries_twentySeven]

def unramifiedGaussResidue (h:Eis):ℂ:=
  translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue/
    cuspWhittakerHeightFactor (4/3:ℂ) (3*h)

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma gaussRep_mk_congr (c d : Eis) :
    c ∣ GaussianShiftedPartition.representative c (Ideal.Quotient.mk (Ideal.span {c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact GaussianShiftedPartition.representative_spec c _

def cubicUnitCRTMap (a b : Eis) (r : CubicUnitResidue (a*b)) :
    CubicUnitResidue a × CubicUnitResidue b :=
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let hd:IsCoprime (a*b) d:=by
    apply (isUnit_quotient_span_iff (a*b) d).mp
    simpa only [d,GaussianShiftedPartition.representative_spec] using r.2
  (⟨Ideal.Quotient.mk (Ideal.span {a}) d,
      (isUnit_quotient_span_iff a d).mpr hd.of_mul_left_left⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr hd.of_mul_left_right⟩)

lemma cubicUnitCRTMap_injective (a b : Eis) (hab : IsCoprime a b) :
    Function.Injective (cubicUnitCRTMap a b) := by
  intro r t he
  have h1:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.1.1) he
  have h2:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.2.1) he
  change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) t.1) at h1
  change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) t.1) at h2
  have hdiv : a*b ∣ GaussianShiftedPartition.representative (a*b) r.1-
      GaussianShiftedPartition.representative (a*b) t.1 :=
    hab.mul_dvd
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
  apply Subtype.ext
  rw [←GaussianShiftedPartition.representative_spec (a*b) r.1,
    ←GaussianShiftedPartition.representative_spec (a*b) t.1]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)

lemma cubicUnitCRTMap_surjective (a b : Eis) (hab : IsCoprime a b) :
    Function.Surjective (cubicUnitCRTMap a b) := by
  rintro ⟨r,t⟩
  obtain ⟨u,v,huv⟩:=hab
  let delta:=GaussianShiftedPartition.representative a r.1
  let xi:=GaussianShiftedPartition.representative b t.1
  let d:=v*b*delta+u*a*xi
  have hda:a∣d-delta:=⟨u*(xi-delta),by dsimp [d];linear_combination delta*huv⟩
  have hdb:b∣d-xi:=⟨v*(delta-xi),by dsimp [d];linear_combination xi*huv⟩
  have had:IsCoprime a delta:=by
    apply (isUnit_quotient_span_iff a delta).mp
    simpa only [delta,GaussianShiftedPartition.representative_spec] using r.2
  have hbd:IsCoprime b xi:=by
    apply (isUnit_quotient_span_iff b xi).mp
    simpa only [xi,GaussianShiftedPartition.representative_spec] using t.2
  have hd:IsCoprime (a*b) d:=
    ((isCoprime_right_congr_of_dvd a d delta hda).mpr had).mul_left
      ((isCoprime_right_congr_of_dvd b d xi hdb).mpr hbd)
  let q:CubicUnitResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {a*b}) d,
    (isUnit_quotient_span_iff (a*b) d).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) q.1)=r.1
    rw [←GaussianShiftedPartition.representative_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:a∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_right a b).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:b∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_left b a).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hdb

def cubicUnitCRTEquiv (a b:Eis) (hab:IsCoprime a b):
    CubicUnitResidue (a*b)≃CubicUnitResidue a×CubicUnitResidue b:=
  Equiv.ofBijective (cubicUnitCRTMap a b)
    ⟨cubicUnitCRTMap_injective a b hab,cubicUnitCRTMap_surjective a b hab⟩

lemma residueAdditive_unit_crt (h a b alpha beta d:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    residueAdditive (3*h) (a*b) d=
      residueAdditive (3*(h*alpha)) a d*residueAdditive (3*(h*beta)) b d:=by
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  have hbeq:=congrArg eisEmbedding hbez
  simp only [map_add,map_mul,map_one] at hbeq
  simp only [cuspFrequency,map_mul,map_ofNat]
  field_simp [hae,hbe,eisLam_ne_zero]
  linear_combination -(eisEmbedding h*eisEmbedding d)*hbeq

lemma cubicUnitCRT_summand (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1) (r:CubicUnitResidue (a*b)):
    eisEmbedding (symbol (GaussianShiftedPartition.representative (a*b) r.1) (a*b))*
      residueAdditive (3*h) (a*b) (GaussianShiftedPartition.representative (a*b) r.1)=
    (eisEmbedding (symbol (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1) a)*
      residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1))*
    (eisEmbedding (symbol (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1)):=by
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let delta:=GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1
  let xi:=GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1
  have hdelta:a∣delta-d:=gaussRep_mk_congr a d
  have hxi:b∣xi-d:=gaussRep_mk_congr b d
  change eisEmbedding (symbol d (a*b))*residueAdditive (3*h) (a*b) d=
    (eisEmbedding (symbol delta a)*residueAdditive (3*(h*alpha)) a delta)*
    (eisEmbedding (symbol xi b)*residueAdditive (3*(h*beta)) b xi)
  rw [symbol_mul_denominator,map_mul,symbol_congr hdelta,symbol_congr hxi,
    residueAdditive_unit_crt h a b alpha beta d ha hb hbez,
    residueAdditive_three_congr (h*alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h*beta) b xi d hb hxi]
  ring

theorem cubicUnitGaussSum_crt (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    cubicUnitGaussSum h (a*b)=
      cubicUnitGaussSum (h*alpha) a*cubicUnitGaussSum (h*beta) b:=by
  have hab:IsCoprime a b:=⟨beta,alpha,by linear_combination hbez⟩
  let f:CubicUnitResidue a→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative a r.1) a)*
    residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a r.1)
  let g:CubicUnitResidue b→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative b r.1) b)*
    residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b r.1)
  have he:cubicUnitGaussSum h (a*b)=∑'r:CubicUnitResidue (a*b),
      f (cubicUnitCRTEquiv a b hab r).1*g (cubicUnitCRTEquiv a b hab r).2:=by
    unfold cubicUnitGaussSum
    apply tsum_congr
    intro r
    exact cubicUnitCRT_summand h a b alpha beta ha hb hbez r
  rw [he,(cubicUnitCRTEquiv a b hab).tsum_eq (fun r=>f r.1*g r.2)]
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  let:Finite (Eis⧸Ideal.span {b}):=finite_quotient_span hb
  let:Fintype (CubicUnitResidue a):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue b):=Fintype.ofFinite _
  change (∑'r:CubicUnitResidue a×CubicUnitResidue b,f r.1*g r.2)=
    (∑'r:CubicUnitResidue a,f r)*(∑'r:CubicUnitResidue b,g r)
  simp only [tsum_fintype,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

theorem cubicUnitGaussSum_coprime_product (h a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b):
    cubicUnitGaussSum h (a*b)=cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez':alpha*b+beta*a=1:=by linear_combination hbez
  have hab':IsCoprime a b:=⟨beta,alpha,hbez⟩
  have hA:=cubicUnitGaussSum_frequency_twist (h*alpha) a b ha hap hab'
  rw [cubicUnitGaussSum_frequency_congr _ h a ha
    (show a∣(h*alpha)*b-h from ⟨-h*beta,by linear_combination h*hbez'⟩)] at hA
  have hB:=cubicUnitGaussSum_frequency_twist (h*beta) b a hb hbp hab'.symm
  rw [cubicUnitGaussSum_frequency_congr _ h b hb
    (show b∣(h*beta)*a-h from ⟨-h*alpha,by linear_combination h*hbez'⟩)] at hB
  rw [cubicUnitGaussSum_crt h a b alpha beta ha hb hbez',←hA,←hB,
    symbol_reciprocity b a hb ha hbp hap]
  have hshift:=cubicUnitGaussSum_frequency_twist h b a hb hbp hab'.symm
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hbp hab',map_one]
  rw [←hshift]
  calc
    _=(eisEmbedding (symbol a b))^3*cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by ring
    _=_:=by rw [hc,one_mul]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedCongruence_zero (j : Fin 3) (n : ℕ) :
    ramifiedCongruence (0:Eis) j.val n ↔ j=0 ∧ 3∣n := by
  have hz : ActualEisensteinCoordinates.coords (0:Eis)=(0,0) := by
    have hh:=ShortDraftLatticeCount.coords_eval 0 0
    simpa [ActualEisensteinCoordinates.eval] using hh
  simp only [ramifiedCongruence,hz,add_zero,sub_zero]
  rw [←Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨h1,h2⟩
    have hj : j.val=0 := by omega
    exact ⟨Fin.ext hj,by simpa only [hj,Nat.cast_zero,Nat.cast_ofNat,mul_zero,zero_add] using h1⟩
  · rintro ⟨rfl,hn⟩
    simpa using And.intro hn (dvd_zero (3:ℤ))

lemma arithmeticResidueSum_zero_ramified (u : Eisˣ) (n : ℕ) :
    arithmeticResidueSum 0 (u.val*lambda^(n+2))=
      if u=1 ∨ u= -1 then if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0 else 0 := by
  have hp : residueAdditive (0:Eis) 3 1=1 := by
    simp [residueAdditive,cuspFrequency]
  by_cases hu : u=1 ∨ u= -1
  · have hs : (u:Eis)=omega^0 ∨ (u:Eis)=-(omega^0) := by
      rcases hu with rfl|rfl <;> simp
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) 0 (by omega) hs (by simp),
      show ramifiedCongruence (0:Eis) 0 (n+2) ↔ 3∣n+2 by
        simpa using ramifiedCongruence_zero (0:Fin 3) (n+2),hp,mul_one,if_pos hu]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
  · obtain ⟨j,hj⟩:=unit_eq_sign_omega u
    have hj0 : j≠0 := by
      intro he
      subst j
      apply hu
      rcases hj with hj|hj
      · left; apply Units.ext; simpa using hj
      · right; apply Units.ext; simpa using hj
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) j.val (by omega) hj (by simp),
      ramifiedCongruence_zero,if_neg (by simp [hj0]),if_neg hu]

lemma arithmeticDirichletSeries_zero_separate (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
        arithmeticResidueSum 0 (u.val*lambda^(n+2)))*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs 0,←tsum_mul_right]
  apply tsum_congr
  intro u
  rw [←tsum_mul_right]
  apply tsum_congr
  intro n
  rw [unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  change (if ramifiedLower u n I=0 then 0 else
    ((‖eisEmbedding (ramifiedLower u n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (ramifiedLower u n I))=_
  rw [if_neg (ramifiedLower_ne_zero u n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,ramifiedLower_span,map_mul,map_pow,ramifiedIdeal_absNorm,
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  rw [show arithmeticResidueSum 0 (ramifiedLower u n I)=
      eisEmbedding (symbol (u.val*lambda^(n+2)) (primaryGenerator I.1))*
      eisEmbedding (symbol (3*(u.val*lambda^(n+2))) (primaryGenerator I.1))*
      arithmeticResidueSum 0 (u.val*lambda^(n+2))*cubicUnitGaussSum 0 (primaryGenerator I.1) from
    arithmeticResidueSum_ramified_split 0 u (n+2) (by omega) _ hp]
  have hg:=cubicUnitGaussSum_phase_shift 0 (u.val*lambda^(n+2)) (primaryGenerator I.1)
    I.2 hp (ramified_primary_coprime u (n+2) _ hp)
  simp only [zero_mul] at hg
  linear_combination ((3^(n+2):ℕ):ℂ)^(-s)*(Ideal.absNorm I.1:ℂ)^(-s)*
    arithmeticResidueSum 0 (u.val*lambda^(n+2))*hg

def ramifiedCubeExponent : ℕ ≃ {n:ℕ // 3∣n+2} :=
  Equiv.ofBijective (fun k=>⟨3*k+1,by use k+1;omega⟩) ⟨by
    intro a b h
    have hh:=congrArg Subtype.val h
    dsimp at hh
    omega,by
    rintro ⟨n,k,hk⟩
    refine ⟨k-1,Subtype.ext ?_⟩
    dsimp
    omega⟩

lemma zero_ramified_geometric (s : ℂ) (hs : 1<s.re) :
    (∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  let F : ℕ→ℂ := fun n=>((3^(n+2):ℕ):ℂ)^(-s)*
    (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0)
  have hsup:Function.support F⊆{n:ℕ|3∣n+2} := by
    intro n hn
    by_contra h
    change ¬3∣n+2 at h
    exact hn (by simp [F,h])
  change (∑'n,F n)=_
  rw [←tsum_subtype_eq_of_support_subset hsup]
  change (∑'n : {n:ℕ // 3∣n+2},F n.val)=_
  rw [←ramifiedCubeExponent.tsum_eq]
  have he (k:ℕ) : F (ramifiedCubeExponent k).val=ramifiedRatio s^(k+1) := by
    change ((3^(3*k+1+2):ℕ):ℂ)^(-s)*(if 3∣3*k+1+2 then ((3^(3*k+1+2):ℕ):ℂ) else 0)=_
    rw [if_pos (by use k+1;omega),show 3*k+1+2=3*(k+1) by omega]
    simpa using cube_norm_weight_algebra s k 1 (by decide)
  simp_rw [he]
  exact ramified_geometric_sum s hs

lemma zero_ramified_factor (s : ℂ) (hs : 1<s.re) :
    (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      arithmeticResidueSum 0 (u.val*lambda^(n+2)))=
      2*((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hne : (1:Eisˣ)≠ -1 := by
    intro h
    have hh:=congrArg Units.val h
    norm_num at hh
  rw [tsum_eq_sum (s:={1,-1}) (fun u hu=>by
    have hn : ¬(u=1 ∨ u= -1):=by simpa using hu
    simp [arithmeticResidueSum_zero_ramified,hn])]
  simp only [Finset.sum_insert,Finset.mem_singleton,hne,not_false_eq_true,Finset.sum_singleton]
  simp only [arithmeticResidueSum_zero_ramified,true_or,or_true,ite_true]
  rw [zero_ramified_geometric s hs]
  ring

theorem arithmeticDirichletSeries_zero_unramified (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (2*((3:ℂ)^(3*s-3)-1)⁻¹)*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_zero_separate s hs,zero_ramified_factor s (by linarith)]

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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma ramified_denominator_ne_zero (s : ℂ) (hs : 1<s.re) :
    (3:ℂ)^(3*s-3)-1≠0 := by
  intro he
  have hpow : (3:ℂ)^(3*s-3)=1 := sub_eq_zero.mp he
  have hnorm : 1<‖(3:ℂ)^(3*s-3)‖ := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.one_lt_rpow (by norm_num)
    norm_num
    linarith
  rw [hpow,norm_one] at hnorm
  exact lt_irrefl _ hnorm

lemma cuspWhittakerHeightFactor_zero (s : ℂ) (hs : 1<s.re) :
    cuspWhittakerHeightFactor s 0=((Real.pi:ℂ)/(s-1))*cuspScatterHeightFactor s := by
  have hs0 : s≠0 := by intro he;subst s;norm_num at hs
  unfold cuspWhittakerHeightFactor
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero s hs]
  rw [integral_mul_const,cuspScatterHeightFactor_integral s hs0]
  ring

lemma opposite_zero_initial_cross (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s=
      ((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s := by
  have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
    apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
      s (by linarith) (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)).trans
    exact hyperbolicEisenstein_cusp_average_eq s (by linarith)
  have ht:=translatedCuspFamily_opposite_initial 0 s hs hi
  simp only [mul_zero] at ht
  rw [ht,cuspWhittakerHeightFactor_zero s (by linarith),baseOutgoingConstant,hb,
    cuspConstantAverage,scatteringCoefficient,arithmeticDirichletSeries_zero_unramified s (by linarith)]
  have hs1 : s-1≠0 := by intro he;have hsx : s=1:=sub_eq_zero.mp he;subst s;norm_num at hs
  have halg (D V A P H U : ℂ) (hD:D≠0) (hV:V≠0) :
      2*(U*(P*H))=D*(V*(A+P*((2*D⁻¹)*U/V)*H)-V*A) := by
    field_simp
    ; ring
  exact halg _ _ _ _ _ _ (ramified_denominator_ne_zero s (by linarith)) cusp_volume_ne_zero

lemma opposite_zero_cross_identity :
    Set.EqOn (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s)
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s) domain := by
    intro s hs
    exact analyticAt_const.mul (translatedCuspFamily_analyticAt_nonreal 0 oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hright : AnalyticOnNhd ℂ
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) domain := by
    intro s hs
    have hp : AnalyticAt ℂ (fun z:ℂ=>(3:ℂ)^(3*z-3)-1) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      exact Eventually.of_forall fun z=>
        ((((differentiableAt_const (3:ℂ)).mul differentiableAt_id).sub_const 3).const_cpow
          (Or.inl (by norm_num))).sub_const 1
    exact hp.mul (baseOutgoingConstant_analyticAt s hs.1 hs.2)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact opposite_zero_initial_cross s hs.1 hs.2
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

theorem translatedCuspFourier_opposite_zero_residue :
    translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=cuspConstantAverageResidue := by
  have hd : Tendsto (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) (𝓝[≠] (4/3:ℂ)) (𝓝 (2:ℂ)) := by
    have hc : Continuous (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) :=
      (((continuous_const.mul continuous_id).sub continuous_const).const_cpow
        (Or.inl (by norm_num))).sub continuous_const
    convert (preTransparency := .instances) hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hl := ((translatedCuspFamily_residue_limit 0 oppositeSource 2 3
    (by norm_num) (by norm_num)).const_mul 2).comp upperVertical_tendsto_cubic_punctured
  have hr := (hd.mul baseOutgoingConstant_residue_limit).comp upperVertical_tendsto_cubic_punctured
  have hevent : (fun t:ℝ=>2*((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((3:ℂ)^(3*((4/3:ℂ)+(t:ℂ)*Complex.I)-3)-1)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*baseOutgoingConstant ((4/3:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=opposite_zero_cross_identity (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : 2*translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=2*cuspConstantAverageResidue :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hevent
  exact mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) heq

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rationalComplex_conjugate (r:SL(2,ℤ)) (M:levelThree) :
    complexMatrix (levelThreeConjugate (rationalEmbedding r) M)*rationalComplex r=
      rationalComplex r*complexMatrix M := by
  rw [←integralComplexMatrix_levelThree,←integralComplexMatrix_levelThree]
  change integralComplexMatrix ((rationalEmbedding r)*(M:SL(2,Eis))*(rationalEmbedding r)⁻¹)*
    integralComplexMatrix (rationalEmbedding r)=
      integralComplexMatrix (rationalEmbedding r)*integralComplexMatrix (M:SL(2,Eis))
  rw [←map_mul,inv_mul_cancel_right,map_mul]

lemma hyperbolicEisenstein_rational_automorphy (r:SL(2,ℤ)) (M:levelThree)
    (s:ℂ) (hs:2<s.re) (w:HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex r • (complexMatrix M • w))=
      complexCharacter M*hyperbolicEisenstein s (rationalComplex r • w) := by
  rw [←mul_smul,←rationalComplex_conjugate,mul_smul,hyperbolicEisenstein_automorphy _ _ hs,
    complexCharacter_conjugate_rational]

lemma hyperbolicEisenstein_rational_periodic (r:SL(2,ℤ)) (a:Eis)
    (s:ℂ) (hs:2<s.re) (z:ℂ) (v:ℝ) (hv:0<v) :
    hyperbolicEisenstein s (rationalComplex r • upperPoint (z+3*eisEmbedding a) v hv)=
      hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv) := by
  have he : upperPoint (z+3*eisEmbedding a) v hv=complexMatrix (upperTranslation a) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (upperTranslation_section a z v hv).symm
  rw [he,hyperbolicEisenstein_rational_automorphy r _ s hs,complexCharacter_upperTranslation,one_mul]

lemma rationalComplex_unipotent_coe (t : ℤ) :
    (rationalComplex (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1,(t : ℂ);0,1] := by
  apply Matrix.ext
  intro i j
  change eisEmbedding ((Int.castRingHom Eis) ((!![1,t;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j)) = _
  fin_cases i <;> fin_cases j <;> simp

lemma rationalUnipotent_section (t:ℤ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (rationalUnipotent t)*upperSection z v hv=upperSection (z+t) v hv := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, rationalComplex_unipotent_coe]
  change (!![1,(t : ℂ);0,1] *
    !![(Real.sqrt v : ℂ),z/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹] :
      Matrix (Fin 2) (Fin 2) ℂ) =
    !![(Real.sqrt v : ℂ),(z+t)/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

lemma rationalComplex_T_pow_upper (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (ModularGroup.T^n) • upperPoint z v hv=upperPoint (z+n) v hv := by
  change ((rationalComplex (ModularGroup.T^n)*upperSection z v hv):HyperbolicSpace)=
    (upperSection (z+(n:ℂ)) v hv:HyperbolicSpace)
  have he:=congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (rationalUnipotent_section (n:ℤ) z v hv)
  simpa only [rationalUnipotent_nat,Int.cast_natCast] using he

lemma cuspFourierPhase_zero (w:HyperbolicSpace) : cuspFourierPhase (0:Eis) w=1 := by
  simp [cuspFourierPhase,cuspFrequency]

lemma kernelCuspFourier_zero (F:KernelQuotientL2) :
    kernelCuspFourier (0:Eis) F=kernelCuspStripAverage F := by
  rw [kernelCuspFourier_integral,kernelCuspStripAverage_hyperbolic]
  simp only [cuspFourierPhase_zero,mul_one]

end

open CubicKubota

lemma sourceComplexMatrix_rationalLift (r:SL(2,ℤ)) :
    sourceComplexMatrix (rationalLift r)=rationalComplex r := rfl

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def cubicMellinMixture (s : ℂ) (t x : ℝ) : ℂ :=
  (t:ℂ)^(-(2:ℂ)/3)*Complex.exp (-(t:ℂ))*
    ((x:ℂ)^((s-1/3)-1)*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2))

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

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

open scoped BigOperators Classical

namespace ShortDraftCRT

section
variable {R : Type*} [CommRing R]

theorem exists_fixed_completion (M c r a d0 : R)
    (hfixed : c∣a*d0-1) (hr : IsCoprime r (M*c)) (ha : IsCoprime a r) :
    ∃b d : R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 := by
  have hcr : IsCoprime c r := hr.of_mul_right_right.symm
  obtain ⟨u,v,huv⟩ := hr
  obtain ⟨x,y,hxy⟩ := ha
  let d : R := d0*u*r+x*v*(M*c)
  have hd : M*c∣d-d0 := by
    refine ⟨v*(x-d0),?_⟩
    dsimp [d]
    linear_combination d0*huv
  have hdr : r∣d-x := by
    refine ⟨u*(d0-x),?_⟩
    dsimp [d]
    linear_combination x*huv
  have hcd : c∣a*d-1 := by
    have hdiff : c∣a*(d-d0) := dvd_mul_of_dvd_right
      ((dvd_mul_left c M).trans hd) a
    convert (preTransparency := .instances) dvd_add hdiff hfixed using 1 ; ring
  have hrd : r∣a*d-1 := by
    have hx : r∣a*x-1 := by
      refine ⟨-y,?_⟩
      linear_combination hxy
    have hdiff : r∣a*(d-x) := dvd_mul_of_dvd_right hdr a
    convert (preTransparency := .instances) dvd_add hdiff hx using 1 ; ring
  obtain ⟨b,hb⟩ := hcr.mul_dvd hcd hrd
  refine ⟨b,d,?_,hd⟩
  linear_combination hb

variable [IsDomain R]

theorem fixed_completion_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) : M∣b-b0 := by
  have hprod : M*c∣a*d-a0*d0 := by
    have h1 := dvd_mul_of_dvd_left ha d
    have h2 := dvd_mul_of_dvd_right hd a0
    convert (preTransparency := .instances) dvd_add h1 h2 using 1 ; ring
  have hcancel : M*c∣c*(b*r-b0*r0) := by
    convert (preTransparency := .instances) hprod using 1
    linear_combination -hdet+hdet0
  have hbr : M∣b*r-b0*r0 := by
    rw [mul_comm M c] at hcancel
    exact (mul_dvd_mul_iff_left hc).mp hcancel
  have hsub : M∣(b-b0)*r := by
    have hsmall := dvd_mul_of_dvd_right hrr b0
    convert (preTransparency := .instances) dvd_sub hbr hsmall using 1 ; ring
  exact hr.dvd_of_dvd_mul_right hsub

end

open scoped BigOperators Classical Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma quotient_eq_of_dvd_sub (M x y : R) (h : M ∣ x-y) :
    Ideal.Quotient.mk (Ideal.span {M}) x = Ideal.Quotient.mk (Ideal.span {M}) y := by
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

theorem fixed_completion_matrix_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) :
    (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) =
      (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) := by
  have hqa := quotient_eq_of_dvd_sub M a a0 ((dvd_mul_right M c).trans ha)
  have hqd := quotient_eq_of_dvd_sub M d d0 ((dvd_mul_right M c).trans hd)
  have hqb := quotient_eq_of_dvd_sub M b b0
    (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc hr hdet hdet0 ha hd hrr)
  have hqc : Ideal.Quotient.mk (Ideal.span {M}) (c*r) =
      Ideal.Quotient.mk (Ideal.span {M}) (c*r0) := by
    apply quotient_eq_of_dvd_sub
    simpa only [mul_sub] using dvd_mul_of_dvd_right hrr c
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply,] <;>
    assumption

theorem exists_fixed_matrix_completion (M c a0 r0 d0 b0 : R)
    (hc : c≠0) (hdet0 : a0*d0-b0*(c*r0)=1) :
    ∀a r : R, M*c∣a-a0 → M∣r-r0 → IsCoprime r (M*c) → IsCoprime a r →
      ∃b d : R, a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧
        (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) =
          (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  have hbase : c ∣ a0*d0-1 := by
    refine ⟨b0*r0,?_⟩
    linear_combination hdet0
  have hfixed : c ∣ a*d0-1 := by
    have hdiff := dvd_mul_of_dvd_left ((dvd_mul_left c M).trans ha) d0
    convert (preTransparency := .instances) dvd_add hdiff hbase using 1 ; ring
  obtain ⟨b,d,hdet,hd⟩ := exists_fixed_completion M c r a d0 hfixed hr har
  exact ⟨b,d,hdet,hd,fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr⟩

end ShortDraftCRT

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def conductorReduction (a b:Eis):
    (Eis⧸Ideal.span {a*b})→+*(Eis⧸Ideal.span {a}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))

lemma conductorReduction_surjective (a b:Eis):Function.Surjective (conductorReduction a b):=
  Ideal.Quotient.factor_surjective _

def quotientTrace (c:Eis) (hc:c≠0):AddChar (Eis⧸Ideal.span {c}) ℂ:=
  eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc

lemma quotientTrace_mk (c:Eis) (hc:c≠0) (x:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ x)=residueAdditive (3*x) c 1:=by
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring

def conductorFourier (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*x)

lemma conductorFourier_shift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h t:Eis):
    conductorFourier a b ha hb F h=
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))*
        conductorFourier a b ha hb F h:=by
  let q:Eis⧸Ideal.span {a*b}:=Ideal.Quotient.mk _ (a*t)
  have hq:conductorReduction a b q=0:=by
    change Ideal.Quotient.mk (Ideal.span {a}) (a*t)=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨t,rfl⟩)
  unfold conductorFourier
  conv_lhs => rw [←(Equiv.addRight q).tsum_eq]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  change F (conductorReduction a b (x+q))*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*(x+q))=_
  simp only [map_add,hq,add_zero,mul_add,AddChar.map_add_eq_mul]
  have he:Ideal.Quotient.mk (Ideal.span {a*b}) h*q=Ideal.Quotient.mk _ (h*a*t):=by
    dsimp [q]
    rw [←map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem conductorFourier_support (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis)
    (hF:conductorFourier a b ha hb F h≠0):b∣h:=by
  have hphase (t:Eis):
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))=1:=by
    apply mul_right_cancel₀ hF
    rw [one_mul,←conductorFourier_shift]
  have hz:Ideal.Quotient.mk (Ideal.span {a*b}) (h*a)=0:=by
    by_contra hn
    apply GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (a*b) (mul_ne_zero ha hb) hn
    ext x
    obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply,←map_mul,AddChar.one_apply,quotientTrace] using hphase t
  have hd:a*b∣h*a:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd':a*b∣a*h:=by simpa only [mul_comm h a] using hd
  exact (mul_dvd_mul_iff_left ha).mp hd'

lemma conductorReduction_kernel_card (a b:Eis) (ha:a≠0) (_hb:b≠0):
    Nat.card (conductorReduction a b).toAddMonoidHom.ker=Ideal.absNorm (Ideal.span {b}):=by
  have hc:=card_ring_eq_card_mul_kernel (conductorReduction a b)
    (conductorReduction_surjective a b)
  change Ideal.absNorm (Ideal.span {a*b})=
    Ideal.absNorm (Ideal.span {a})*Nat.card (conductorReduction a b).toAddMonoidHom.ker at hc
  conv_lhs at hc => rw [←Ideal.span_singleton_mul_span_singleton,map_mul]
  have hpos:0<Ideal.absNorm (Ideal.span {a}):=by
    apply Nat.pos_iff_ne_zero.mpr
    intro hz
    exact ha (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz))
  exact (Nat.eq_of_mul_eq_mul_left hpos hc).symm

theorem finite_tsum_conductor_pullback {R S:Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f:R→+S) (hf:Function.Surjective f) (F:S→ℂ):
    (∑'x:R,F (f x))=(Nat.card f.ker:ℂ)*∑'y:S,F y:=by
  let:Fintype R:=Fintype.ofFinite _
  let:Fintype S:=Fintype.ofFinite _
  let:Fintype f.ker:=Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,←Fintype.sum_fiberwise' f F]
  have hc (y:S):Fintype.card {x:R//f x=y}=Fintype.card f.ker:=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

lemma quotientTrace_conductor_scale (a b k:Eis) (ha:a≠0) (hb:b≠0)
    (x:Eis⧸Ideal.span {a*b}):
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (b*k)*x)=
      quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change quotientTrace (a*b) (mul_ne_zero ha hb)
    (Ideal.Quotient.mk _ (b*k)*Ideal.Quotient.mk _ d)=
    quotientTrace a ha (Ideal.Quotient.mk _ k*Ideal.Quotient.mk _ d)
  rw [←map_mul,←map_mul,quotientTrace_mk,quotientTrace_mk]
  simp only [residueAdditive,cuspFrequency,map_mul,map_one,map_ofNat]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  field_simp

theorem conductorFourier_lift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (k:Eis):
    conductorFourier a b ha hb F (b*k)=
      (Ideal.absNorm (Ideal.span {b}):ℂ)*
        ∑'x:Eis⧸Ideal.span {a},F x*quotientTrace a ha (Ideal.Quotient.mk _ k*x):=by
  let:Finite (Eis⧸Ideal.span {a*b}):=finite_quotient_span (mul_ne_zero ha hb)
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  unfold conductorFourier
  calc
    _=∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
        quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
      apply tsum_congr
      intro x
      rw [quotientTrace_conductor_scale a b k ha hb]
    _=_:=by
      have he:=finite_tsum_conductor_pullback (conductorReduction a b).toAddMonoidHom
        (conductorReduction_surjective a b)
        (fun y=>F y*quotientTrace a ha (Ideal.Quotient.mk _ k*y))
      rw [conductorReduction_kernel_card a b ha hb] at he
      exact he

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_pow_denominator (x p:Eis) (n:ℕ):
    symbol x (p^n)=(symbol x p)^n:=by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,symbol_mul_denominator,ih,pow_succ]

def primeCubicMulChar (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    MulChar (Eis⧸Ideal.span {p}) ℂ:=by
  letI:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  refine {toFun:=fun x=>eisEmbedding (symbol (GaussianShiftedPartition.representative p x) p)
          map_one':=?_,map_mul':=?_,map_nonunit':=?_}
  · have hd:p∣GaussianShiftedPartition.representative p 1-1:=by
      simpa only [map_one] using gaussRep_mk_congr p 1
    rw [symbol_congr hd,symbol_one_numerator p hprimary,map_one]
  · intro x y
    have hd:p∣GaussianShiftedPartition.representative p (x*y)-
        GaussianShiftedPartition.representative p x*GaussianShiftedPartition.representative p y:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      simp only [map_mul,GaussianShiftedPartition.representative_spec]
    rw [symbol_congr hd,symbol_mul_numerator _ _ p hprimary,map_mul]
  · intro x hx
    rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
      GaussianShiftedPartition.representative_spec,MulChar.map_nonunit _ hx,map_zero]

lemma primeCubicMulChar_mk (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (x:Eis):
    primeCubicMulChar p hp hprimary (Ideal.Quotient.mk _ x)=eisEmbedding (symbol x p):=by
  change eisEmbedding (symbol (GaussianShiftedPartition.representative p
    (Ideal.Quotient.mk _ x)) p)=_
  rw [symbol_congr (gaussRep_mk_congr p x)]

lemma quotientTrace_mk_product (c:Eis) (hc:c≠0) (h d:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ h*Ideal.Quotient.mk _ d)=
      residueAdditive (3*h) c d:=by
  rw [←map_mul,quotientTrace_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring

lemma conductorReduction_prime_power_unit (p:Eis) (n:ℕ)
    (x:Eis⧸Ideal.span {p*p^n}):
    IsUnit (conductorReduction p (p^n) x)↔IsUnit x:=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change IsUnit (Ideal.Quotient.mk (Ideal.span {p}) d)↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {p*p^n}) d)
  rw [isUnit_quotient_span_iff,isUnit_quotient_span_iff,←pow_succ',
    IsCoprime.pow_left_iff (Nat.succ_pos n)]

theorem cubicUnitGaussSum_prime_power_fourier (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum h (p^(n+1))=
      conductorFourier p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)
        (fun x=>(primeCubicMulChar p hp hprimary^(n+1)) x) h:=by
  let χ:=primeCubicMulChar p hp hprimary
  let f:(Eis⧸Ideal.span {p*p^n})→ℂ:=fun x=>
    (χ^(n+1)) (conductorReduction p (p^n) x)*
      quotientTrace (p*p^n) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hn
    have hn':¬IsUnit (conductorReduction p (p^n) x):=
      fun hh=>hn ((conductorReduction_prime_power_unit p n x).mp hh)
    exact hx (by dsimp [f];rw [MulChar.map_nonunit _ hn',zero_mul])
  rw [pow_succ']
  change cubicUnitGaussSum h (p*p^n)=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  let d:=GaussianShiftedPartition.representative (p*p^n) x.val
  have hd:Ideal.Quotient.mk (Ideal.span {p*p^n}) d=x.val:=
    GaussianShiftedPartition.representative_spec _ _
  change eisEmbedding (symbol d (p*p^n))*residueAdditive (3*h) (p*p^n) d=f x.val
  rw [←hd]
  dsimp [f]
  change _=(χ^(n+1)) (Ideal.Quotient.mk _ d)*_
  rw [MulChar.pow_apply' _ (Nat.succ_ne_zero n),primeCubicMulChar_mk,
    quotientTrace_mk_product,←pow_succ',cubicSymbol_pow_denominator,map_pow]

theorem cubicUnitGaussSum_prime_power_support (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis)
    (hne:cubicUnitGaussSum h (p^(n+1))≠0):p^n∣h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n h] at hne
  exact conductorFourier_support p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero) _ h hne

def primeCubicGauss (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {p},(primeCubicMulChar p hp hprimary^e) x*
    quotientTrace p hp.ne_zero (Ideal.Quotient.mk _ h*x)

theorem cubicUnitGaussSum_prime_power_lift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (p^n*h) (p^(n+1))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^n*primeCubicGauss p hp hprimary (n+1) h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n,
    conductorFourier_lift p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)]
  have hn:Ideal.absNorm (Ideal.span {p^n})=Ideal.absNorm (Ideal.span {p})^n:=by
    rw [←Ideal.span_singleton_pow,map_pow]
  rw [hn,Nat.cast_pow]
  rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_cube (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary^3=1:=by
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [MulChar.pow_apply' _ (by decide),primeCubicMulChar_mk,←map_pow,
      symbol_cube_of_isCoprime d p hprimary ((isUnit_quotient_span_iff p d).mp hx).symm,map_one]
    exact (MulChar.one_apply_coe hx.unit).symm
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_ne_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary≠1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  intro hchar
  apply cubicChar_ne_one (Ideal.span {p}) hg
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    have he:=congrArg (fun χ:MulChar (Eis⧸Ideal.span {p}) ℂ=>χ (Ideal.Quotient.mk _ d)) hchar
    rw [primeCubicMulChar_mk,symbol_prime p hp hprimary,primeValue_eq _ hg] at he
    have hoc:(1:MulChar (Eis⧸Ideal.span {p}) ℂ) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    have hoo:(1:MulChar (Eis⧸Ideal.span {p}) Eis) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    rw [hoo]
    apply eisEmbedding_injective
    simpa only [hoc,map_one] using he
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_order (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    orderOf (primeCubicMulChar p hp hprimary)=3:=by
  have hd:=orderOf_dvd_of_pow_eq_one (primeCubicMulChar_cube p hp hprimary)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1|h3
  · exact False.elim (primeCubicMulChar_ne_one p hp hprimary (orderOf_eq_one_iff.mp h1))
  · exact h3

lemma primeCubicMulChar_pow_eq_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ):
    primeCubicMulChar p hp hprimary^e=1↔3∣e:=by
  rw [←orderOf_dvd_iff_pow_eq_one,primeCubicMulChar_order]

lemma primeCubicGauss_mod_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ) (h:Eis):
    primeCubicGauss p hp hprimary e h=primeCubicGauss p hp hprimary (e%3) h:=by
  unfold primeCubicGauss
  have he:=pow_mod_orderOf (primeCubicMulChar p hp hprimary) e
  rw [primeCubicMulChar_order] at he
  rw [he]

lemma primeCubicGauss_eq_gaussSum (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) [Fintype (Eis⧸Ideal.span {p})]:
    primeCubicGauss p hp hprimary e h=
      gaussSum (primeCubicMulChar p hp hprimary^e)
        ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)):=by
  simp only [primeCubicGauss,tsum_fintype,gaussSum,AddChar.mulShift_apply]

theorem primeCubicGauss_of_dvd (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) (hph:p∣h):
    primeCubicGauss p hp hprimary e h=
      if 3∣e then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else 0:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  rw [primeCubicGauss_eq_gaussSum,hh,AddChar.mulShift_zero]
  split_ifs with he
  · rw [(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he,gaussSum_one_one,
      Nat.card_units,Nat.cast_sub (Nat.succ_le_of_lt Nat.card_pos),Nat.cast_one]
    rfl
  · exact gaussSum_one_right (fun hχ=>he ((primeCubicMulChar_pow_eq_one p hp hprimary e).mp hχ))

theorem primeCubicGauss_one_mul_two (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary 1 h*primeCubicGauss p hp hprimary 2 h=
      (Ideal.absNorm (Ideal.span {p}):ℂ):=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  have hψ:((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)).IsPrimitive:=
    AddChar.IsPrimitive.of_ne_one (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)
  have he:=gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (primeCubicMulChar_ne_one p hp hprimary) hψ
  rw [primeCubicMulChar_order] at he
  have hm:=MulChar.val_neg_one_eq_one_of_odd_order (by decide:Odd 3)
    (primeCubicMulChar_cube p hp hprimary)
  rw [hm,one_mul] at he
  change _=(Nat.card (Eis⧸Ideal.span {p}):ℂ)
  simpa only [primeCubicGauss_eq_gaussSum,pow_one,Nat.reduceSub,
    Nat.card_eq_fintype_card] using he

lemma primeCubicGauss_one_eq (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis):
    primeCubicGauss p hp hprimary 1 h=cubicUnitGaussSum h p:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary 0 h
  simpa only [pow_zero,one_mul,pow_one,Nat.zero_add] using he.symm

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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def residualCuspDecayRate : ℝ := Real.pi*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹/4

lemma residualCuspDecayRate_pos : 0< residualCuspDecayRate := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  unfold residualCuspDecayRate
  positivity

end CubicEisenstein

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix

section
variable {R : Type*} [CommRing R]

theorem exists_frequency_lift (N p h : R) (hcop : IsCoprime N p) :
    ∃k : R, N∣k ∧ p∣k-h := by
  obtain ⟨u,v,huv⟩ := hcop
  refine ⟨h*u*N,⟨h*u,by ring⟩,⟨-h*v,?_⟩⟩
  linear_combination h*huv

variable [IsDomain R]

end

variable {R : Type*} [CommRing R] [IsDomain R]

end ShortDraftCRT

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicUnitGaussSum_norm_le (h c:Eis) (hc:c≠0) (hp:lambda^2∣c-1):
    ‖cubicUnitGaussSum h c‖≤Ideal.absNorm (Ideal.span {c}):=by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Fintype (Eis⧸Ideal.span {c}):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue c):=Fintype.ofFinite _
  have hs (r:CubicUnitResidue c):
      ‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)‖=1:=by
    apply Complex.norm_eq_one_of_pow_eq_one (n:=3) _ (by decide)
    rw [←map_pow,symbol_cube_of_isCoprime _ c hp _ ,map_one]
    apply IsCoprime.symm
    apply (isUnit_quotient_span_iff c _).mp
    simpa only [GaussianShiftedPartition.representative_spec] using r.2
  rw [cubicUnitGaussSum,tsum_fintype]
  calc
    _≤∑r:CubicUnitResidue c,‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive (3*h) c (GaussianShiftedPartition.representative c r.val)‖:=norm_sum_le _ _
    _=(Fintype.card (CubicUnitResidue c):ℝ):=by
      simp only [norm_mul,hs,residueAdditive,breveE_norm,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _≤(Fintype.card (Eis⧸Ideal.span {c}):ℝ):=by
      exact_mod_cast Fintype.card_subtype_le (fun r=>IsUnit r)
    _=Ideal.absNorm (Ideal.span {c}):=by
      simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem unramifiedCubicGaussSeries_summable_norm (s:ℂ) (hs:2<s.re) (h:Eis):
    Summable (fun I:GoodIdeal=>‖(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)‖):=by
  have hs':1<(s-1).re:=by simp only [Complex.sub_re,Complex.one_re];linarith
  apply ((unramifiedNormWeight_summable_norm (s-1) hs').subtype
    (fun I:Ideal Eis=>primaryGenerator I≠0)).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro I
  dsimp only [Function.comp_def]
  simp only [unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast,
    unramifiedNormWeight_of_good s I.val I.2]
  have hg:=cubicUnitGaussSum_norm_le h (primaryGenerator I.val) I.2
    (primaryGenerator_spec I.val I.2).2
  rw [(primaryGenerator_spec I.val I.2).1] at hg
  nlinarith [norm_nonneg ((Ideal.absNorm I.val:ℂ)^(-s))]

abbrev PrimeDeletedIdeal (p:Eis):={I:GoodIdeal//¬(Ideal.span {p}:Ideal Eis)∣I.val}

def unramifiedPrimeDeletedSeries (p:Eis) (s:ℂ) (h:Eis):ℂ:=
  ∑'I:PrimeDeletedIdeal p,(Ideal.absNorm I.val.val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator I.val.val)

lemma primaryGenerator_pow (I:Ideal Eis) (n:ℕ):
    primaryGenerator (I ^n)=primaryGenerator I ^n:=
  map_pow primaryGeneratorHom I n

lemma gaussPrimeIdeal_prime (p:Eis) (hp:Prime p):Prime (Ideal.span {p}:Ideal Eis):=
  Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)

def gaussPrimeFactorMap (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (q:ℕ×PrimeDeletedIdeal p):GoodIdeal:=
  ⟨(Ideal.span {p})^q.1*q.2.val.val,by
    rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) q.2.val.2⟩

lemma gaussPrimeFactorMap_bijective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    Function.Bijective (gaussPrimeFactorMap p hp hprimary):=by
  let P:Ideal Eis:=Ideal.span {p}
  have hP:Prime P:=gaussPrimeIdeal_prime p hp
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh:P^n*I.val.val=P^m*J.val.val:=congrArg Subtype.val heq
    have hn:n=m:=by
      have hm:=congrArg (multiplicity P) hh
      rw [prime_power_remainder_multiplicity hP I.2,
        prime_power_remainder_multiplicity hP J.2] at hm
      exact hm
    subst m
    have hIJ:I=J:=Subtype.ext (Subtype.ext
      (mul_left_cancel₀ (pow_ne_zero n hP.ne_zero) hh))
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hP
      (primaryGenerator_ne_zero_ideal I.val I.2)).exists_eq_pow_mul_and_not_dvd
    have hgood:primaryGenerator J≠0:=by
      intro hzero
      apply I.2
      rw [hJ,primaryGenerator_mul,hzero,mul_zero]
    refine ⟨(multiplicity P I.val,⟨⟨J,hgood⟩,hnot⟩),?_⟩
    exact Subtype.ext hJ.symm

def gaussPrimeFactorEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    ℕ×PrimeDeletedIdeal p≃GoodIdeal:=
  Equiv.ofBijective (gaussPrimeFactorMap p hp hprimary)
    (gaussPrimeFactorMap_bijective p hp hprimary)

lemma primeDeleted_generator_coprime (p:Eis) (hp:Prime p) (I:PrimeDeletedIdeal p):
    IsCoprime p (primaryGenerator I.val.val):=by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  apply I.2
  rw [Ideal.dvd_iff_le,←(primaryGenerator_spec I.val.val I.val.2).1,
    Ideal.span_singleton_le_span_singleton]
  exact hd

lemma primary_pow_congruence (p:Eis) (hprimary:lambda^2∣p-1) (n:ℕ):
    lambda^2∣p^n-1:=by
  simpa only [one_pow] using hprimary.trans (sub_dvd_pow_sub_pow p 1 n)

lemma gaussPrimeFactor_term (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (s:ℂ) (h:Eis) (n:ℕ) (I:PrimeDeletedIdeal p):
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val)=
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
      ((Ideal.absNorm I.val.val:ℂ)^(-s)*cubicUnitGaussSum (h*p^n) (primaryGenerator I.val.val)):=by
  change (Ideal.absNorm ((Ideal.span {p})^n*I.val.val):ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator ((Ideal.span {p})^n*I.val.val))=_
  rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary,
    cubicUnitGaussSum_coprime_product h (p^n) (primaryGenerator I.val.val)
      (pow_ne_zero _ hp.ne_zero) I.val.2 (primary_pow_congruence p hprimary n)
      (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).pow_left,
    map_mul,map_pow,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have he:((Ideal.absNorm (Ideal.span {p})^n:ℕ):ℂ)^(-s)=
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n:=by
    rw [Nat.cast_pow,←Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]
  rw [he]
  ring

theorem unramifiedCubicGaussSeries_prime_reindex (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis):
    unramifiedCubicGaussSeries s h=
      ∑'n:ℕ,((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
        unramifiedPrimeDeletedSeries p s (h*p^n):=by
  have hsum:Summable (fun I:GoodIdeal=>(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)):=
    (unramifiedCubicGaussSeries_summable_norm s hs h).of_norm
  have hpull:=(gaussPrimeFactorEquiv p hp hprimary).summable_iff.mpr hsum
  change Summable (fun q:ℕ×PrimeDeletedIdeal p=>
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val)) at hpull
  rw [unramifiedCubicGaussSeries,←(gaussPrimeFactorEquiv p hp hprimary).tsum_eq]
  change (∑'q:ℕ×PrimeDeletedIdeal p,
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val))=_
  rw [hpull.tsum_prod]
  apply tsum_congr
  intro n
  change (∑'I:PrimeDeletedIdeal p,(Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val))=_
  simp_rw [gaussPrimeFactor_term p hp hprimary s h n]
  exact tsum_mul_left

lemma unramifiedPrimeDeletedSeries_cube_shift (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis):
    unramifiedPrimeDeletedSeries p s (h*p^3)=unramifiedPrimeDeletedSeries p s h:=by
  apply tsum_congr
  intro I
  congr 1
  exact cubicUnitGaussSum_cube_shift h _ p I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).symm

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
open scoped BigOperators Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

def cuspSpatialInput (q : ℝ × ℂ) : SpatialCoordinates := ![q.2.re,q.2.im,q.1]
def cuspSpatialOutput (p : SpatialCoordinates) : ℝ × ℂ := (p 2,spatialHorizontal p)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ninth_trace_character_period (c x : Eis) :
    ShortDraftTrace.breveE ((eisEmbedding c/(9*eisLam))*(9*eisEmbedding x))=1 := by
  have he : (eisEmbedding c/(9*eisLam))*(9*eisEmbedding x)=eisEmbedding (c*x)/eisLam := by
    rw [map_mul]
    ring
  rw [he,breveE_embedding_div_traceLambda]

lemma ramifiedSource_scaled_periodic10 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction omega (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction omega (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift10,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift10*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift10,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (omega-1) x
  rw [hp,one_mul]

lemma ramifiedSource_scaled_periodic19 (v : ℝ) (hv : 0<v) (x : Eis) (z : ℂ) :
    ramifiedSourceFunction (omega^2) (upperPoint (3*(z+3*eisEmbedding x)) v hv)=
      ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding x)=3*z+3*eisEmbedding (3*x) := by
    rw [map_mul,map_ofNat]
    ring
  rw [he,ramifiedSourceFunction_upper_shift19,show eisEmbedding (3*x)=3*eisEmbedding x by rw [map_mul,map_ofNat]]
  have hp : ShortDraftTrace.breveE (ramifiedShift19*(3*(3*eisEmbedding x)))=1 := by
    simpa only [ramifiedShift19,show (3:ℂ)*(3*eisEmbedding x)=9*eisEmbedding x by ring] using
      ninth_trace_character_period (-2-omega) x
  rw [hp,one_mul]

lemma periodic_integral_zero_of_eigen_translation (f : ℂ→ℂ)
    (hf : ∀x:Eis,∀z,f (z+3*eisEmbedding x)=f z) (b c : ℂ)
    (hc : c≠1) (he : ∀z,f (b+z)=c*f z) :
    (∫z in periodDomain,f z)=0 := by
  have hi := period_integral_translation f hf b
  simp_rw [he] at hi
  rw [integral_const_mul] at hi
  have hzero : (c-1)*(∫z in periodDomain,f z)=0 := by linear_combination hi
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hc)

theorem ramifiedSource_zero_mode10 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction omega (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic10 v hv) 1 (eisEmbedding omega)
  · exact fun h => omega_primitive.ne_one (by decide) (eisEmbedding_injective (by simpa using h))
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift10,ramifiedShift10_period]
    norm_num [cubicExp]

theorem ramifiedSource_zero_mode19 (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,ramifiedSourceFunction (omega^2) (upperPoint (3*z) v hv))=0 := by
  apply periodic_integral_zero_of_eigen_translation _
    (ramifiedSource_scaled_periodic19 v hv) 1 (eisEmbedding (omega^2))
  · intro h
    have he : omega^2=(1:Eis) := eisEmbedding_injective (by simpa using h)
    have hpoly := ramified_omega_relation
    rw [he] at hpoly
    have hw : omega=(-2:Eis) := by linear_combination hpoly
    rw [hw] at he
    norm_num at he
  · intro z
    have he : 3*(1+z)=3*z+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 0) := by
      norm_num [ActualEisensteinCoordinates.eval]
      ring
    rw [he,ramifiedSourceFunction_upper_shift19,ramifiedShift19_period]
    norm_num [cubicExp]

end

open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

abbrev UnitLowerData := Σa:PrimaryLower,{d:PrimaryLower//IsCoprime a.val d.val}

def unitLowerToPrimitive (u : Eisˣ) (p : UnitLowerData) : PrimitiveRow := by
  refine ⟨![(u:Eis)*(p.1.val-p.2.val.val),p.2.val.val],?_,?_,p.2.val.2⟩
  · change IsCoprime ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val
    apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd p.2.val.val (p.1.val-p.2.val.val) p.1.val
      ⟨-1,by ring⟩).mpr
    exact p.2.2.symm
  · have hd : (3:Eis)∣p.1.val-p.2.val.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub p.1.2 p.2.val.2
    exact hd.mul_left (u:Eis)

lemma unitLowerToPrimitive_bijective (u : Eisˣ) :
    Function.Bijective (unitLowerToPrimitive u) := by
  constructor
  · rintro ⟨a,d,hd⟩ ⟨b,e,he⟩ h
    have hrow := congrArg Subtype.val h
    have hde : d=e := Subtype.ext (congrFun hrow 1)
    subst e
    have hab : a=b := by
      apply Subtype.ext
      have hh := congrFun hrow 0
      change (u:Eis)*(a.val-d.val)=(u:Eis)*(b.val-d.val) at hh
      have hcancel := u.isUnit.mul_left_cancel hh
      linear_combination hcancel
    subst b
    rfl
  · intro r
    let d : PrimaryLower := ⟨r.val 1,r.2.2.2⟩
    let a : PrimaryLower := ⟨(↑u⁻¹:Eis)*r.val 0+r.val 1,by
      have hc := r.2.2.1.mul_left (↑u⁻¹:Eis)
      have hh := dvd_add hc r.2.2.2
      convert (preTransparency := .instances) hh using 1 ;ring⟩
    have hcop : IsCoprime a.val d.val := by
      apply IsCoprime.symm
      apply (isCoprime_right_congr_of_dvd d.val a.val ((↑u⁻¹:Eis)*r.val 0)
        ⟨1,by dsimp [a,d];ring⟩).mpr
      exact (isCoprime_mul_unit_left_right u⁻¹.isUnit _ _).mpr r.2.1.symm
    refine ⟨⟨a,d,hcop⟩,Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change (u:Eis)*((↑u⁻¹:Eis)*r.val 0+r.val 1-r.val 1)=r.val 0
      rw [add_sub_cancel_right,←mul_assoc]
      simp
    · rfl

def unitLowerEquiv (u : Eisˣ) : UnitLowerData≃PrimitiveRow :=
  Equiv.ofBijective _ (unitLowerToPrimitive_bijective u)

lemma rowOperator_lowerCusp (t : Eis) (v : Fin 2→ℂ) :
    rowOperator (integralComplexMatrix (lowerCuspMatrix t)) v=
      ![v 0+eisEmbedding t*v 1,v 1] := by
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,integralComplexMatrix_apply]
  fin_cases i <;>
    simp [lowerCuspMatrix,mul_comm]

lemma unitLower_row_phase (u : Eisˣ) (p : UnitLowerData) :
    (cosetCharacter (primitiveRowEquiv.symm (unitLowerEquiv u p)))⁻¹=
      eisEmbedding (symbol (u:Eis) p.2.val.val)*
        eisEmbedding (symbol p.2.val.val p.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val)=_
  have hh : symbol ((u:Eis)*(p.1.val-p.2.val.val)) p.2.val.val=
      symbol ((u:Eis)*p.1.val) p.2.val.val := by
    exact symbol_congr ⟨-(u:Eis),by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.val),
    symbol_reciprocity p.1.val p.2.val.val (primaryLower_ne_zero p.1)
      (primaryLower_ne_zero p.2.val) (primaryLower_primary p.1)
        (primaryLower_primary p.2.val),map_mul]

def unitLowerTerm (u : Eisˣ) (z : ℂ) (v : ℝ) (s : ℂ) (a d : Eis) : ℂ :=
  (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s

lemma unitLower_summand (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (p : UnitLowerData) :
    summand (integralComplexMatrix (lowerCuspMatrix (u:Eis))*upperSection z v hv) s
      (primitiveRowEquiv.symm (unitLowerEquiv u p))=
      unitLowerTerm u z v s p.1.val p.2.val.val := by
  let r : Fin 2→ℂ := ![eisEmbedding ((u:Eis)*p.1.val),eisEmbedding p.2.val.val]
  have hr : rowOperator (integralComplexMatrix (lowerCuspMatrix (u:Eis)))
      (embeddedRow (primitiveRowEquiv.symm (unitLowerEquiv u p)))=r := by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [unitLowerEquiv, Equiv.ofBijective_apply, unitLowerToPrimitive, r, map_mul, map_sub, mul_sub]
  have hr0 : r≠0 := by
    intro hh
    have he := congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.val) he
  have hp := heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,unitLower_row_phase]
  change _=(eisEmbedding (symbol (u:Eis) p.2.val.val)*eisEmbedding (symbol p.2.val.val p.1.val))*
    ((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi : ((v/heightDenominator z v r:ℝ):ℂ)=
      (((heightDenominator z v r/v:ℝ):ℂ))⁻¹ := by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

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

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ramifiedTraceLambda : Eis := 1+2*omega

lemma ramifiedEmbedding_traceLambda : eisEmbedding ramifiedTraceLambda=eisLam := by
  change eisEmbedding (1+2*omega)=1+2*EisensteinEmbedding.omega3
  rw [map_add,map_one,map_mul,map_ofNat,eisEmbedding_omega_actual]

lemma primary_add_three (a r : Eis) (ha : lambda^2∣a-1) :
    lambda^2∣a+3*r-1 := by
  have h3 : (3:Eis)∣a-1 := three_dvd_lambda_sq.trans ha
  exact lambda_sq_dvd_three.trans (by
    convert (preTransparency := .instances) dvd_add h3 (dvd_mul_right (3:Eis) r) using 1 ;ring)

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def ninthCuspFrequency (h : Eis) : ℂ := cuspFrequency h/3

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma cuspTransition_dilate (A : ℝ) (hA : A≠0) :
    cuspTransition A (2*A)=fun v => cuspTransition 1 2 (v/A) := by
  funext v
  unfold cuspTransition
  congr 1
  field_simp

lemma cuspTransition_dilate_deriv (A v : ℝ) (hA : A≠0) :
    deriv (cuspTransition A (2*A)) v=deriv (cuspTransition 1 2) (v/A)/A := by
  rw [cuspTransition_dilate A hA]
  have hd := (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)
  simpa [Function.comp_def,id_eq,div_eq_mul_inv] using hd.deriv

lemma cuspTransition_dilate_second (A v : ℝ) (hA : A≠0) :
    deriv (deriv (cuspTransition A (2*A))) v=
      deriv (deriv (cuspTransition 1 2)) (v/A)/A^2 := by
  have he : deriv (cuspTransition A (2*A))=
      fun x => deriv (cuspTransition 1 2) (x/A)/A := by
    funext x
    exact cuspTransition_dilate_deriv A x hA
  rw [he]
  have hc := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have hd := (((hc.differentiable (by simp) (v/A)).hasDerivAt).comp v
    ((hasDerivAt_id v).div_const A)).div_const A
  simp only [Function.comp_def,id_eq] at hd
  convert (preTransparency := .instances) hd.deriv using 1; field_simp

def cuspBaseDefectFactor (s : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^2*(deriv (deriv (cuspTransition 1 2)) x:ℝ)+
    (2*s-1)*(x:ℂ)*(deriv (cuspTransition 1 2) x:ℝ)

lemma cuspBaseDefectFactor_continuous (s : ℂ) : Continuous (cuspBaseDefectFactor s) := by
  have h1 := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff 1 2)).2
  have h2 := (contDiff_infty_iff_deriv.mp h1).2
  unfold cuspBaseDefectFactor
  exact ((Complex.continuous_ofReal.pow 2).mul (Complex.continuous_ofReal.comp h2.continuous)).add
    ((continuous_const.mul Complex.continuous_ofReal).mul (Complex.continuous_ofReal.comp h1.continuous))

lemma cuspBaseDefectFactor_compact (s : ℂ) : HasCompactSupport (cuspBaseDefectFactor s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 2))
  intro x hx
  by_contra hn
  have hout : x<1 ∨ 2<x := by simpa only [Set.mem_Icc,not_and_or,not_le] using hn
  obtain ⟨h1,h2⟩ := cuspTransition_derivatives 1 2 x (by norm_num) hout
  exact hx (by simp [cuspBaseDefectFactor,h1,h2])

lemma cuspSeedDefectProfile_dilate (A v : ℝ) (hA : A≠0) (s : ℂ) :
    cuspSeedDefectProfile A (2*A) s v=
      positiveHeightPower s v*cuspBaseDefectFactor s (v/A) := by
  rw [cuspSeedDefectProfile,cuspTransition_dilate_deriv A v hA,cuspTransition_dilate_second A v hA]
  unfold cuspBaseDefectFactor
  push_cast
  field_simp

theorem cuspSeedDefectProfile_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀v : ℝ,
      ‖cuspSeedDefectProfile A (2*A) (4/3) v‖≤C*A^2 := by
  obtain ⟨B,hB⟩ := (cuspBaseDefectFactor_compact (4/3)).exists_bound_of_continuous
    (cuspBaseDefectFactor_continuous (4/3))
  let C := max B 0
  have hC : 0≤C := le_max_right _ _
  have hbound (x : ℝ) : ‖cuspBaseDefectFactor (4/3) x‖≤C := (hB x).trans (le_max_left _ _)
  refine ⟨4*C,by positivity,fun A hA v => ?_⟩
  have hApos : 0<A := lt_of_lt_of_le zero_lt_one hA
  by_cases hv : v∈Set.Icc A (2*A)
  · have hv1 : 1≤v := hA.trans hv.1
    have hvpos : 0<v := hApos.trans_le hv.1
    have hp : ‖positiveHeightPower (4/3) v‖≤v^2 := by
      rw [positiveHeightPower_eq_cpow _ _ hvpos,Complex.norm_cpow_eq_rpow_re_of_pos hvpos]
      norm_num
      have hh := Real.rpow_le_rpow_of_exponent_le hv1 (show (4/3:ℝ)≤2 by norm_num)
      simpa using hh
    rw [cuspSeedDefectProfile_dilate A v hApos.ne',norm_mul]
    have hm := mul_le_mul hp (hbound (v/A)) (norm_nonneg _) (sq_nonneg v)
    calc
      _ ≤ v^2*C := hm
      _ ≤ (2*A)^2*C := mul_le_mul_of_nonneg_right (sq_le_sq₀ hvpos.le (by positivity) |>.mpr hv.2) hC
      _ = (4*C)*A^2 := by ring
  · have hout : v<A ∨ 2*A<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    rw [cuspSeedDefectProfile_zero A (2*A) (4/3) v (by linarith) hout,norm_zero]
    positivity

theorem smoothCuspSeedDefect_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2 := by
  obtain ⟨C,hC,hbound⟩ := cuspSeedDefectProfile_dilate_bound
  exact ⟨C,hC,fun A hA w => cuspCutoffCorrection_norm_le _ _ (by positivity) (hbound A hA) w⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

lemma movingDefect_product_bound
    (f : KernelQuotient→ℂ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) (q : KernelQuotient) :
    ‖f q‖*‖kernelQuotientDefect A (2*A) (4/3) q‖≤K*C/A := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change ‖f (integralOrbitProjection globalKubotaKernel w)‖*
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤_
    have hApos : 0<A := zero_lt_one.trans hA
    by_cases hz : smoothCuspSeedDefect A (2*A) (4/3) w=0
    · rw [hz,norm_zero,mul_zero]
      positivity
    obtain ⟨r,hr,hr'⟩ := smoothCuspSeedDefect_support A (2*A) (4/3) (by linarith) w hz
    have hheight : 0<cosetHeight r w := hApos.trans_le hr
    have hf : ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/A^3 := by
      apply (hdec w r (hA.trans_le hr)).trans
      apply div_le_div_of_nonneg_left hK (pow_pos hApos 3)
      exact pow_le_pow_left₀ hApos.le hr 3
    calc
      _ ≤ (K/A^3)*(C*A^2) := mul_le_mul hf (hbound A hA.le w) (norm_nonneg _) (by positivity)
      _ = K*C/A := by field_simp

lemma movingDefect_inner_bound
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) :
    ‖inner ℂ F (kernelL2Defect A (2*A) (by linarith) (by linarith) (4/3))‖≤
      (K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ := by
  rw [L2.inner_def]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hrep,kernelL2Defect_ae_eq A (2*A) (by linarith) (by linarith) (4/3)] with q hf hd
  rw [hf,hd,RCLike.inner_apply,norm_mul]
  simpa only [starRingEnd_apply,norm_star,mul_comm] using
    movingDefect_product_bound f K C hK hC hdec hbound A hA q

theorem cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3) :
    inner ℂ F cubicEisensteinResidue=0 := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_dilate_bound
  let B : ℝ := (3/2)*(K*C)*(integralQuotientVolume globalKubotaKernel).real Set.univ
  have hB : 0≤B := by dsimp [B]; positivity
  have hb (A : ℝ) (hA : 1<A) : ‖inner ℂ F cubicEisensteinResidue‖≤B/A := by
    have he : cubicEisensteinResidue=
        kernelEisensteinResidueVector A (2*A) (by linarith) (by linarith) :=
      kernelEisensteinResidueVector_cutoff_independent 2 3 A (2*A)
        (by norm_num) (by norm_num) hA (by linarith)
    rw [he,kernelEisensteinResidueVector_pairing,norm_mul]
    norm_num
    calc
      _ ≤ (3/2)*((K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ) :=
        mul_le_mul_of_nonneg_left (movingDefect_inner_bound F f hrep K C hK hC hdec hbound A hA) (by norm_num)
      _ = B/A := by dsimp [B]; ring
    exact hF
  apply norm_eq_zero.mp
  by_contra hn
  have hnpos : 0<‖inner ℂ F cubicEisensteinResidue‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let A := B/‖inner ℂ F cubicEisensteinResidue‖+2
  have hA : 1<A := by
    have hh := div_nonneg hB hnpos.le
    dsimp [A]
    linarith
  have hh := (le_div_iff₀ (zero_lt_one.trans hA)).mp (hb A hA)
  have he : ‖inner ℂ F cubicEisensteinResidue‖*A=B+2*‖inner ℂ F cubicEisensteinResidue‖ := by
    dsimp [A]
    field_simp

  rw [he] at hh
  linarith

lemma coset_decay_of_cusp_chart_decay
    (f : KernelQuotient→ℂ) (K : ℝ)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3 := by
  intro w r
  induction r using Quotient.inductionOn with
  | _ M =>
    intro hr
    change 1<cosetHeight (cosetOf M) w at hr
    change _≤K/(cosetHeight (cosetOf M) w)^3
    rw [cosetHeight_cosetOf] at hr ⊢
    obtain ⟨z,v,hv,hpt⟩ := upperPoint_surjective (complexMatrix M • w)
    have hh : hyperbolicHeight (complexMatrix M • w)=v := by
      rw [←hpt,hyperbolicHeight_upperPoint]
    rw [hh] at hr ⊢
    have he : complexMatrix M⁻¹ • upperPoint z v hv=w := by
      rw [hpt,map_inv,inv_smul_smul]
    simpa only [he] using hdec M⁻¹ z v hv hr

theorem cubicEisensteinResidue_orthogonal_of_cusp_chart_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    inner ℂ F cubicEisensteinResidue=0 :=
  cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay F hF f hrep K hK
    (coset_decay_of_cusp_chart_decay f K hdec)

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota

section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_congruent_cusp_completion (A : SL(2,Eis)) (x y : Eis)
    (hxy : IsCoprime x y) (hx : (3:Eis)∣x-A 0 0) (hy : (3:Eis)∣y-A 1 0) :
    ∃ N : SL(2,Eis), N 0 0=x ∧ N 1 0=y ∧ N*A⁻¹∈levelThree := by
  obtain ⟨u,v,huv⟩ := hxy
  let t := u*A 0 1+v*A 1 1
  let N : SL(2,Eis) := ⟨!![x,-v+x*t;y,u+y*t],by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hr : (3:Eis)∣1+y*A 0 1-x*A 1 1 := by
    convert (preTransparency := .instances) dvd_sub (dvd_mul_of_dvd_left hy (A 0 1))
      (dvd_mul_of_dvd_left hx (A 1 1)) using 1 ; linear_combination -hd
  have hmod : ∀i j,(3:Eis)∣N i j-A i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hx
    · have hv := dvd_mul_of_dvd_left hr (-v)
      convert (preTransparency := .instances) hv using 1 ; dsimp [N,t] ; linear_combination (A 0 1)*huv
    · exact hy
    · have hu := dvd_mul_of_dvd_left hr u
      convert (preTransparency := .instances) hu using 1 ; dsimp [N,t] ; linear_combination (A 1 1)*huv
  have hq : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) N =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) A := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (hmod i j))
  refine ⟨N,rfl,rfl,?_⟩
  change Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1
  rw [map_mul,map_inv,hq,mul_inv_cancel]

lemma cusp_completion_upper_factor (A N : SL(2,Eis)) (q g x y : Eis)
    (hx : A 0 0+3*q*A 1 0=g*N 0 0) (hy : x*A 1 0=g*N 1 0)
    (hg : g≠0) (hdet : x=g*y) :
    N.val⁻¹ * (!![1,3*q;0,x] * A.val) =
      !![g,(N.val⁻¹ * (!![1,3*q;0,x] * A.val)) 0 1;0,y] := by
  have hNdet : N 0 0*N 1 1-N 0 1*N 1 0=1 := by
    simpa only [Matrix.det_fin_two] using N.property
  have hAdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hinv : N.val⁻¹ = !![N 1 1,-N 0 1;-N 1 0,N 0 0] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    linear_combination g*hNdet
  · rfl
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    ring
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    apply mul_left_cancel₀ hg
    linear_combination x*hAdet-x*(A 1 1)*hx+(A 0 1+3*q*A 1 1)*hy+hdet

end

open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma bounded_power_factor (p a : Eis) (n : ℕ) :
    ∃ j≤n,∃b,a=p^j*b ∧ (j=n ∨ ¬p∣b) := by
  induction n generalizing a with
  | zero => exact ⟨0,le_rfl,a,by simp,Or.inl rfl⟩
  | succ n ih =>
    by_cases h:p∣a
    · obtain ⟨a',rfl⟩:=h
      obtain ⟨j,hj,b,hab,hb⟩:=ih a'
      refine ⟨j+1,Nat.succ_le_succ hj,b,?_,?_⟩
      · rw [hab,pow_succ]
        ring
      · exact hb.elim (fun h=>Or.inl (congrArg (fun k=>k+1) h)) Or.inr
    · exact ⟨0,Nat.zero_le _,a,by simp,Or.inr h⟩

lemma cube_average_cusp_reduction (A : SL(2,Eis)) (p q : Eis)
    (hp : Prime p) (hprimary : lambda^2∣p-1) :
    ∃ j≤3,∃N : SL(2,Eis),
      A 0 0+3*q*A 1 0=p^j*N 0 0 ∧
      p^3*A 1 0=p^j*N 1 0 ∧ N*A⁻¹∈levelThree ∧
      (j=3 ∨ ¬p∣N 0 0) ∧
      N.val⁻¹*(!![1,3*q;0,p^3]*A.val)=
        !![p^j,(N.val⁻¹*(!![1,3*q;0,p^3]*A.val)) 0 1;0,p^(3-j)] := by
  let a:=A 0 0+3*q*A 1 0
  have haC:IsCoprime a (A 1 0) := by
    have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
      simpa only [Matrix.det_fin_two] using A.property
    refine ⟨A 1 1,-(A 0 1+3*q*A 1 1),?_⟩
    dsimp [a]
    linear_combination hd
  obtain ⟨j,hj,b,hab,hb⟩:=bounded_power_factor p a 3
  have hbC:IsCoprime b (A 1 0) := by
    rw [hab] at haC
    exact haC.of_mul_left_right
  have hbY:IsCoprime b (p^(3-j)*A 1 0) := by
    rcases hb with h | h
    · simpa [h] using hbC
    · exact ((hp.coprime_iff_not_dvd.mpr h).symm.pow_right).mul_right hbC
  have hpow (k:ℕ):(3:Eis)∣p^k-1 := by
    have hd:(3:Eis)∣p-1:=CubicJacobiGlobal.three_dvd_primary_sub_one p hprimary
    simpa using hd.trans (sub_dvd_pow_sub_pow p 1 k)
  have hbA:(3:Eis)∣b-A 0 0 := by
    have h1:(3:Eis)∣a-A 0 0:=by
      refine ⟨q*A 1 0,?_⟩
      dsimp [a]
      ring
    have h2:(3:Eis)∣a-b:=by
      rw [hab]
      convert (preTransparency := .instances) dvd_mul_of_dvd_left (hpow j) b using 1 ; ring
    convert (preTransparency := .instances) dvd_sub h1 h2 using 1 ; ring
  have hyC:(3:Eis)∣p^(3-j)*A 1 0-A 1 0 := by
    convert (preTransparency := .instances) dvd_mul_of_dvd_left (hpow (3-j)) (A 1 0) using 1 ; ring
  obtain ⟨N,hN0,hN1,hNA⟩:=exists_congruent_cusp_completion A b (p^(3-j)*A 1 0) hbY hbA hyC
  have hA:a=p^j*N 0 0:=by rw [hN0];exact hab
  have hC:p^3*A 1 0=p^j*N 1 0:=by
    rw [hN1,←mul_assoc,←pow_add,Nat.add_sub_of_le hj]
  refine ⟨j,hj,N,hA,hC,hNA,?_,?_⟩
  · simpa [hN0] using hb
  · exact cusp_completion_upper_factor A N q (p^j) (p^3) (p^(3-j))
      hA hC (pow_ne_zero j hp.ne_zero) (by rw [←pow_add,Nat.add_sub_of_le hj])

end CubicKubota

end

end OAI
end


