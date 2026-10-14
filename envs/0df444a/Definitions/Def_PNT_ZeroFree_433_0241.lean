-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0241
-- name    : PNT_ZeroFree_433_0241
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:21:13.689102+00:00
-- url     : https://prove2.me/theorems/32ccc7fa-bee6-4bdd-9a1d-537b77fecdaa
-- title:
--   Zero-free region foundations: Cusp.ResiduesModThree [0241]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Cusp.ResiduesModThree
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduesModThree.lean#L85-L633

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0076
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0138_parallel1
import Definitions.Def_PNT_ZeroFree_433_0185_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel2
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Cusp/ResiduesModThree.lean
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

open scoped Classical MatrixGroups

namespace EisensteinCuspModThree


open scoped Classical MatrixGroups Matrix

local notation "O" => ActualEisensteinCubic.O
local notation "ζ" => ActualEisensteinCubic.omega
open CubicKubota CubicEisenstein


def cuspRepresentative (j : Fin 3) : SL(2,ActualEisensteinCubic.O) := lowerCuspMatrix (cuspParameter j)


def columnRepresentative (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) : SL(2,ActualEisensteinCubic.O) :=
  rationalEmbedding r*cuspRepresentative j*unitDiagonal (unitRepresentative u)

lemma columnRepresentative_entry (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) (i : Fin 2) :
    columnRepresentative r j u i 0=
      ((r i 0:ActualEisensteinCubic.O)+(r i 1:ActualEisensteinCubic.O)*cuspParameter j)*(unitRepresentative u:ActualEisensteinCubic.O) := by
  change (((r : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom O) *
    !![1, 0; cuspParameter j, 1]) *
    !![(unitRepresentative u : O), 0; 0, (↑(unitRepresentative u)⁻¹ : O)]) i 0 = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma columnRepresentative_top_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 0 0)=columnTop (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl

lemma columnRepresentative_bottom_residue (r : SL(2,ℤ)) (j : Fin 3) (u : Fin 2 × Fin 3) :
    residue (columnRepresentative r j u 1 0)=columnBottom (rationalReductionThree r) j u := by
  rw [columnRepresentative_entry,residue_mul,residue_add,residue_intCast,
    residue_mul_intCast,cuspParameter_residue,unitRepresentative_residue]
  rfl


theorem three_cusp_decomposition (M : SL(2,ActualEisensteinCubic.O)) :
    ∃G : levelTwo, ∃j : Fin 3, ∃T : SL(2,ActualEisensteinCubic.O),
      T 1 0=0 ∧ IsUnit (T 0 0) ∧ IsUnit (T 1 1) ∧
        M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T := by
  obtain ⟨g,j,u,ht,hb⟩ := primitive_column_three_cusps _ _ (first_column_primitive M)
  obtain ⟨r,hr⟩ := rationalReductionThree_surjective g
  let B := columnRepresentative r j u
  have hB0 : residue (B 0 0)=residue (M 0 0) := by
    dsimp only [B]
    rw [columnRepresentative_top_residue,hr]
    exact ht
  have hB1 : residue (B 1 0)=residue (M 1 0) := by
    dsimp only [B]
    rw [columnRepresentative_bottom_residue,hr]
    exact hb
  have hxy : IsCoprime (M 0 0) (M 1 0) := by
    refine ⟨M 1 1,-M 0 1,?_⟩
    have hd := M.property
    rw [Matrix.det_fin_two] at hd
    linear_combination hd
  obtain ⟨N,hN0,hN1,hNB⟩ := exists_congruent_cusp_completion B (M 0 0) (M 1 0) hxy
    (residue_eq_implies_three_dvd hB0.symm) (residue_eq_implies_three_dvd hB1.symm)
  let G : levelTwo := ⟨(N*B⁻¹)*rationalEmbedding r,⟨⟨N*B⁻¹,hNB⟩,r,rfl⟩⟩
  let T : SL(2,ActualEisensteinCubic.O) := unitDiagonal (unitRepresentative u)*(N⁻¹*M)
  have hT : T 1 0=0 := by
    have hz := same_column_quotient_lower_zero M N hN0 hN1
    change (∑k : Fin 2,(unitDiagonal (unitRepresentative u)) 1 k*(N⁻¹*M) k 0)=0
    rw [Fin.sum_univ_two]
    change 0*(N⁻¹*M) 0 0+(↑(unitRepresentative u)⁻¹:ActualEisensteinCubic.O)*(N⁻¹*M) 1 0=0
    rw [hz]
    ring
  have hdet : T 0 0*T 1 1=1 := by
    have hd := T.property
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using hd
  refine ⟨G,j,T,hT,?_,?_,?_⟩
  · exact IsUnit.of_mul_eq_one _ hdet
  · exact IsUnit.of_mul_eq_one _ (show T 1 1*T 0 0=1 by simpa only [mul_comm] using hdet)
  · dsimp [G,T,B,columnRepresentative]
    group

end EisensteinCuspModThree

namespace CubicEisenstein
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O
abbrev PrimaryCoprimeDenominator (a : PrimaryLower) := {d:PrimaryLower//IsCoprime a.val d.val}

def primaryDenominatorFromCoprime (a : PrimaryLower) (x : CoprimeElement a.val) :
    PrimaryCoprimeDenominator a := by
  refine ⟨⟨a.val+3*x.val,?_⟩,?_⟩
  · convert! dvd_add a.2 (dvd_mul_right (3:Eis) x.val) using 1 ;ring
  · apply (isCoprime_right_congr_of_dvd a.val (a.val+3*x.val) (3*x.val) ⟨1,by ring⟩).mpr
    exact (primary_coprime_three a.val (primaryLower_primary a)).mul_right x.2

lemma primaryDenominatorFromCoprime_bijective (a : PrimaryLower) :
    Function.Bijective (primaryDenominatorFromCoprime a) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg (fun d : PrimaryCoprimeDenominator a => d.val.val) h
    change a.val+3*x.val=a.val+3*y.val at he
    exact mul_left_cancel₀ (by norm_num : (3:Eis)≠0) (add_left_cancel he)
  · intro d
    have hdiv : (3:Eis)∣d.val.val-a.val := by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub d.val.2 a.2
    obtain ⟨x,hx⟩ := hdiv
    have hd : d.val.val=a.val+3*x := by linear_combination hx
    have hcop : IsCoprime a.val x := by
      have hc : IsCoprime a.val (3*x) :=
        (isCoprime_right_congr_of_dvd a.val d.val.val (3*x) ⟨1,by rw [hd];ring⟩).mp d.2
      exact hc.of_isCoprime_of_dvd_right (dvd_mul_left x 3)
    refine ⟨⟨x,hcop⟩,Subtype.ext (Subtype.ext ?_)⟩
    exact hd.symm

def primaryDenominatorEquiv (a : PrimaryLower) : CoprimeElement a.val≃PrimaryCoprimeDenominator a :=
  Equiv.ofBijective _ (primaryDenominatorFromCoprime_bijective a)

def unitLowerIntegral (u : Eisˣ) (v : ℝ) (s freq : ℂ) (a d : Eis) : ℂ :=
  ∫z in periodDomain,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z)

lemma hasSum_unitLowerIntegrals (u : Eisˣ) (v : ℝ) (hv : 0<v) (s freq : ℂ) (hs : 2<s.re) :
    HasSum (fun p : UnitLowerData => unitLowerIntegral u v s freq p.1.val p.2.val.val)
      (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
        upperSection z v hv) s*ShortDraftTrace.breveE (-freq*z)) := by
  have hh := ((unitLowerEquiv u).trans primitiveRowEquiv.symm).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))) v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only [Equiv.trans_apply,unitLowerIntegral]
    rw [unitLower_summand])

lemma unitLowerTerm_eq_shifted (u : Eisˣ) (z : ℂ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (a d : Eis) (ha : a≠0) :
    unitLowerTerm u z v s a d=
      (eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a)*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s))*
          shiftedHeightKernel v s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) z := by
  rw [unitLowerTerm,rowHeight_eq_shiftedHeightKernel z v hv s ((u:Eis)*a) d (mul_ne_zero u.ne_zero ha),
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  ring

lemma unitLowerTerm_integrable (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s : ℂ) (hs : 1<s.re) (a d : Eis) (ha : a≠0) :
    Integrable (fun z=>unitLowerTerm u z v s a d) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma unitLowerTerm_fourier_integral (u : Eisˣ) (v : ℝ) (hv : 0<v)
    (s freq : ℂ) (a d : Eis) (ha : a≠0) :
    (∫z:ℂ,unitLowerTerm u z v s a d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding a‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) d)*eisEmbedding (symbol d a))*
            ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding ((u:Eis)*a))) := by
  simp_rw [unitLowerTerm_eq_shifted u _ v hv s a d ha,mul_assoc]
  rw [integral_const_mul,integral_const_mul,integral_const_mul,
    traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding ((u:Eis)*a)) freq]
  ring_nf

lemma unitLowerGaussTerm_factor (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))=
    (ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
      (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)))*
        (eisEmbedding (symbol r a)*residueAdditive (3*k) a r) := by
  have hchar : eisEmbedding (symbol (u:Eis) (a+3*r))=
      eisEmbedding (symbol (u:Eis) a)*ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3) := by
    rw [hu]
    exact symbol_omega_pow_primary_shift j a r hprimary
  have hs : symbol (a+3*r) a=symbol (3*r) a := symbol_congr ⟨1,by ring⟩
  rw [hchar,hs,symbol_mul_numerator _ _ _ hprimary,map_mul]
  have hp := unitLower_phase_identity h a r k u j ha hk
  calc
    _ = (eisEmbedding (symbol (u:Eis) a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol r a))*
      (ShortDraftTrace.breveE ((j:ℂ)*eisEmbedding r/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a))) := by ring
    _ = _ := by rw [hp];ring

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitLowerTwistedCoefficient_add (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda) :
    (eisEmbedding (symbol (u:Eis) (a+3*(r+a*n)))*eisEmbedding (symbol (a+3*(r+a*n)) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*(r+a*n))/eisEmbedding ((u:Eis)*a))=
    (eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)) := by
  rw [unitLowerGaussTerm_factor h a k (r+a*n) u j ha hprimary hu hk,
    unitLowerGaussTerm_factor h a k r u j ha hprimary hu hk]
  rw [symbol_congr (show a∣r+a*n-r from ⟨n,by ring⟩),
    residueAdditive_three_congr k a (r+a*n) r ha ⟨n,by ring⟩]

lemma unitLowerTerm_weighted_translate (h a k r n : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (z : ℂ) (v : ℝ) (s : ℂ) :
    unitLowerTerm u z v s a (a+3*(r+a*((u:Eis)*n)))*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=
    unitLowerTerm u (z+3*eisEmbedding n) v s a (a+3*r)*
      ShortDraftTrace.breveE (-ninthCuspFrequency h*(z+3*eisEmbedding n)) := by
  let c1 := eisEmbedding (symbol (u:Eis) (a+3*(r+a*((u:Eis)*n))))*
    eisEmbedding (symbol (a+3*(r+a*((u:Eis)*n))) a)
  let c0 := eisEmbedding (symbol (u:Eis) (a+3*r))*eisEmbedding (symbol (a+3*r) a)
  let B := ninthCuspFrequency h*eisEmbedding (a+3*r)/eisEmbedding ((u:Eis)*a)
  let Q := ninthCuspFrequency h*(3*eisEmbedding n)
  have hc0 := eisEmbedding_ne_zero (mul_ne_zero u.ne_zero ha)
  have harg : ninthCuspFrequency h*eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a)=B+Q := by
    dsimp [B,Q]
    simp only [map_add,map_mul,map_ofNat]
    field_simp [eisEmbedding_ne_zero u.ne_zero,eisEmbedding_ne_zero ha]
    ;ring
  have hcoef := unitLowerTwistedCoefficient_add h a k r ((u:Eis)*n) u j ha hprimary hu hk
  change c1*ShortDraftTrace.breveE (ninthCuspFrequency h*
    eisEmbedding (a+3*(r+a*((u:Eis)*n)))/eisEmbedding ((u:Eis)*a))=c0*ShortDraftTrace.breveE B at hcoef
  rw [harg,AddChar.map_add_eq_mul] at hcoef
  have heB : ShortDraftTrace.breveE B≠0 := Complex.exp_ne_zero _
  have heQ : ShortDraftTrace.breveE Q≠0 := Complex.exp_ne_zero _
  have hmult : c1*ShortDraftTrace.breveE Q=c0 := by
    apply mul_right_cancel₀ heB
    calc
      _ = c1*(ShortDraftTrace.breveE B*ShortDraftTrace.breveE Q) := by ring
      _ = _ := hcoef
  have hsolve : c1=c0*ShortDraftTrace.breveE (-Q) := by
    rw [AddChar.map_neg_eq_inv]
    calc
      c1=c1*(ShortDraftTrace.breveE Q*(ShortDraftTrace.breveE Q)⁻¹) := by rw [mul_inv_cancel₀ heQ,mul_one]
      _ = (c1*ShortDraftTrace.breveE Q)*(ShortDraftTrace.breveE Q)⁻¹ := by ring
      _ = _ := by rw [hmult]
  have hrow : eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))=
      eisEmbedding ((u:Eis)*a)*(z+3*eisEmbedding n)+eisEmbedding (a+3*r) := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  change c1*((v/(‖eisEmbedding ((u:Eis)*a)*z+eisEmbedding (a+3*(r+a*((u:Eis)*n)))‖^2+
    ‖eisEmbedding ((u:Eis)*a)‖^2*v^2):ℝ):ℂ)^s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z)=_
  rw [hsolve,hrow]
  unfold unitLowerTerm
  have hphase : -ninthCuspFrequency h*(z+3*eisEmbedding n)=(-Q)+(-ninthCuspFrequency h*z) := by
    dsimp [Q]
    ring
  rw [hphase,AddChar.map_add_eq_mul]
  dsimp only [c0]
  ring

lemma unitLowerIntegral_sum_translate (h a k r : Eis) (u : Eisˣ) (j : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hu : (u:Eis)=omega^j)
    (hk : 3*k=h*(↑u⁻¹:Eis)+(j:Eis)*a*ramifiedTraceLambda)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 1<s.re) :
    (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a (a+3*(r+a*((u:Eis)*n))))=
      ∫z:ℂ,unitLowerTerm u z v s a (a+3*r)*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z=>unitLowerTerm u z v s a (a+3*r))
    (unitLowerTerm_integrable u v hv s hs a (a+3*r) ha) (ninthCuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => unitLowerTerm_weighted_translate h a k r n u j ha hprimary hu hk z v s)


end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma unitDenominator_integral_formula (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j) (a : PrimaryLower)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∑'d:PrimaryCoprimeDenominator a,unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val := by
  obtain ⟨k,hk⟩ := unitCuspFrequency_lift h a.val u j (primaryLower_primary a) hh
  let e := (cubicResidueElementEquiv a.val (primaryLower_ne_zero a)).trans (primaryDenominatorEquiv a)
  have hf : Summable (fun d:PrimaryCoprimeDenominator a =>
      unitLowerIntegral u v s (ninthCuspFrequency h) a.val d.val.val) :=
    (hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs).summable.sigma_factor a
  have hsum := e.summable_iff.mpr hf
  change Summable (fun q:CubicUnitResidue a.val×Eis =>
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2))) at hsum
  rw [←e.tsum_eq]
  change (∑'q:CubicUnitResidue a.val×Eis,
    unitLowerIntegral u v s (ninthCuspFrequency h) a.val
      (a.val+3*(GaussianShiftedPartition.representative a.val q.1.val+a.val*q.2)))=_
  rw [hsum.tsum_prod]
  have hinner (r:CubicUnitResidue a.val) :
      (∑'n:Eis,unitLowerIntegral u v s (ninthCuspFrequency h) a.val
        (a.val+3*(GaussianShiftedPartition.representative a.val r.val+a.val*n)))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*
          ((eisEmbedding (symbol (u:Eis) (a.val+3*GaussianShiftedPartition.representative a.val r.val))*
            eisEmbedding (symbol (a.val+3*GaussianShiftedPartition.representative a.val r.val) a.val))*
              ShortDraftTrace.breveE (ninthCuspFrequency h*
                eisEmbedding (a.val+3*GaussianShiftedPartition.representative a.val r.val)/eisEmbedding ((u:Eis)*a.val))) := by
    rw [←(unitCuspIndexEquiv u).tsum_eq]
    exact (unitLowerIntegral_sum_translate h a.val k
      (GaussianShiftedPartition.representative a.val r.val) u j (primaryLower_ne_zero a)
      (primaryLower_primary a) hu hk v hv s (by linarith)).trans
        (unitLowerTerm_fourier_integral u v hv s (ninthCuspFrequency h) a.val _ (primaryLower_ne_zero a))
  simp_rw [hinner]
  exact tsum_mul_left

theorem unitLowerEisenstein_fourier (u : Eisˣ) (j : ℕ) (hu : (u:Eis)=omega^j)
    (h : Eis) (hh : UnitCuspFrequency h u j)
    (v : ℝ) (hv : 0<v) (s : ℂ) (hs : 2<s.re) :
    (∫z in periodDomain,eisenstein (integralComplexMatrix (lowerCuspMatrix (u:Eis))*
      upperSection z v hv) s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (u:Eis))*
          unramifiedCubicGaussSeries s (3*h*(u:Eis)) := by
  have hhSum := hasSum_unitLowerIntegrals u v hv s (ninthCuspFrequency h) hs
  rw [←hhSum.tsum_eq,hhSum.summable.tsum_sigma]
  simp_rw [unitDenominator_integral_formula u j hu h hh _ v hv s hs]
  have he : (∑'a:PrimaryLower,
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*
        ((‖eisEmbedding a.val‖^2:ℝ):ℂ)^(-s)*unitLowerGauss h u a.val)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (ninthCuspFrequency h*v))*unitCuspArithmeticSeries s h u := by
    rw [unitCuspArithmeticSeries,←tsum_mul_left]
    apply tsum_congr
    intro a
    ring
  rw [he,unitCuspArithmeticSeries_eq s h u j hu hh]
  ring

end CubicEisenstein


end

end OAI

end


