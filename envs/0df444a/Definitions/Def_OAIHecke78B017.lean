-- Prove2me | Definitions.Def_OAIHecke78B017
-- name    : OAIHecke78B017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:41:53.428748+00:00
-- url     : https://prove2.me/theorems/0802ecd3-311c-4a60-9638-5357ed172467
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 18 of 29
-- statement:
--   Definitions bundle 18 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B016` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Reciprocity.RamifiedCuspPhases`, `Descent.SecondCanonicalSplit`, `Descent.SecondAssignedSource`, `Descent.SecondSquarefree`, `Descent.SecondParentLists`, `Detector.PrimePower`, `Detector.CongruenceScalar`, `Detector.LiftedFourier`, `Detector.PhysicalFourier`, `Detector.LocalSeries`, `Detector.LocalSummation`, `Detector.PrincipalEulerIdentity`, `Detector.SourceLocal`, `Detector.SourceExclusions`, `Hecke.LogarithmicInput`, `Detector.FiniteProductX`, `Detector.GaussianDensityBudget`, `Detector.GaussianRemoteRows`, `Detector.HighRowsSeries`, `Detector.HighRowsFamilies`, `Detector.HighRowsPrime`, `Detector.HighRowsClosed`, `Detector.HighRowsCentralRamified`, `Hecke.PrimeDyadicContour`, `Hecke.PrimeRay`, `Moments.DivisorRawEnergy`, `Moments.RetainedEnergy`, `Moments.WholeSlotDeletion`, `Moments.PrimeSlot`, `Moments.DetectorDictionary`, `Moments.DetectorDictionaryUniformLog`, `Dictionary.InverseUniformScale`, `Moments.ActiveAllocation`, `Moments.ReflectionMass`, `Moments.ScaleSupremum`, `Moments.SupportedZeroEnergy`, `Hecke.PrimeRow`, `Moments.SecondSourcePowerDescent`, `Energy.FirstGaussianCoefficients`, `Hecke.DetectorWitnessRows`, `Hecke.DetectorInverseFiberCount`, `Inversion.InitialPhysicalSlots`, `PrimeRows.DetectorZeros`, `PrimeRows.RowPartition`, `Moments.DetectorDictionarySource`, `Moments.NaturalFixedRaySourceCharacters`, `Reflection.Cofactor`, `Reflection.Frozen`, `Reflection.FrozenSplit`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B016

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B017

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Reciprocity.RamifiedCuspPhases
  Descent.SecondCanonicalSplit
  Descent.SecondAssignedSource
  Descent.SecondSquarefree
  Descent.SecondParentLists
  Detector.PrimePower
  Detector.CongruenceScalar
  Detector.LiftedFourier
  Detector.PhysicalFourier
  Detector.LocalSeries
  Detector.LocalSummation
  Detector.PrincipalEulerIdentity
  Detector.SourceLocal
  Detector.SourceExclusions
  Hecke.LogarithmicInput
  Detector.FiniteProductX
  Detector.GaussianDensityBudget
  Detector.GaussianRemoteRows
  Detector.HighRowsSeries
  Detector.HighRowsFamilies
  Detector.HighRowsPrime
  Detector.HighRowsClosed
  Detector.HighRowsCentralRamified
  Hecke.PrimeDyadicContour
  Hecke.PrimeRay
  Moments.DivisorRawEnergy
  Moments.RetainedEnergy
  Moments.WholeSlotDeletion
  Moments.PrimeSlot
  Moments.DetectorDictionary
  Moments.DetectorDictionaryUniformLog
  Dictionary.InverseUniformScale
  Moments.ActiveAllocation
  Moments.ReflectionMass
  Moments.ScaleSupremum
  Moments.SupportedZeroEnergy
  Hecke.PrimeRow
  Moments.SecondSourcePowerDescent
  Energy.FirstGaussianCoefficients
  Hecke.DetectorWitnessRows
  Hecke.DetectorInverseFiberCount
  Inversion.InitialPhysicalSlots
  PrimeRows.DetectorZeros
  PrimeRows.RowPartition
  Moments.DetectorDictionarySource
  Moments.NaturalFixedRaySourceCharacters
  Reflection.Cofactor
  Reflection.Frozen
  Reflection.FrozenSplit
-/

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

namespace CubicKubota

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def actualCubeCuspPhaseSum (A:levelTwo) (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (w:Fin 4→ℂ) : ℂ :=
  ∑' r:Eis⧸Ideal.span {p^3},
    let d:=actualCubeCuspData (A:SL(2,Eis)) p (GaussianShiftedPartition.representative (p^3) r) hp hprimary
    w d.exponent * complexCharacter ⟨d.matrix*(A:SL(2,Eis))⁻¹,d.congruent⟩

theorem actualCubeCuspPhaseSum_coprime (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  let e:=cubeResidueStrataEquiv p hp hprimary
  let a:=cubeCuspAffineEquiv p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0) hprimary hC
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  let phi (s:CubeResidueStrata p):=w s.1*cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) s.1 s.2
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=
        phi (e.symm (a r)) := by
    rw [(d r).comparison_phase A hp hprimary hA hC]
    change phi ((d r).stratum hp.ne_zero)=phi (e.symm (a r))
    apply congrArg phi
    apply e.injective
    rw [e.apply_symm_apply]
    change cubeResidueStratumMap p ((d r).stratum hp.ne_zero)=a r
    rw [(d r).stratum_map hp.ne_zero]
    rw [←cubeCuspAffineEquiv_mk p ((A:SL(2,Eis)) 0 0) ((A:SL(2,Eis)) 1 0)
      (GaussianShiftedPartition.representative (p^3) r) hprimary hC,
      GaussianShiftedPartition.representative_spec]
  let (j:Fin 4):Finite (Eis⧸Ideal.span {p^(3-j.val)}) :=
    finite_quotient_span (pow_ne_zero _ hp.ne_zero)
  let (j:Fin 4):Finite (CubicUnitResidue (p^(3-j.val))) := inferInstance
  have hphi:Summable phi:=Summable.of_finite
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r,phi (e.symm (a r)) := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = ∑' r,phi (e.symm r) := a.tsum_eq (fun r => phi (e.symm r))
    _ = ∑' s,phi s := e.symm.tsum_eq phi
    _ = ∑j:Fin 4,w j*∑' b:CubicUnitResidue (p^(3-j.val)),cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b := by
      rw [hphi.tsum_sigma,tsum_fintype]
      apply Finset.sum_congr rfl
      intro j hj
      exact tsum_mul_left (f := fun b:CubicUnitResidue (p^(3-j.val)) =>
        cubeStratumSymbol p ((A:SL(2,Eis)) 1 0) j b) (a := w j)
    _ = _ := cubeStrata_weighted_sum p ((A:SL(2,Eis)) 1 0) hp hprimary hC w

theorem actualCubeCuspPhaseSum_dvd (A:levelTwo) (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hC:p∣((A:SL(2,Eis)) 1 0)) (w:Fin 4→ℂ) :
    actualCubeCuspPhaseSum A p hp hprimary w =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^3 := by
  let d (r:Eis⧸Ideal.span {p^3}):=actualCubeCuspData (A:SL(2,Eis)) p
    (GaussianShiftedPartition.representative (p^3) r) hp hprimary
  have hpoint (r:Eis⧸Ideal.span {p^3}):
      w (d r).exponent*complexCharacter ⟨(d r).matrix*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0 := by
    have hj:((d r).exponent:ℕ)=0:=cube_exponent_zero_of_lower_divisible
      (A:SL(2,Eis)) (d r).matrix p _ _ hp hC (d r).first
    have hj':(d r).exponent=0:=Fin.ext hj
    let N:levelTwo:=⟨(d r).matrix,comparison_levelTwo A (d r).matrix (d r).congruent⟩
    have hphase:=levelTwo_cube_zero_phase A N p
      (GaussianShiftedPartition.representative (p^3) r) hprimary hA
      (comparison_primary _ _ (d r).congruent hA)
      (by simpa only [hj,pow_zero,one_mul] using (d r).first)
      (by simpa only [hj,Nat.sub_zero] using (d r).lower_eq hp.ne_zero)
      (d r).congruent
    change w (d r).exponent*complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,(d r).congruent⟩=w 0
    rw [hphase,hj',mul_one]
  calc
    actualCubeCuspPhaseSum A p hp hprimary w = ∑' r:Eis⧸Ideal.span {p^3},w 0 := by
      unfold actualCubeCuspPhaseSum
      exact tsum_congr hpoint
    _ = (Nat.card (Eis⧸Ideal.span {p^3}):ℂ)*w 0 := by
      rw [tsum_const,nsmul_eq_mul]
    _ = _ := by
      change (Ideal.absNorm (Ideal.span {p^3}):ℂ)*w 0 = _
      rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
      ring

end CubicKubota

namespace CubicEisenstein

section
open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma onceCusp_trace_lambda : ramifiedTraceLambda*ramLambda=3*omega^2 := by
  unfold ramifiedTraceLambda
  linear_combination -ramified_omega_relation

lemma onceCusp_lambda_dvd_trace : ramLambda∣ramifiedTraceLambda := by
  refine ⟨-omega,?_⟩
  unfold ramifiedTraceLambda
  linear_combination ramified_omega_relation

def onceCuspScale (u:Eisˣ) : Eis := (u:Eis)*ramifiedTraceLambda

def onceCuspComplement (u:Eisˣ) : Eis := -(↑u⁻¹:Eis)*ramifiedTraceLambda

lemma onceCusp_scale_complement (u:Eisˣ) : onceCuspScale u*onceCuspComplement u=3 := by
  calc
    _ = -((u:Eis)*(↑u⁻¹:Eis))*ramifiedTraceLambda^2 := by
      unfold onceCuspScale onceCuspComplement; ring
    _ = 3 := by simp [ramifiedTraceLambda_square]

lemma onceCusp_scale_ne_zero (u:Eisˣ) : onceCuspScale u≠0 := by
  intro h
  have hh:=onceCusp_scale_complement u
  rw [h,zero_mul] at hh
  exact (by norm_num : (0:Eis)≠3) hh

lemma onceCusp_scale_lambda (u:Eisˣ) : (3:Eis)∣onceCuspScale u*ramLambda := by
  refine ⟨(u:Eis)*omega^2,?_⟩
  simp only [onceCuspScale,mul_assoc,onceCusp_trace_lambda]
  ring

lemma onceCusp_complement_lambda (u:Eisˣ) : ramLambda∣onceCuspComplement u :=
  onceCusp_lambda_dvd_trace.mul_left _

lemma onceCusp_scale_coprime (u:Eisˣ) (d:PrimaryLower) : IsCoprime (onceCuspScale u) d.val := by
  apply (isCoprime_mul_unit_left_left u.isUnit _ _).mpr
  apply (primary_coprime_three d.val (primaryLower_primary d)).symm.of_isCoprime_of_dvd_left
  exact ⟨-ramifiedTraceLambda,by linear_combination ramifiedTraceLambda_square⟩

abbrev OnceRamifiedData := Fin 3×UnitLowerData

def onceRamifiedToPrimitive (u:Eisˣ) (p:OnceRamifiedData) : PrimitiveRow := by
  let b:=omega^p.1.val*p.2.1.val
  let d:=p.2.2.val.val
  refine ⟨![onceCuspScale u*(b-d),d],?_,?_,p.2.2.val.2⟩
  · change IsCoprime (onceCuspScale u*(b-d)) d
    apply (onceCusp_scale_coprime u p.2.2.val).mul_left
    apply IsCoprime.symm
    apply (isCoprime_right_congr_of_dvd d (b-d) b ⟨-1,by ring⟩).mpr
    exact ((isCoprime_mul_unit_left_left ((omega_primitive.isUnit (by decide)).pow _) _ _).mpr
      p.2.2.2).symm
  · change (3:Eis)∣onceCuspScale u*(b-d)
    have hb:ramLambda∣b-1:=(halfPrimaryFromAssociate (p.1,p.2.1)).2
    have hd:ramLambda∣d-1:=halfPrimary_lambda_dvd_three.trans p.2.2.val.2
    have hbd:ramLambda∣b-d:=by
      simpa only [sub_sub_sub_cancel_right] using dvd_sub hb hd
    obtain ⟨k,hk⟩:=hbd
    rw [hk,←mul_assoc]
    exact (onceCusp_scale_lambda u).mul_right k

lemma onceRamifiedToPrimitive_bijective (u:Eisˣ) :
    Function.Bijective (onceRamifiedToPrimitive u) := by
  constructor
  · rintro ⟨j,a,d,had⟩ ⟨k,b,e,hbe⟩ h
    have hrow:=congrArg Subtype.val h
    have hde:d=e:=Subtype.ext (congrFun hrow 1)
    subst e
    have he:=congrFun hrow 0
    change onceCuspScale u*(omega^j.val*a.val-d.val)=
      onceCuspScale u*(omega^k.val*b.val-d.val) at he
    have hsub:=mul_left_cancel₀ (onceCusp_scale_ne_zero u) he
    have hassoc:halfPrimaryFromAssociate (j,a)=halfPrimaryFromAssociate (k,b):=by
      apply Subtype.ext
      change omega^j.val*a.val=omega^k.val*b.val
      linear_combination hsub
    have hp:=halfPrimaryFromAssociate_injective hassoc
    have hj:j=k:=congrArg Prod.fst hp
    have hab:a=b:=congrArg Prod.snd hp
    subst k
    subst b
    rfl
  · intro r
    obtain ⟨k,hk⟩:=r.2.2.1
    let d:PrimaryLower:=⟨r.val 1,r.2.2.2⟩
    let b:HalfPrimary:=⟨onceCuspComplement u*k+d.val,by
      have hh:=dvd_add ((onceCusp_complement_lambda u).mul_right k)
        (halfPrimary_lambda_dvd_three.trans d.2)
      convert (preTransparency := .instances) hh using 1 ;ring⟩
    let p:=halfPrimaryAssociateEquiv.symm b
    have hp:omega^p.1.val*p.2.val=b.val:=
      congrArg Subtype.val (halfPrimaryAssociateEquiv.apply_symm_apply b)
    have hr:onceCuspScale u*(b.val-d.val)=r.val 0:=by
      change onceCuspScale u*(onceCuspComplement u*k+d.val-d.val)=_
      rw [add_sub_cancel_right,←mul_assoc,onceCusp_scale_complement,hk]
    have hcop:IsCoprime p.2.val d.val:=by
      have h0:IsCoprime (b.val-d.val) d.val:=
        (hr ▸ r.2.1).of_isCoprime_of_dvd_left (dvd_mul_left _ _)
      have hb:IsCoprime b.val d.val:=by
        apply IsCoprime.symm
        exact (isCoprime_right_congr_of_dvd d.val (b.val-d.val) b.val ⟨-1,by ring⟩).mp h0.symm
      rw [←hp] at hb
      exact hb.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
    refine ⟨(p.1,⟨p.2,d,hcop⟩),Subtype.ext ?_⟩
    funext i
    fin_cases i
    · change onceCuspScale u*(omega^p.1.val*p.2.val-d.val)=r.val 0
      rw [hp,hr]
    · rfl

def onceRamifiedEquiv (u:Eisˣ) : OnceRamifiedData≃PrimitiveRow :=
  Equiv.ofBijective _ (onceRamifiedToPrimitive_bijective u)

lemma onceRamified_row_phase (u:Eisˣ) (p:OnceRamifiedData) :
    (cosetCharacter (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))⁻¹=
      eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
        eisEmbedding (symbol p.2.2.val.val p.2.1.val) := by
  rw [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
  change eisEmbedding (symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val))
    p.2.2.val.val)=_
  have hh : symbol (onceCuspScale u*(omega^p.1.val*p.2.1.val-p.2.2.val.val)) p.2.2.val.val=
      symbol ((onceCuspScale u*omega^p.1.val)*p.2.1.val) p.2.2.val.val :=
    symbol_congr ⟨-onceCuspScale u,by ring⟩
  rw [hh,symbol_mul_numerator _ _ _ (primaryLower_primary p.2.2.val),
    symbol_reciprocity p.2.1.val p.2.2.val.val (primaryLower_ne_zero p.2.1)
      (primaryLower_ne_zero p.2.2.val) (primaryLower_primary p.2.1)
        (primaryLower_primary p.2.2.val),map_mul]

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def diagonalPrimitiveMap (u:Eisˣ) (v:PrimitiveRow) : PrimitiveRow :=
  ⟨![(u:Eis)^2*v.val 0,v.val 1],by
    refine ⟨?_,?_,v.2.2.2⟩
    · exact (isCoprime_mul_unit_left_left (u.isUnit.pow 2) _ _).mpr v.2.1
    · exact v.2.2.1.mul_left _⟩

def diagonalPrimitiveEquiv (u:Eisˣ) : PrimitiveRow≃PrimitiveRow where
  toFun:=diagonalPrimitiveMap u
  invFun:=diagonalPrimitiveMap u⁻¹
  left_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (↑u⁻¹:Eis)^2*((u:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl
  right_inv v:=by
    apply Subtype.ext
    funext i
    fin_cases i
    · change (u:Eis)^2*((↑u⁻¹:Eis)^2*v.val 0)=v.val 0
      rw [←mul_assoc,←mul_pow]
      simp
    · rfl

lemma rowOperator_unitCuspDiagonal (u:Eisˣ) (v:PrimitiveRow) :
    rowOperator (integralComplexMatrix (unitCuspDiagonal u))
      (embeddedRow (primitiveRowEquiv.symm v))=
      eisEmbedding (↑u⁻¹:Eis) •
        embeddedRow (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  simp only [embeddedRow, Function.comp_def, primitiveRowEquiv_symm_row]
  rw [rowOperator_apply]
  funext i
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    integralComplexMatrix_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · change eisEmbedding (v.val 0) * eisEmbedding (u : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (0 : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding ((u : Eis) ^ 2 * v.val 0)
    simp only [map_zero, mul_zero, add_zero, map_mul, pow_two]
    have hu : eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis) = 1 := by
      rw [← map_mul]
      simp
    calc
      _ = (eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (u : Eis)) *
          (eisEmbedding (v.val 0) * eisEmbedding (u : Eis)) := by rw [hu, one_mul]
      _ = _ := by ring
  · change eisEmbedding (v.val 0) * eisEmbedding (0 : Eis) +
      eisEmbedding (v.val 1) * eisEmbedding (↑u⁻¹ : Eis) =
      eisEmbedding (↑u⁻¹ : Eis) * eisEmbedding (v.val 1)
    simp [mul_comm]

lemma rowEnergy_unit_smul (u:Eisˣ) (v:Fin 2→ℂ) :
    rowEnergy (eisEmbedding (u:Eis) • v)=rowEnergy v := by
  simp only [rowEnergy,Pi.smul_apply,smul_eq_mul,norm_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

lemma diagonal_ray_summand (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) (v:PrimitiveRow) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*g) s (primitiveRowEquiv.symm v)=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        summand g s (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)) := by
  have hphase : (cosetCharacter (primitiveRowEquiv.symm v))⁻¹=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        (cosetCharacter (primitiveRowEquiv.symm (diagonalPrimitiveEquiv u v)))⁻¹ := by
    simp only [inverse_cosetCharacter_eq_row_symbol,primitiveRowEquiv_symm_row]
    change eisEmbedding (symbol (v.val 0) (v.val 1))=
      eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
        eisEmbedding (symbol ((u:Eis)^2*v.val 0) (v.val 1))
    rw [←map_mul,←symbol_mul_numerator _ _ _ (lambda_sq_dvd_three.trans v.2.2.2)]
    congr 2
    rw [←mul_assoc,←mul_pow]
    simp
  rw [summand,←rowOperator_mul,rowOperator_unitCuspDiagonal,map_smul,rowEnergy_unit_smul,hphase,
    summand]
  ring

end

section
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def affineLowerTerm (q r:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:Eis) : ℂ :=
  (eisEmbedding (symbol r d)*eisEmbedding (symbol d a))*
    ((v/(‖eisEmbedding (q*a)*z+eisEmbedding d‖^2+
      ‖eisEmbedding (q*a)‖^2*v^2):ℝ):ℂ)^s

lemma affineLowerTerm_mul_ray (q r t:Eis) (z:ℂ) (v:ℝ) (s:ℂ) (a d:PrimaryLower) :
    eisEmbedding (symbol t d.val)*affineLowerTerm q r z v s a.val d.val=
      affineLowerTerm q (t*r) z v s a.val d.val := by
  rw [affineLowerTerm,affineLowerTerm,symbol_mul_numerator _ _ _ (primaryLower_primary d),
    map_mul eisEmbedding (symbol t d.val) (symbol r d.val)]
  ring

lemma onceRamified_summand (u:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u))*upperSection z v hv) s
      (primitiveRowEquiv.symm (onceRamifiedEquiv u p))=
      affineLowerTerm (onceCuspScale u*omega^p.1.val) (onceCuspScale u*omega^p.1.val)
        z v s p.2.1.val p.2.2.val.val := by
  let r:Fin 2→ℂ:=![eisEmbedding ((onceCuspScale u*omega^p.1.val)*p.2.1.val),
    eisEmbedding p.2.2.val.val]
  have hr:rowOperator (integralComplexMatrix (lowerCuspMatrix (onceCuspScale u)))
      (embeddedRow (primitiveRowEquiv.symm (onceRamifiedEquiv u p)))=r:=by
    rw [embeddedRow, primitiveRowEquiv_symm_row, rowOperator_lowerCusp]
    funext i
    fin_cases i <;>
      simp [onceRamifiedEquiv, Equiv.ofBijective_apply, onceRamifiedToPrimitive,
        r, map_mul, map_sub, mul_sub, mul_assoc]
  have hr0:r≠0:=by
    intro hh
    have he:=congrFun hh 1
    exact eisEmbedding_ne_zero (primaryLower_ne_zero p.2.2.val) he
  have hp:=heightDenominator_pos z v hv r hr0
  rw [summand,←rowOperator_mul,hr,rowEnergy_upperSection,onceRamified_row_phase]
  change _= (eisEmbedding (symbol (onceCuspScale u*omega^p.1.val) p.2.2.val.val)*
    eisEmbedding (symbol p.2.2.val.val p.2.1.val))*((v/heightDenominator z v r:ℝ):ℂ)^s
  have hi:((v/heightDenominator z v r:ℝ):ℂ)=(((heightDenominator z v r/v:ℝ):ℂ))⁻¹:=by
    simp only [Complex.ofReal_div,inv_div]
  rw [hi,Complex.inv_cpow_ofReal_nonneg (div_nonneg hp.le hv.le),Complex.cpow_neg]

def diagonalOnceCuspIndex (u t:Eisˣ) : OnceRamifiedData≃CuspCosets :=
  (onceRamifiedEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

def diagonalUnitCuspIndex (u t:Eisˣ) : UnitLowerData≃CuspCosets :=
  (unitLowerEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)

lemma diagonal_once_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:OnceRamifiedData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s
      (diagonalOnceCuspIndex u t p)=
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (onceRamifiedEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,onceRamified_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.2.1 p.2.2.val

lemma diagonal_unit_summand (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) (p:UnitLowerData) :
    summand (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s
      (diagonalUnitCuspIndex u t p)=
      affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis)) z v s p.1.val p.2.val.val := by
  rw [mul_assoc]
  change summand _ _ (primitiveRowEquiv.symm
    ((diagonalPrimitiveEquiv u).symm (unitLowerEquiv t p)))=_
  rw [diagonal_ray_summand,Equiv.apply_symm_apply,unitLower_summand]
  change eisEmbedding (symbol ((↑u⁻¹:Eis)^2) p.2.val.val)*affineLowerTerm _ _ _ _ _ _ _=_
  exact affineLowerTerm_mul_ray _ _ _ _ _ _ p.1 p.2.val

theorem diagonal_once_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv)) s=
      ∑'p:OnceRamifiedData,affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val := by
  rw [eisenstein,←(diagonalOnceCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_once_summand u t z v hv s)

theorem diagonal_unit_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s=
      ∑'p:UnitLowerData,affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis))
        z v s p.1.val p.2.val.val := by
  rw [eisenstein,←(diagonalUnitCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_unit_summand u t z v hv s)

theorem hasSum_diagonal_once_integrals (u t:Eisˣ) (v:ℝ) (hv:0<v) (s freq:ℂ) (hs:2<s.re) :
    HasSum (fun p:OnceRamifiedData=>∫z in periodDomain,
      affineLowerTerm (onceCuspScale t*omega^p.1.val)
        ((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^p.1.val)) z v s p.2.1.val p.2.2.val.val*
          ShortDraftTrace.breveE (-freq*z))
      (∫z in periodDomain,eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
        integralComplexMatrix (lowerCuspMatrix (onceCuspScale t))*upperSection z v hv) s*
          ShortDraftTrace.breveE (-freq*z)) := by
  have hh:=(diagonalOnceCuspIndex u t).hasSum_iff.mpr
    (hasSum_integral_fixed_left_Eisenstein
      (integralComplexMatrix (unitCuspDiagonal u)*integralComplexMatrix (lowerCuspMatrix (onceCuspScale t)))
      v hv s freq hs)
  apply hh.congr_fun
  intro p
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z=>by dsimp only; rw [mul_assoc,diagonal_once_summand])

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
local instance instMeasureSpaceUnitAddCircle_solutions_2 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsAddHaarMeasureUnitAddCircleVolume_solutions_2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions_2_rb615b9_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def eisensteinCoordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) : Fin 2→ℝ :=
  ![(ActualEisensteinCoordinates.coords b).1 • x 0-(ActualEisensteinCoordinates.coords b).2 • x 1,
    (ActualEisensteinCoordinates.coords b).2 • x 0+
      ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • x 1]

def eisensteinTorusMul (b : ActualEisensteinCubic.O) : UnitAddTorus (Fin 2)→+UnitAddTorus (Fin 2) where
  toFun t :=
    ![(ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1,
      (ActualEisensteinCoordinates.coords b).2 • t 0+
        ((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1]
  map_zero' := by ext i;fin_cases i <;> simp
  map_add' t s := by ext i;fin_cases i <;> simp [smul_add] <;> abel

lemma eisensteinTorusMul_continuous (b : ActualEisensteinCubic.O) : Continuous (eisensteinTorusMul b) := by
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).1 • t 0-(ActualEisensteinCoordinates.coords b).2 • t 1)
    fun_prop
  · change Continuous (fun t : UnitAddTorus (Fin 2) => (ActualEisensteinCoordinates.coords b).2 • t 0+((ActualEisensteinCoordinates.coords b).1-(ActualEisensteinCoordinates.coords b).2) • t 1)
    fun_prop

lemma periodVector_coordinateMul (b : ActualEisensteinCubic.O) (x : Fin 2→ℝ) :
    periodVector (eisensteinCoordinateMul b x)=eisEmbedding b*periodVector x := by
  have hb : eisEmbedding b=((ActualEisensteinCoordinates.coords b).1:ℂ)+
      ((ActualEisensteinCoordinates.coords b).2:ℂ)*omega3 := by
    simpa only [ActualEisensteinCubic.eisEmbedding_eval] using (congrArg eisEmbedding (ActualEisensteinCoordinates.eval_coords b)).symm
  rw [periodVector_apply,periodVector_apply,hb]
  simp only [eisensteinCoordinateMul,Matrix.cons_val_zero,Matrix.cons_val_one,
    zsmul_eq_mul]
  push_cast
  linear_combination -(3*((ActualEisensteinCoordinates.coords b).2:ℂ)*(x 1:ℂ))*EisensteinEmbedding.omega3_sq

lemma eisensteinTorusMul_periodTorus (b : ActualEisensteinCubic.O) (z : ℂ) :
    eisensteinTorusMul b (periodTorus z)=periodTorus (eisEmbedding b*z) := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  rw [←periodVector_coordinateMul,periodTorus_periodVector,periodTorus_periodVector]
  ext i
  fin_cases i <;> rfl

lemma eisensteinTorusMul_surjective (b : ActualEisensteinCubic.O) (hb : b≠0) : Function.Surjective (eisensteinTorusMul b) := by
  intro t
  refine ⟨periodTorus ((eisEmbedding b)⁻¹*periodSection t),?_⟩
  rw [eisensteinTorusMul_periodTorus,←mul_assoc,mul_inv_cancel₀ (eisEmbedding_ne_zero hb),one_mul,
    periodTorus_section]

theorem eisensteinTorusMul_measurePreserving (b : ActualEisensteinCubic.O) (hb : b≠0) :
    MeasurePreserving (eisensteinTorusMul b) volume volume :=
  AddMonoidHom.measurePreserving (eisensteinTorusMul_continuous b) (eisensteinTorusMul_surjective b hb) rfl

lemma periodTorus_eq_implies_lattice_difference (z w : ℂ) (h : periodTorus z=periodTorus w) :
    ∃n : ActualEisensteinCubic.O,z=w+3*eisEmbedding n := by
  obtain ⟨x,rfl⟩ := periodVector.surjective z
  obtain ⟨y,rfl⟩ := periodVector.surjective w
  rw [periodTorus_periodVector,periodTorus_periodVector] at h
  have hz (i : Fin 2) : ((x i-y i:ℝ):UnitAddCircle)=0 := by
    rw [AddCircle.coe_sub,congrFun h i,sub_self]
  obtain ⟨n0,hn0⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 0)
  obtain ⟨n1,hn1⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp (hz 1)
  simp only [zsmul_eq_mul,mul_one] at hn0 hn1
  have hx0 : x 0=y 0+n0 := by linarith
  have hx1 : x 1=y 1+n1 := by linarith
  refine ⟨ActualEisensteinCoordinates.eval n0 n1,?_⟩
  rw [periodVector_apply,periodVector_apply,ActualEisensteinCubic.eisEmbedding_eval,hx0,hx1]
  push_cast
  ring

lemma periodic_function_periodSection (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (z : ℂ) :
    f (periodSection (periodTorus z))=f z := by
  obtain ⟨n,hn⟩ := periodTorus_eq_implies_lattice_difference (periodSection (periodTorus z)) z
    (periodTorus_section (periodTorus z))
  rw [hn,hp]

theorem period_integral_eisenstein_mul (f : ℂ→ℂ) (hf : Measurable f)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (b : ActualEisensteinCubic.O) (hb : b≠0) :
    (∫z in periodDomain,f (eisEmbedding b*z))=∫z in periodDomain,f z := by
  let F : UnitAddTorus (Fin 2)→ℂ := fun t=>f (periodSection t)
  have hF : Measurable F := hf.comp periodSection_measurableEmbedding.measurable
  have hm := eisensteinTorusMul_measurePreserving b hb
  have hi : (∫t,F (eisensteinTorusMul b t))=∫t,F t := by
    have hh := integral_map («μ» := (volume : Measure (UnitAddTorus (Fin 2)))) hm.measurable.aemeasurable hF.stronglyMeasurable.aestronglyMeasurable
    rw [hm.map_eq] at hh
    exact hh.symm
  rw [periodTorus_integral,periodTorus_integral] at hi
  simp only [eisensteinTorusMul_periodTorus,F,periodic_function_periodSection f hp] at hi
  simp only [Complex.real_smul] at hi
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (show (2/(9*Real.sqrt 3):ℝ)≠0 by positivity)) hi

end CubicEisenstein

open MeasureTheory Filter
open scoped BigOperators Classical ENNReal

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_index_period_unfold_of_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f)
    (hsum:Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℂ:=fun n=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫z:ℂ,f z := by
    rw [GaussianFiberEquiv.fiber_tsum q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)]
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    change (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    simp_rw [he]
    rw [←integral_eq_period_integrals (fun z=>f (z+b)) (hf.comp_add_right b)]
    exact integral_add_right_eq_self f b
  have hsplit:=(hsum.hasSum.tsum_fiberwise (Ideal.Quotient.mk (Ideal.span {q}))).tsum_eq.symm
  change (∑'n:Eis,I n)=_ at hsplit ⊢
  rw [hsplit]
  change (∑'r:Eis⧸Ideal.span {q},∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=_
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℂ)=(Nat.card (Eis⧸Ideal.span {q}):ℂ)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_lintegral (q:Eis) (hq:q≠0) (f:ℂ→ℝ≥0∞) :
    (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℝ≥0∞)*(∫⁻z:ℂ,f z) := by
  let : Finite (Eis⧸Ideal.span {q}):=finite_quotient_span hq
  let : Fintype (Eis⧸Ideal.span {q}):=Fintype.ofFinite _
  let I:Eis→ℝ≥0∞:=fun n=>∫⁻z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)
  have hinner (r:Eis⧸Ideal.span {q}) :
      (∑'n:((Ideal.Quotient.mk (Ideal.span {q})) ⁻¹' {r}),I n.val)=∫⁻z:ℂ,f z := by
    rw [←(GaussianFiberEquiv.fiberEquiv q hq r (GaussianShiftedPartition.representative q r)
      (GaussianShiftedPartition.representative_spec q r)).tsum_eq]
    change (∑'n:Eis,∫⁻z in periodDomain,f (z+3*eisEmbedding
      (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q))=_
    let b:=3*eisEmbedding (GaussianShiftedPartition.representative q r)/eisEmbedding q
    have he (n:Eis) (z:ℂ) :
        z+3*eisEmbedding (GaussianShiftedPartition.representative q r+q*n)/eisEmbedding q=
          (z+3*eisEmbedding n)+b := by
      dsimp [b]
      simp only [map_add,map_mul]
      field_simp [eisEmbedding_ne_zero hq]
      ;ring
    simp_rw [he]
    rw [←lintegral_eq_period_lintegrals (fun z=>f (z+b))]
    exact lintegral_add_right_eq_self f b
  change (∑'n:Eis,I n)=_
  rw [←ENNReal.tsum_fiberwise I (Ideal.Quotient.mk (Ideal.span {q}))]
  simp only [hinner,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  change (Fintype.card (Eis⧸Ideal.span {q}):ℝ≥0∞)=(Nat.card (Eis⧸Ideal.span {q}):ℝ≥0∞)
  rw [Nat.card_eq_fintype_card]

lemma finite_index_period_integrals_summable (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    Summable (fun n:Eis=>∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q)) := by
  apply Summable.of_enorm
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n=>enorm_integral_le_lintegral_enorm _))
  rw [finite_index_period_lintegral q hq (fun z=>‖f z‖ₑ)]
  exact ENNReal.mul_lt_top (by simp) hf.hasFiniteIntegral

theorem finite_index_period_unfold (q:Eis) (hq:q≠0) (f:ℂ→ℂ) (hf:Integrable f) :
    (∑'n:Eis,∫z in periodDomain,f (z+3*eisEmbedding n/eisEmbedding q))=
      (Ideal.absNorm (Ideal.span {q}):ℂ)*(∫z:ℂ,f z) :=
  finite_index_period_unfold_of_summable q hq f hf
    (finite_index_period_integrals_summable q hq f hf)

end CubicEisenstein

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def actualMarkedSecondProfileData {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) (A₁ A₂ : Finset ι) : SecondProfileData ι :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  expansionProfileData p Ψ (m*b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit*d)
    c d z A₁ A₂ x.second

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def pairedSlotAssignment (J₁ J₂ : Finset σ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : Fin (J₁.card+J₂.card) → ι :=
  Fin.addCases (indexedSlotAssignment J₁ q.1) (indexedSlotAssignment J₂ q.2)

def pairedSlotWeight (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁ q.1)*slotAssignmentWeight J₂ a₂ q.2

def attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0)
    (newAssigned : Fin Jn → ι) : MarkedSecondSource ι Jo Jn where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := newAssigned

def attachPairedSlots {Jo : ℕ} (J₁ J₂ : Finset σ)
    (q : MarkedSecondSource ι Jo 0 × ((∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))) :
    MarkedSecondSource ι Jo (J₁.card+J₂.card) :=
  attachSecondSlots q.1 (pairedSlotAssignment J₁ J₂ q.2)

def assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    Finset (MarkedSecondSource ι Jo (J₁.card+J₂.card)) :=
  ((source ×ˢ ((J₁.pi (fun i => L₁ i)) ×ˢ (J₂.pi (fun i => L₂ i)))).filter
    (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q.2 j ∈ q.1.second.sourceCommon∪q.1.second.overlap)).image
      (attachPairedSlots J₁ J₂)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourcePrime )
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def actualSecondSignedWeight {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ℂ :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  secondSignedSourceWeight p hp hcop hg Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit*d) c d z x.second

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def actualSecondRawInheritedPuncture {Jo Jn : ℕ} (m : O) (x : MarkedSecondSource ι Jo Jn) : O :=
  ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*b0Label p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    secondExpansionQuotient p x.second

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein

local notation "O" => ActualEisensteinCubic.O

def primeGauss (p : O) (hp : p ≠ 0) (χ : MulChar (O ⧸ Ideal.span {p}) ℂ)
    (h : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {p}, χ x * quotientTrace p hp (Ideal.Quotient.mk _ h * x)

def primePowerGauss (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  conductorFourier p (p ^ n) hp (pow_ne_zero _ hp) χ h

def scalarKOne (p : O) (hp : p ≠ 0)
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {p}, χ d * primePowerGauss p hp ξ n
    (h - p ^ n * GaussianShiftedPartition.representative p d)

end SevenEighths.ProbePrimePower
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

def exactQuotient (a b : O) (h : b ∣ a) : O := Classical.choose h

def positiveScalar (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) : ℂ :=
  if k = 0 then primePowerGauss p hp (χ^(n+1)) n (p^j)
  else ∑' d : O ⧸ Ideal.span {p^k},
    if h : p^k ∣ p^j-p^(n+1)*representative (p^k) d then
      (χ^k) (Ideal.Quotient.mk (Ideal.span {p}) (representative (p^k) d)) *
        primePowerGauss p hp (χ^(n+1)) n
          (exactQuotient (p^j-p^(n+1)*representative (p^k) d) (p^k) h)
    else 0

@[simp] theorem positiveScalar_kzero (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 0 j = primePowerGauss p hp (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, ite_true]

end SevenEighths.ProbePrimePower
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

def quotientFourier (p c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {c}, χ (Ideal.Quotient.mk _ (representative c d)) *
    quotientTrace c hc (Ideal.Quotient.mk _ (H*representative c d))

end SevenEighths.ProbePrimePower
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

def rawFourier (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a}, F m * quotientTrace a ha (Ideal.Quotient.mk _ H * m)

def congruenceCoefficient (a s : O) (ha : a≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s}, χ d *
    (if h : s ∣ H-a*representative s d then
      rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)

def fullFourier (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a*s}, F (conductorReduction a s m) *
    rawFourier s hs χ (-representative (a*s) m) *
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ H*m)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalMarkedTerm (eta a X W V : ℂ) (e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (6*m)) e l k m

include hc

omit hc in
@[simp] theorem markedTerm_zero_index (eta a X W V : ℂ) (k m : ℕ) :
    principalMarkedTerm p hp hg eta a X W V 0 0 k m = 0 := by
  simp only [principalMarkedTerm, mul_zero, add_zero, ite_true]

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalInner (eta a X W V : ℂ) (e l : ℕ) : ℂ :=
  ∑' k : ℕ, ∑' m : ℕ, principalMarkedTerm p hp hg eta a X W V e l k m

include hc

omit hc in
@[simp] lemma principalInner_zero (eta a X W V : ℂ) :
    principalInner p hp hg eta a X W V 0 0 = 0 := by
  simp only [principalInner, markedTerm_zero_index p hp hg, tsum_zero]

def principalMarkedSeries (eta a X W V : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, principalInner p hp hg eta a X W V e.val l

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def principalFullSeries (eta a X W V : ℂ) : ℂ :=
  1/(1-V)+W/(1-W)+principalMarkedSeries p hp hg eta a X W V

include hc

omit hc

def actualACube (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p)^3 * HeckeFamily.elementCoeff eta p^3

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def sourceScalar (t k j : ℕ) : ℂ :=
  if t=0 then
    if k=0 then 1 else (actualSextic (Ideal.span {p}) hg ^ k) (Ideal.Quotient.mk _ (p^j))
  else positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k j

def sourcePrincipalTerm (eta a x w z : ℂ) (e l k m : ℕ) : ℂ :=
  sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (6*m)) e l k m

def sourcePrincipalSeries (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z e.val l k m

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_prime_supported (S : Finset Id) (hbad : fixedBadPrimes⊆S)
    (P : PrimeIdeal) (hP : P.val∉S) : Supported P.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  refine ⟨P.property.ne_zero,?_⟩
  intro Q hQ
  have heq : Q=P.val := by
    simpa only [normalizedFactors_irreducible P.property.irreducible,normalize_eq,
      Multiset.mem_singleton] using hQ
  subst Q
  exact (prime_good_iff_not_bad P.val).mpr (fun h=>hP (hbad h))

structure SourceExclusions (S : Finset Id) : Prop where
  prime : ∀P∈S,Prime P
  bad : fixedBadPrimes⊆S
  tail : CorrectionTail S

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set
namespace SevenEighths.HeckeLogarithmicInput
open HeckeFamily

def regular (η : Character) (s : ℂ) : ℂ :=
  if η.residue = 1 then HeckePrincipalStrip.sourceNormalized η s else LFunction η s

def uniformConstant : ℝ :=
  108*((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10))

end SevenEighths.HeckeLogarithmicInput

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductX
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds
local notation "Id" => Ideal ActualEisensteinCubic.O

def continuedSourceMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(x+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((x+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS) x *
      globalClosedCorrection η S x w z * slotMultiplier η J T b x w z

end SevenEighths.ProbeFiniteProductX
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianJointMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : ℝ :=
  ∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedFamilyIntegral {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
    (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianCompletedFamilyMass {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*∏i,‖W i (q k i)‖

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def rowMarkedTerm (eta a X W V rho : ℂ) (j e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    rowWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V rho
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (j+6*m)) e l k m

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowInner (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑' k, ∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m

def rowMarkedSeries (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2, ∑' l,rowInner p hp hg eta a X W V rho j e.val l

@[simp] lemma rowInner_zero (eta a X W V rho : ℂ) (j : ℕ) :
    rowInner p hp hg eta a X W V rho j 0 0=0 := by
  simp only [rowInner,rowMarkedTerm,mul_zero,add_zero,ite_true,tsum_zero]

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

def sourceRowTerm (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (j+6*m)) e l k m

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowBaseFinite (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑ k : Fin 2,
    (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V))

def rowClosedMarked (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  (rowBaseFinite p hp hg eta a X W V rho j 0 2+
   rowBaseFinite p hp hg eta a X W V rho j 1 0+
   rowBaseFinite p hp hg eta a X W V rho j 0 1+
   rowBaseFinite p hp hg eta a X W V rho j 1 1)/
    (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)

def sourceRowSeries (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j e.val l k m

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

def ramifiedStrictSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        (coordV (Ideal.absNorm (Ideal.span {p})) z)))

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def integrand (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+HeckeDyadic.shift σ freq-(1/2 : ℂ)) *
    series χ (s+HeckeDyadic.shift σ freq)

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.HeckePrimeRay
open HeckeFamily HeckePrimeAnnular
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance instIsPrincipalIdealRingO_solutions_rb615b9_1 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
def twistedFamily (η : Character) (θ : RayQuotient.Characters M H) : Character :=
  η.product (HeckeRayQuotient.character M H hH θ)

def rayPrimePolynomial (η : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter
    (fun I => Prime I ∧ I∈RayQuotient.identityClass M H),
      idealCoeff η I*annularWeight W D σ freq I

end SevenEighths.HeckePrimeRay

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentHeckeSlots CenteredMomentHeckeHeight HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def residualCenteredRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  centeredSlotRow η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))
    (Y₁/Ideal.absNorm (selectedPlain D a 0)) (Y₂/Ideal.absNorm (selectedPlain D a 1))
    (T/selectedNorm D a)

end SevenEighths.CenteredMomentDivisorRawEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open CenteredMomentDivisorRawEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

def retainedPositiveRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  positiveSlotRow η m A z (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂))
    S β P t (clippedScale X₁) (clippedScale X₂)

end SevenEighths.CenteredMomentRetainedEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentWholeSlotDeletion
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeHeight
local notation "O" => ActualEisensteinCubic.O

def normalizedSlot (η:Character) (m A z:O) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (t P:ℝ) : ℂ := (Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S β t

def selectedProduct {α:Type*} (J:Finset α) (η:Character) (m A z:O)
    (W₁ W₂:ℝ→ℂ) (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ)
    (t X₁ X₂:ℝ) : ℂ :=
  ((Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂))*
    ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i)

end SevenEighths.CenteredMomentWholeSlotDeletion

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

def primePool (M:Ideal O) (H:Subgroup (O⧸M)ˣ) (b D:ℝ) : Finset (Ideal O) :=
  (annulusSet b D).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem oriented_twist_support (reverse : Bool) (W : ℝ→ℂ) (σ t : ℝ) :
    Function.support (twistProfile (HeckeDetectorCoefficientTransfer.orientedProfile reverse W) σ t)
      ⊆Function.support W := by
  apply (twistProfile_support _ _ _).trans
  cases reverse <;> simp only [HeckeDetectorCoefficientTransfer.orientedProfile,ite_true]
  · exact Set.Subset.rfl
  · intro x hx hzero
    exact hx (by simp only [hzero,map_zero])

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic

def realInterpolatedLog (W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • W (Real.exp x)

def realInterpolatedLogSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logSchwartz (twistProfile W p.1 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W p.1 0 a b ha hs hW)

def interpolatedProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CenteredMomentLattice.normPowerProfile (twistProfile W σ 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W σ 0 a b ha hs hW) t

lemma interpolatedProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t x : ℝ) :
    interpolatedProfile W a b ha hs hW σ t x=twistProfile W σ t x := by
  rw [interpolatedProfile,CenteredMomentLattice.normPowerProfile_apply]
  unfold twistProfile
  by_cases hw : W x=0
  · simp [hw]
  · have hx : 0<x := ha.trans_le (hs hw).1
    calc
      _=W x*((x:ℂ)^(Complex.I*t)*(x:ℂ)^(-HeckeDyadic.shift σ 0)) := by ring
      _=W x*(x:ℂ)^(Complex.I*t-HeckeDyadic.shift σ 0) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2;unfold HeckeDyadic.shift;simp only [Complex.ofReal_zero,zero_mul,sub_zero];ring

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification

def scaleCLM : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (-1/2:ℝ) • ContinuousLinearMap.id ℝ (𝓢(ℝ,ℂ))-
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ=>x)).comp (SchwartzMap.derivCLM ℝ ℂ)

lemma scaleCLM_apply (W : 𝓢(ℝ,ℂ)) (x : ℝ) : scaleCLM W x=scaleProfile W x := by
  simp only [scaleCLM,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    SchwartzMap.derivCLM_apply,Complex.real_smul,scaleProfile]
  push_cast
  ring

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveAllocation
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy
open CenteredMomentSlotRatios CenteredMomentDivisorRectangle
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def activeAllocations (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) :
    Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  Finset.univ.filter (fun a=>∃z:O,allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂≠0)

end SevenEighths.CenteredMomentActiveAllocation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

def weight (I : Ideal O) : ℝ := (Real.sqrt (I.absNorm : ℝ))⁻¹

def exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) (P : S) : ℕ :=
  (normalizedFactors I.val.val).count P.val

def localMass (P : Ideal O) : ℝ := (1+weight P)/(1-weight P)

def coefficient (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P):ℝ) * norm H.val) : ℂ)

def unitSmooth (S : Finset (Ideal O)) : SmoothIdeal S :=
  ⟨⟨1,one_ne_zero⟩,by
    change (normalizedFactors (1 : Ideal O)).toFinset ⊆ S
    rw [normalizedFactors_one]
    exact Finset.empty_subset _⟩

end SevenEighths.CenteredMomentReflectionMass
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_support
  scaleSupport )

def scaleTest (W : ℝ→ℂ) (j : Fin 2) : ℝ→ℂ :=
  if j=0 then W else scaleProfile W

lemma scaleTest_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) (j : Fin 2) :
    Function.support (scaleTest W j)⊆Icc a b := by
  unfold scaleTest
  split
  · exact hs
  · exact scaleProfile_support W a b hs

end SevenEighths.CenteredMomentScaleSupremum

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSupportedZeroEnergy
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentZeroMeanBridge EisensteinSchwartzPoisson HeckeFamily
local notation "O" => ActualEisensteinCubic.O

def activeColumns (S : Finset (Ideal O)) (c : Ideal O → ℂ) : Finset (Ideal O) :=
  (supportedColumns S).filter (fun I => c I≠0)

lemma activeColumns_supported (S : Finset (Ideal O)) (c : Ideal O → ℂ)
    (I : Ideal O) (hI : I∈activeColumns S c) : Supported I :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2

end SevenEighths.CenteredMomentSupportedZeroEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate BigOperators
namespace SevenEighths.HeckePrimeRow
open HeckeFamily CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_rb615b9_1 : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance instIsPrincipalIdealRingO_solutions_rb615b9_2 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
def canonicalPrimeAmplitude (u : O) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ P∈(HeckePrimeAnnular.annulusSet b D).filter
    (fun P => Prime P ∧ P∈RayQuotient.identityClass M H),
    starRingEnd ℂ (idealRowHom u P)*W ((P.absNorm : ℝ)/D)*
      (((P.absNorm : ℝ)/D : ℝ) : ℂ)^(z-1)

end SevenEighths.HeckePrimeRow

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondSourcePowerDescent
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge
open CenteredMomentMobiusRegroup CenteredMomentSecondWindowBudget
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFiniteProfileExceptional
open EisensteinSchwartzPoisson

open CenteredMomentLogDyadic
open MeasureTheory UniqueFactorizationMonoid

local instance instDecidableEqSumFinOfNatNat_solutions_rb615b9_1 : DecidableEq (ι⊕Fin 2):=Classical.decEq _
def physicalFactors (Cmain Cexc Cdiag Ctail Z ε δ θ B saving K t ηNorm E₁ E₂ r
    loProduct wlo : ℝ) (J₁ J₂ : ℕ) (SΦ : Finset (ℕ×ℕ))
    (W : 𝓢(ℝ,ℂ)) : Fin 4→ℝ :=
  ![Cmain*Z^(2*δ+ε)*ηNorm*Real.sqrt (E₁*E₂)*heightEnvelope t^(J₁+J₂)*
      profileMoment J₁*profileMoment J₂,
    Cexc*Z^(2*ε+2*δ+2*(5*B+1)*θ-2*max r 0/3)*K^(5/6:ℝ)*
      (loProduct*wlo*wlo)^(-2/3:ℝ),
    Cdiag*K*‖paperRadialFourier W 0‖,
    Ctail*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*K*Z^(-saving)]

end SevenEighths.CenteredMomentSecondSourcePowerDescent

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients
open HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondSourcePowerDescent CenteredMomentSecondWindowBudget
local notation "O"=>HeckeFamily.O

def fixedFactors (Cm Ce Cd Ct Z epsilon delta theta B cost Ebase t loFloor seed:ℝ)
    (J:ℕ)(Sf:Finset (ℕ×ℕ))(W:𝓢(ℝ,ℂ)):Fin 4→ℝ:=
  ![Cm*Z^(2*delta+epsilon)*cost*Ebase*heightEnvelope t^(J+J)*profileMoment J*profileMoment J,
    Ce*Z^(2*epsilon+2*delta+2*(5*B+1)*theta)*loFloor^(-2/3:ℝ),
    Cd*‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖,
    Ct*Sf.sup (schwartzSeminormFamily ℝ ℝ ℂ) W/seed]

end SevenEighths.CenteredMomentEnergyFirstGaussianCoefficients

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def dyadicLength (U : ℝ) : ℕ := HeckeDetectorPartition.length (⌈2*U^21⌉₊ : ℝ)+1

structure Witness {ι : Type*} (χ : ι→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) where
  label : ι
  zero : ℂ
  zero_eq : LFunction (χ label) zero=0
  zero_lower : a≤zero.re
  zero_height : |zero.im|≤(3*i : ℕ)*T
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  nu : ℝ
  r : ℝ
  m : ℝ
  nu_bound : ‖nu‖≤allowance
  left_scale : U^r=(2 : ℝ)^left.val
  right_scale : U^m=(2 : ℝ)^right.val
  inverse_length_lower : tstar-1/2-76*ε≤ r
  inverse_length_upper : r≤tstar+ε
  plain_length_lower : 0≤ m
  plain_length_upper : m≤1/2+75*ε
  inverse_spike : U^((2*a-1)*r-2*ε)≤
    ‖polynomial (χ label) true
      (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
      (U^r) zero.re (2*Real.pi*nu-zero.im)‖^2
  plain_spike : U^((2*a-1)*m-2*ε)≤
    ‖polynomial (χ label) false positiveAnnular (U^m) zero.re (2*Real.pi*nu-zero.im)‖^2

def Witness.frequency {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : ℝ := 2*Real.pi*w.nu-w.zero.im

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorInverseFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial

def inverseTest (U tstar r : ℝ) : ℝ→ℂ :=
  HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r)

variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

end SevenEighths.HeckeDetectorInverseFiberCount

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialPhysicalSlots
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open InverseInitialRawDictionary
open InverseInitialConjugateEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def livePrimes (V : ℝ→ℂ) (b D : ℝ) : Finset (Ideal O) :=
  ((HeckePrimeAnnular.annulusSet b D).filter
    (fun P=>Prime P ∧ P∈RayQuotient.identityClass M H)).filter
      (fun P=>V ((P.absNorm:ℝ)/D)≠0)

end SevenEighths.InverseInitialPhysicalSlots

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily

def detectorEntire (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue=1 then HeckeOrigin.poleRemoved χ s else HeckeOrigin.continued χ s

lemma detectorEntire_eq_nonprincipal (χ : Character) (hχ : χ.residue≠1) :
    detectorEntire χ=LFunction χ := by
  funext s
  simp only [detectorEntire,HeckeOrigin.continued,if_neg hχ]

lemma detectorEntire_entire (χ : Character) : Differentiable ℂ (detectorEntire χ) := by
  by_cases hχ : χ.residue=1
  · have he : detectorEntire χ=HeckeOrigin.poleRemoved χ := by funext s;simp [detectorEntire,hχ]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    exact LFunction_entire_nonprincipal χ hχ

lemma detectorEntire_zero_iff (χ : Character) {s : ℂ} (hs : 0<s.re) :
    detectorEntire χ s=0 ↔ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · simp only [detectorEntire,if_pos hχ]
    by_cases h1 : s=1
    · subst s
      simp [HeckeOrigin.poleRemoved_one_ne_zero χ hχ,hχ]
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
      simp [mul_eq_zero,sub_ne_zero.mpr h1,h1]
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    simp [hχ]

lemma detectorEntire_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1<s.re) :
    detectorEntire χ s≠0 := by
  intro hz
  exact LFunction_ne_zero_of_one_lt_re χ hs ((detectorEntire_zero_iff χ (by linarith)).mp hz).1

def detectorZeros (χ : Character) (T : ℝ) : Set ℂ :=
  {s | s∈HeckeDetectorZeros.rectangle T ∧ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1)}

lemma detectorZeros_finite (χ : Character) (T : ℝ) : (detectorZeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (detectorEntire χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (detectorEntire_entire χ)
  have hc := ha.preimage_zero_mem_codiscreteWithin
    (detectorEntire_ne_zero_of_one_lt_re χ (by norm_num : 1<(2:ℂ).re))
    (Set.mem_univ (2:ℂ)) isConnected_univ
  have hf := (HeckeDetectorZeros.rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (HeckeDetectorZeros.rectangle T)) hc)
  convert (preTransparency := .instances) hf using 1
  ext s
  by_cases hs : s∈HeckeDetectorZeros.rectangle T
  · have hr : 0<s.re := by have h:=hs.1;linarith
    simp [detectorZeros,hs,detectorEntire_zero_iff χ hr]
  · simp [detectorZeros,hs]

def detectorZeroFinset (χ : Character) (T : ℝ) : Finset ℂ := (detectorZeros_finite χ T).toFinset

@[simp] lemma mem_detectorZeroFinset (χ : Character) (T : ℝ) (s : ℂ) :
    s∈detectorZeroFinset χ T ↔ (51/100:ℝ)≤ s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  simp only [detectorZeroFinset,Set.Finite.mem_toFinset,detectorZeros,HeckeDetectorZeros.rectangle,Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def detectorFamilyZeros (χ : ι→Character) (T : ℝ) : Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i=>(detectorZeroFinset (χ i) T).image (fun s=>(i,s)))

@[simp] lemma mem_detectorFamilyZeros (χ : ι→Character) (T : ℝ) (i : ι) (s : ℂ) :
    (i,s)∈detectorFamilyZeros χ T ↔ (51/100:ℝ)≤ s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) := by
  simp [detectorFamilyZeros]

def detectorRealParts (χ : ι→Character) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((detectorFamilyZeros χ T).image (fun p=>p.2.re))

lemma detectorRealParts_nonempty (χ : ι→Character) (T : ℝ) : (detectorRealParts χ T).Nonempty :=
  Finset.insert_nonempty _ _

def detectorMaximum (χ : ι→Character) (T : ℝ) : ℝ :=
  (detectorRealParts χ T).max' (detectorRealParts_nonempty χ T)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def rowNorm (u : FreeRow) : ℝ := (Ideal.span {u.val}:Ideal O).absNorm

lemma finite_bounded_freeRows (H : ℝ) : {u : FreeRow | rowNorm u≤H}.Finite := by
  by_contra hs
  obtain ⟨n,hn⟩ := exists_nat_gt (128*max 1 H)
  have hinf : Set.Infinite {u : FreeRow | rowNorm u≤H} := hs
  obtain ⟨T,hT,hcard⟩ := hinf.exists_subset_card_eq n
  have hc := freeRow_count T (max 1 H) (le_max_left _ _) (fun u hu=>(hT hu).trans (le_max_right _ _))
  rw [hcard] at hc
  exact not_le_of_gt hn hc

def boundedFreeRows (H : ℝ) : Finset FreeRow := (finite_bounded_freeRows H).toFinset

@[simp] lemma mem_boundedFreeRows {H : ℝ} {u : FreeRow} : u∈boundedFreeRows H ↔ rowNorm u≤H :=
  Set.Finite.mem_toFinset _

def rowBand (A B : ℝ) : Finset FreeRow := (boundedFreeRows B).filter (fun u=>u.val≠1 ∧ A≤ rowNorm u ∧ rowNorm u<B)

@[simp] lemma mem_rowBand {A B : ℝ} {u : FreeRow} :
    u∈rowBand A B ↔ u.val≠1 ∧ A≤ rowNorm u ∧ rowNorm u<B := by
  simp only [rowBand,Finset.mem_filter,mem_boundedFreeRows]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.2.2.le,h⟩

def dyadicRows (A : ℝ) (n : ℕ) : Finset FreeRow := rowBand (A*(2:ℝ)^n) (A*(2:ℝ)^(n+1))

lemma mem_dyadicRows {A : ℝ} {n : ℕ} {u : FreeRow} :
    u∈dyadicRows A n ↔ u.val≠1 ∧ A*(2:ℝ)^n≤ rowNorm u ∧ rowNorm u<2*(A*(2:ℝ)^n) := by
  simp only [dyadicRows,mem_rowBand,pow_succ]
  ring_nf

lemma dyadicRows_disjoint (A : ℝ) (hA : 0<A) : Pairwise (fun m n=>Disjoint (dyadicRows A m) (dyadicRows A n)) := by
  intro m n hmn
  apply Finset.disjoint_left.mpr
  intro u hm hn
  rw [mem_dyadicRows] at hm hn
  have hpow (j k : ℕ) (hjk : j<k) : 2*(A*(2:ℝ)^j)≤A*(2:ℝ)^k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.succ_le_iff.mpr hjk)
    have := mul_le_mul_of_nonneg_left hh hA.le
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using this
  rcases lt_or_gt_of_ne hmn with h|h
  · exact not_lt_of_ge ((hpow m n h).trans hn.2.1) hm.2.2
  · exact not_lt_of_ge ((hpow n m h).trans hm.2.1) hn.2.2

lemma exists_dyadicRows (A : ℝ) (hA : 0<A) (u : FreeRow) (hu : u.val≠1) (hU : A≤ rowNorm u) :
    ∃n : ℕ,u∈dyadicRows A n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hA).mpr (by simpa using hU)) (by norm_num : (1:ℝ)<2)
  refine ⟨n,mem_dyadicRows.mpr ⟨hu,?_,?_⟩⟩
  · have hh := (le_div_iff₀ hA).mp hn
    simpa only [mul_comm] using hh
  · have hh := (div_lt_iff₀ hA).mp hn'
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

def dyadicRowEquiv (A : ℝ) (hA : 0<A) :
    (Σn : ℕ,dyadicRows A n) ≃ {u : FreeRow // u.val≠1 ∧ A≤ rowNorm u} :=
  Equiv.ofBijective (fun p=>⟨p.2.val,(mem_dyadicRows.mp p.2.property).1,
    (le_mul_of_one_le_right hA.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans (mem_dyadicRows.mp p.2.property).2.1⟩) (by
    constructor
    · rintro ⟨m,u⟩ ⟨n,v⟩ heq
      have huv : u.val=v.val := congrArg Subtype.val heq
      have hmn : m=n := by
        by_contra h
        exact (Finset.disjoint_left.mp (dyadicRows_disjoint A hA h)) u.property (huv.symm ▸ v.property)
      subst n
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext huv))
    · intro u
      obtain ⟨n,hn⟩ := exists_dyadicRows A hA u.val u.property.1 u.property.2
      exact ⟨⟨n,⟨u.val,hn⟩⟩,rfl⟩)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentBase (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→Character :=
  Sum.elim (fun b=>if b then fixedSourcePrincipal S hS else η.inverse.excludePrimes S hS)
    (fun θ=>(HeckeRayQuotient.character M H hH θ).inverse)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily ConcretePrimeRowBridge CanonicalRowCompletion
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def relativeCharacter (η₀ : Character) (θ : RayQuotient.Characters M H) : Character :=
  (HeckeRayQuotient.character M H hH θ).product η₀.inverse

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance phaseField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def markedPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (-tau χ (quotientTrace p hp) 2)*(χ (-1))⁻¹^2*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^2

def residualPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (tau χ ((quotientTrace p hp).mulShift (-1)) 1*tau χ (quotientTrace p hp) 3)*
    (χ (-1))⁻¹^3*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)))*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^3

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

noncomputable local instance frozenField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance frozenFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenPrimeScalar (p c : Eis) [(Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  if j=4 then tau χ ((quotientTrace p hp).mulShift (-1)) 4*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))⁻¹^2
  else if j=0 then markedPrimeScalar p c hp hg
  else (tau χ ((quotientTrace p hp).mulShift (-1)) j*tau χ (quotientTrace p hp) (j+2)) *
    (χ (-1))⁻¹^(j+2)*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))^j*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c)))^(j+2)

def frozenCofactorCharacter (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (j : ℕ) : Eis →* ℂ :=
  (if j=4 then ((actualSextic P hg)⁻¹)^2 else (actualSextic P hg)^(2*j+2)).toMonoidHom.comp
    (Ideal.Quotient.mk P).toMonoidHom

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance frozenSplitFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenArgument [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ F, frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i)

def frozenCore [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, frozenPrimeScalar (p i) c (hp i) (hg i) (j i) *
    frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k)

end
end SevenEighths.InverseReflectedPhase

end OAI
end


