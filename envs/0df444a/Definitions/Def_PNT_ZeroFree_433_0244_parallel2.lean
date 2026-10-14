-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0244_parallel2
-- name    : PNT_ZeroFree_433_0244_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:21:21.200723+00:00
-- url     : https://prove2.me/theorems/2be00646-3978-470f-a0d6-1147b0b6f88b
-- title:
--   Zero-free region foundations: Reciprocity.RamifiedCuspPhases [0244_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.RamifiedCuspPhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedCuspPhases.lean#L173-L484

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0076
import Definitions.Def_PNT_ZeroFree_433_0088
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedCuspPhases.lean
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


end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


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


theorem eisenstein_unit_diagonal (u:Eisˣ) (g:SL(2,ℂ)) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*g) s=
      rayEisenstein ((↑u⁻¹:Eis)^2) g s := by
  rw [eisenstein,←primitiveRowEquiv.symm.tsum_eq]
  simp_rw [diagonal_ray_summand]
  exact (diagonalPrimitiveEquiv u).tsum_eq
    (fun v:PrimitiveRow=>eisEmbedding (symbol ((↑u⁻¹:Eis)^2) (v.val 1))*
      summand g s (primitiveRowEquiv.symm v))

end

section
open MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


def diagonalUnitCuspIndex (u t:Eisˣ) : UnitLowerData≃CuspCosets :=
  (unitLowerEquiv t).trans ((diagonalPrimitiveEquiv u).symm.trans primitiveRowEquiv.symm)


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


theorem diagonal_unit_eisenstein_rows (u t:Eisˣ) (z:ℂ) (v:ℝ) (hv:0<v) (s:ℂ) :
    eisenstein (integralComplexMatrix (unitCuspDiagonal u)*
      (integralComplexMatrix (lowerCuspMatrix (t:Eis)))*upperSection z v hv) s=
      ∑'p:UnitLowerData,affineLowerTerm (t:Eis) ((↑u⁻¹:Eis)^2*(t:Eis))
        z v s p.1.val p.2.val.val := by
  rw [eisenstein,←(diagonalUnitCuspIndex u t).tsum_eq]
  exact tsum_congr (diagonal_unit_summand u t z v hv s)


end


end CubicEisenstein


end

end OAI

end


