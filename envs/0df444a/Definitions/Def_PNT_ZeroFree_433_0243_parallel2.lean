-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0243_parallel2
-- name    : PNT_ZeroFree_433_0243_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:33.806387+00:00
-- url     : https://prove2.me/theorems/b1c1d806-b538-49ab-ad63-cf8c7f6666be
-- title:
--   Zero-free region foundations: Eisenstein.CubeResidueStrata [0243_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CubeResidueStrata
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeResidueStrata.lean#L215-L620

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0237_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0242_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeResidueStrata.lean
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


open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal GoodElement)
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)


lemma halfPrimaryFromAssociate_surjective : Function.Surjective halfPrimaryFromAssociate := by
  intro b
  let z:GoodElement:=⟨b.val,PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff b.val |>.mpr
    (halfPrimary_not_dvd b)⟩
  let p:=PrimaryIdealUnitReindex.unitIdealEquiv.symm z
  have he:(p.1:Eis)*primaryGenerator p.2.val=b.val:=
    congrArg Subtype.val (PrimaryIdealUnitReindex.unitIdealEquiv.apply_symm_apply z)
  let a:PrimaryLower:=primaryLowerIdealEquiv.symm p.2
  have ha:a.val=primaryGenerator p.2.val:=rfl
  have hea:(p.1:Eis)*a.val=b.val:=by simpa only [ha] using he
  have hu:ramLambda∣(p.1:Eis)-1:=by
    have hpa:ramLambda∣a.val-1:=halfPrimary_lambda_dvd_three.trans a.2
    have hh:=dvd_sub b.2 (hpa.mul_left (p.1:Eis))
    rw [←hea] at hh
    convert! hh using 1 ;ring
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega p.1
  · exact ⟨(j,a),Subtype.ext (by simpa only [halfPrimaryFromAssociate,hj] using hea)⟩
  · exact (halfPrimary_not_negative j.val (by simpa only [hj] using hu)).elim

def halfPrimaryAssociateEquiv : Fin 3×PrimaryLower ≃ HalfPrimary :=
  Equiv.ofBijective halfPrimaryFromAssociate
    ⟨halfPrimaryFromAssociate_injective,halfPrimaryFromAssociate_surjective⟩

lemma halfPrimaryAssociateEquiv_apply (j:Fin 3) (a:PrimaryLower) :
    (halfPrimaryAssociateEquiv (j,a)).val=omega^j.val*a.val:=rfl

lemma halfPrimary_tsum (f:Eis→ℂ) :
    (∑'b:HalfPrimary,f b.val)=∑'p:Fin 3×PrimaryLower,f (omega^p.1.val*p.2.val) :=
  halfPrimaryAssociateEquiv.tsum_eq (fun b:HalfPrimary=>f b.val) |>.symm

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O


theorem rational_cusp_lower_factor (u : Eisˣ) (n : ℤ) :
    rationalEmbedding ModularGroup.S*unitCuspUpper (n:Eis)*lowerCuspMatrix (u:Eis)=
      unitCuspDiagonal (-u)*lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis)))*
        unitCuspUpper (↑u⁻¹:Eis) := by
  apply Subtype.ext
  change ((!![(0 : ℤ), -1; 1, 0]).map (Int.castRingHom Eis) *
    !![1, (n : Eis); 0, 1] * !![1, 0; (u : Eis), 1]) =
    (!![(↑(-u) : Eis), 0; 0, (↑(-u)⁻¹ : Eis)] *
      !![1, 0; -(u : Eis) * (1 + (n : Eis) * (u : Eis)), 1] *
      !![1, (↑u⁻¹ : Eis); 0, 1])
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, neg_mul, Units.val_neg,
      mul_add, add_mul, mul_assoc, add_comm]

lemma unitCuspUpper_section (b : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (unitCuspUpper b)*upperSection z v hv=
      upperSection (z+eisEmbedding b) v hv := by
  apply Subtype.ext
  change ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) Eis).map eisEmbedding *
    !![(Real.sqrt v : ℂ), z / Real.sqrt v; 0, (Real.sqrt v : ℂ)⁻¹]) =
    !![(Real.sqrt v : ℂ), (z + eisEmbedding b) / Real.sqrt v;
      0, (Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring


end CubicEisenstein

open scoped Classical MatrixGroups


open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


lemma levelTwo_cube_zero_phase (A N:levelTwo) (p q:Eis)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^3*(A:SL(2,Eis)) 1 0)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=1 := by
  have hcop:IsCoprime ((N:SL(2,Eis)) 0 0) p:=by
    refine ⟨(N:SL(2,Eis)) 1 1,-(N:SL(2,Eis)) 0 1*p^2*(A:SL(2,Eis)) 1 0,?_⟩
    have hd:(N:SL(2,Eis)) 0 0*(N:SL(2,Eis)) 1 1-
        (N:SL(2,Eis)) 0 1*(N:SL(2,Eis)) 1 0=1:=by
      simpa only [Matrix.det_fin_two] using (N:SL(2,Eis)).property
    rw [hc] at hd
    linear_combination hd
  have hcube:eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hcop,map_one]
  have hb:=levelTwo_cube_phase_balance A N p q 0 hp hA hN (by simpa using hx) (by simpa using hc)
  simp only [pow_zero,mul_one,Nat.sub_zero,hcube] at hb
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  apply mul_right_cancel₀ hbase
  rw [one_mul,hcomp,hb]


end CubicKubota


open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O


namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}


lemma stratum_map (d:CubeCuspData A p q) (hp:p≠0) :
    cubeResidueStratumMap p (d.stratum hp)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A 0 0+3*q*A 1 0) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^d.exponent.val*GaussianShiftedPartition.representative
    (p^(3-d.exponent.val)) (Ideal.Quotient.mk _ (d.matrix 0 0))-(A 0 0+3*q*A 1 0)
  rw [d.first,←mul_sub]
  have hpow:p^3=p^d.exponent.val*p^(3-d.exponent.val):=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  rw [hpow]
  exact mul_dvd_mul_left _ (gaussRep_mk_congr _ _)

lemma comparison_phase (A2:levelTwo) (d:CubeCuspData (A2:SL(2,Eis)) p q)
    (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A2:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A2:SL(2,Eis)) 1 0) p) :
    complexCharacter ⟨d.matrix*(A2:SL(2,Eis))⁻¹,d.congruent⟩ =
      cubeStratumSymbol p ((A2:SL(2,Eis)) 1 0) d.exponent (d.stratum hp.ne_zero).2 := by
  let N2:levelTwo:=⟨d.matrix,comparison_levelTwo A2 d.matrix d.congruent⟩
  have hN:lambda^2∣d.matrix 0 0-1:=comparison_primary _ _ d.congruent hA
  have he:=levelTwo_cube_comparison_phase A2 N2 p q d.exponent.val
    (by omega:d.exponent.val≤3) hprimary hA hN d.first (d.lower_eq hp.ne_zero) hC d.congruent
  rw [he]
  unfold cubeStratumSymbol
  rw [←map_pow,←cubicSymbol_pow_denominator]
  apply congrArg eisEmbedding
  apply symbol_congr
  have hd:=gaussRep_mk_congr (p^(3-d.exponent.val)) (d.matrix 0 0)
  change p^(3-d.exponent.val)∣d.matrix 0 0*((A2:SL(2,Eis)) 1 0)-
    GaussianShiftedPartition.representative (p^(3-d.exponent.val))
      (Ideal.Quotient.mk _ (d.matrix 0 0))*((A2:SL(2,Eis)) 1 0)
  convert! dvd_mul_of_dvd_left (dvd_neg.mpr hd) ((A2:SL(2,Eis)) 1 0) using 1 ; ring

end CubeCuspData
end CubicKubota

end

end OAI

end


