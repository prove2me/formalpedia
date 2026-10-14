-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0227_parallel2
-- name    : PNT_ZeroFree_433_0227_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:28:39.500392+00:00
-- url     : https://prove2.me/theorems/011c6079-3ef6-4a36-ae90-c72c4772a820
-- title:
--   Zero-free region foundations: Eisenstein.RationalTranslations [0227_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.RationalTranslations
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RationalTranslations.lean#L84-L669

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0097
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221
import Definitions.Def_PNT_ZeroFree_433_0221_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0224_parallel1
import Definitions.Def_PNT_ZeroFree_433_0226_parallel1
import Definitions.Def_PNT_ZeroFree_433_0227_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/RationalTranslations.lean
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


end CubicEisenstein

end

end OAI

end


