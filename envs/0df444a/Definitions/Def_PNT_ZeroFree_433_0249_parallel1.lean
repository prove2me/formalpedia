-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0249_parallel1
-- name    : PNT_ZeroFree_433_0249_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:24:05.801754+00:00
-- url     : https://prove2.me/theorems/3bc7014b-7554-479d-b898-b307f7d3799d
-- title:
--   Zero-free region foundations: Eisenstein.InverseCorrespondence [0249_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.InverseCorrespondence
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCorrespondence.lean#L226-L598

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2
import Definitions.Def_PNT_ZeroFree_433_0239_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0245_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/InverseCorrespondence.lean
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


open Filter MeasureTheory
open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def primaryDenominatorShift (a:PrimaryLower) (m:Eis) : PrimaryCoprimeDenominator a≃PrimaryCoprimeDenominator a where
  toFun d:=⟨⟨d.val.val+3*a.val*m,by
    convert! dvd_add d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
      exact (isCoprime_right_congr_of_dvd a.val (d.val.val+3*a.val*m) d.val.val ⟨3*m,by ring⟩).mpr d.2⟩
  invFun d:=⟨⟨d.val.val-3*a.val*m,by
    convert! dvd_sub d.val.2 (show (3:Eis)∣3*a.val*m from ⟨a.val*m,by ring⟩) using 1 ;ring⟩,by
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
    convert! dvd_add hbase (a.2.mul_left (ramifiedAffineParameter j n*q)) using 1 ;ring
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

lemma affineCuspBlock_integral_translation (h q r:Eis) (j n:ℕ)
    (hq:q≠0) (hr:r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hbase:(3:Eis)∣h+ramifiedAffineParameter j n*q) (v:ℝ) (s b:ℂ) :
    (∫z in periodDomain,affineCuspBlock q r (z+b) v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z))=
      ShortDraftTrace.breveE (ninthCuspFrequency h*b)*
        ∫z in periodDomain,affineCuspBlock q r z v s*ShortDraftTrace.breveE (-ninthCuspFrequency h*z) :=
  period_integral_twisted_translation (fun z=>affineCuspBlock q r z v s) (ninthCuspFrequency h)
    (affineCuspBlock_weighted_periodic h q r j n hq hr hbase v s) b

end


section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O


def ramifiedCuspDirectIndex (b:Bool) : ℕ := if b then 2 else 1

def ramifiedCuspOppositeIndex (b:Bool) : ℕ := if b then 1 else 2

lemma ramified_omega_four : omega^4=omega := by
  rw [show (4:ℕ)=3+1 from rfl,pow_add,omega_primitive.pow_eq_one,pow_one,one_mul]


end

open Filter MeasureTheory
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspGaussSeries (u t:Eisˣ) (h:Eis) (s:ℂ) : ℂ :=
  ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (t:Eis))*
    unramifiedCubicGaussSeries s (3*((↑u⁻¹:Eis)^2*(t:Eis))^2*((↑t⁻¹:Eis)*h))


lemma unitCuspDiagonal_one : unitCuspDiagonal (1:Eisˣ)=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;>fin_cases j <;>simp [unitCuspDiagonal]


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

def cubeCoverMatrix (p : ActualEisensteinCubic.O) (hp : p≠0) : SL(2,ℂ) :=
  (cubeArchimedean_correspondence p hp).choose

lemma cubeCoverMatrix_spec (p : ActualEisensteinCubic.O) (hp : p≠0) :
    cubeCoverMatrix p hp 0 1=0 ∧ cubeCoverMatrix p hp 1 0=0 ∧
    cubeCoverMatrix p hp 0 0/cubeCoverMatrix p hp 1 1=ConcreteTraceCRT.eisEmbedding p^3 ∧
    ∀x : cubeKernelCorrespondence p,
      cubeCoverMatrix p hp*integralComplexMatrix (cubeKernelLeftGlobal p x)=
        integralComplexMatrix (cubeKernelRightGlobal p hp x)*cubeCoverMatrix p hp :=
  (cubeArchimedean_correspondence p hp).choose_spec


end CubicKubota

end

end OAI

end


