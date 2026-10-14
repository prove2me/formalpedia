-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0285_parallel1_1
-- name    : PNT_ZeroFree_433_0285_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:38:44.257301+00:00
-- url     : https://prove2.me/theorems/053c9e45-85a7-4a1b-b24f-992f9de0efd0
-- title:
--   Zero-free region foundations: RowCompletion.ControlledPrimeStrata [0285_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.ControlledPrimeStrata
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/ControlledPrimeStrata.lean#L144-L280

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0131
import Definitions.Def_PNT_ZeroFree_433_0132
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel1
import Definitions.Def_PNT_ZeroFree_433_0154_parallel1
import Definitions.Def_PNT_ZeroFree_433_0159_parallel1
import Definitions.Def_PNT_ZeroFree_433_0178_parallel1
import Definitions.Def_PNT_ZeroFree_433_0189_parallel1
import Definitions.Def_PNT_ZeroFree_433_0194_parallel1
import Definitions.Def_PNT_ZeroFree_433_0196_parallel1
import Definitions.Def_PNT_ZeroFree_433_0199_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel2
import Definitions.Def_PNT_ZeroFree_433_0227_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel2
import Definitions.Def_PNT_ZeroFree_433_0248_parallel1
import Definitions.Def_PNT_ZeroFree_433_0253_parallel1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0266_parallel1
import Definitions.Def_PNT_ZeroFree_433_0270_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/ControlledPrimeStrata.lean
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

open scoped BigOperators Classical

namespace CanonicalRowCompletion
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O


lemma actualSextic_power_transport (P R:Ideal Eis) [P.IsMaximal] [R.IsMaximal]
    (hP:lambda∉P) (hR:lambda∉R) (he:P=R) (j:ℕ) (n:Eis) :
    (actualSextic P hP^j) (Ideal.Quotient.mk P n)=
      (actualSextic R hR^j) (Ideal.Quotient.mk R n) := by
  subst R
  rfl


end CanonicalRowCompletion

namespace FixedRayActiveSet

theorem fourier_inversion_by_active_set {ι:Type*} [Fintype ι]
    (F:ι→Type*) [∀i,Field (F i)] [∀i,Fintype (F i)]
    (ψ:∀i,AddChar (F i) ℂ) (hψ:∀i,(ψ i).IsPrimitive)
    (φ:∀i,F i→ℂ) (x:∀i,F i) :
    (∏i,φ i (x i))=
      ∑A∈(Finset.univ:Finset ι).powerset,
        (∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0)*
        (∑v:∀i:A,(F i.val)ˣ,
          (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
            (∏i:A,ψ i.val ((v i:F i.val)*x i.val))) := by
  let f:=fun i (a:F i)=>CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) a*ψ i (a*x i)
  have he: (∑h:∀i,F i,∏i,f i (h i))=∏i,φ i (x i):=by
    rw [←Fintype.prod_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact CubicEisenstein.finiteAdditiveFourier_inversion (ψ i) (hψ i) (φ i) (x i)
  rw [←he,sum_by_active_strata]
  apply Finset.sum_congr rfl
  intro A hA
  rw [sum_active_stratum]
  have hz:(∏i∈(Finset.univ:Finset ι)\A,f i 0)=
      ∏i∈(Finset.univ:Finset ι)\A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i) (φ i) 0:=by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [f,zero_mul,AddChar.map_zero_eq_one,mul_one]
  rw [hz,mul_comm]
  congr 1
  rw [show (∑v:∀i:A,(F i.val)ˣ,
      (∏i:A,CubicEisenstein.finiteAdditiveFourierCoeff (ψ i.val) (φ i.val) (v i)) *
        (∏i:A,ψ i.val ((v i:F i.val)*x i.val)))=
      ∑v:∀i:A,(F i.val)ˣ,∏i:A,f i.val (v i) by
    apply Finset.sum_congr rfl
    intro v hv
    exact (Finset.prod_mul_distrib).symm]
  calc
    _=∏i:A,∑u:(F i.val)ˣ,f i.val (u:F i.val):=
      (Finset.prod_coe_sort A (fun i=>∑u:(F i)ˣ,f i (u:F i))).symm
    _=_:=Fintype.prod_sum (fun (i:A) (u:(F i.val)ˣ)=>f i.val (u:F i.val))

end FixedRayActiveSet

open scoped BigOperators Classical ContDiff

namespace CubicEisenstein


open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma theta_lifted_phase (c:Eis) (hc:c≠0) (lift n:Eis) :
    ShortDraftTrace.breveE (-cuspFrequency n*(eisLam^2*eisEmbedding lift/eisEmbedding c))=
      quotientTrace c hc (Ideal.Quotient.mk _ lift*Ideal.Quotient.mk _ n) := by
  rw [←map_mul]
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  congr 1
  unfold cuspFrequency
  rw [map_mul]
  have hc0:=eisEmbedding_ne_zero hc
  have hl:=eisLam_ne_zero
  field_simp
  linear_combination -(eisEmbedding n*eisEmbedding lift)*TraceLambdaPhase.eisLam_sq


end CubicEisenstein


end

end OAI

end


