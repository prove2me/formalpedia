-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0250_parallel1
-- name    : PNT_ZeroFree_433_0250_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:05:01.056484+00:00
-- url     : https://prove2.me/theorems/d0a67a49-b78e-4920-b233-7caf9ef0e45f
-- title:
--   Zero-free region foundations: Eisenstein.CorrespondenceTests [0250_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CorrespondenceTests
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondenceTests.lean#L84-L631

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0134
import Definitions.Def_PNT_ZeroFree_433_0141
import Definitions.Def_PNT_ZeroFree_433_0143
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0247_parallel1
import Definitions.Def_PNT_ZeroFree_433_0247_parallel2
import Definitions.Def_PNT_ZeroFree_433_0249_parallel3
import Definitions.Def_PNT_ZeroFree_433_0249_parallel3_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CorrespondenceTests.lean
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


open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O

lemma cubePrime_norm_ge_one (p:Eis) (hp:p≠0) : 1≤‖eisEmbedding p‖ := by
  have hn:1≤‖eisEmbedding p‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    have hq:Ideal.absNorm (Ideal.span {p})≠0:=
      (Ideal.absNorm_ne_zero_iff _).mpr (finite_quotient_span hp)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  nlinarith [norm_nonneg (eisEmbedding p)]


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


end CubicEisenstein

end

end OAI

end


