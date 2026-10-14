-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0200_parallel1
-- name    : PNT_ZeroFree_433_0200_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:33:22.443516+00:00
-- url     : https://prove2.me/theorems/c87085cf-d959-4202-822b-bfe05ec0b553
-- title:
--   Zero-free region foundations: Eisenstein.FredholmAlternative [0200_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.FredholmAlternative
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FredholmAlternative.lean#L87-L468

import Mathlib.Analysis.Normed.Module.Complemented
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0131
import Definitions.Def_PNT_ZeroFree_433_0132
import Definitions.Def_PNT_ZeroFree_433_0144_parallel1
import Definitions.Def_PNT_ZeroFree_433_0159_parallel1
import Definitions.Def_PNT_ZeroFree_433_0178_parallel1
import Definitions.Def_PNT_ZeroFree_433_0189_parallel1
import Definitions.Def_PNT_ZeroFree_433_0192_parallel1
import Definitions.Def_PNT_ZeroFree_433_0194_parallel1
import Definitions.Def_PNT_ZeroFree_433_0196_parallel1
import Definitions.Def_PNT_ZeroFree_433_0199_parallel1
import Definitions.Def_PNT_ZeroFree_433_0215_parallel2
import Definitions.Def_PNT_ZeroFree_433_0227_parallel2
import Definitions.Def_PNT_ZeroFree_433_0230_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel1
import Definitions.Def_PNT_ZeroFree_433_0243_parallel2
import Definitions.Def_PNT_ZeroFree_433_0248_parallel1
import Definitions.Def_PNT_ZeroFree_433_0253_parallel1
import Definitions.Def_PNT_ZeroFree_433_0263_parallel2
import Definitions.Def_PNT_ZeroFree_433_0266_parallel1
import Definitions.Def_PNT_ZeroFree_433_0270_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/FredholmAlternative.lean
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

section

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma ker_orthogonal_restriction_injective (T : E→L[ℂ]F) :
    Function.Injective (T.domRestrict T.kerᗮ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply Subtype.ext
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact T.ker.inner_right_of_mem_orthogonal hu u.2

lemma ker_orthogonal_restriction_range (T : E→L[ℂ]F) :
    Set.range (T.domRestrict T.kerᗮ)=Set.range T := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  apply Set.Subset.antisymm
  · rintro _ ⟨u,rfl⟩
    exact ⟨u.1,rfl⟩
  · rintro _ ⟨u,rfl⟩
    refine ⟨⟨u-T.ker.starProjection u,T.ker.sub_starProjection_mem_orthogonal u⟩,?_⟩
    change T (u-T.ker.starProjection u)=T u
    rw [map_sub]
    have hz : T (T.ker.starProjection u)=0 := T.ker.starProjection_apply_mem u
    rw [hz,sub_zero]

lemma ker_orthogonal_restriction_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.domRestrict T.kerᗮ) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  apply antilipschitz_of_injective_compact_estimate (T.domRestrict T.kerᗮ)
    (K.domRestrict T.kerᗮ) (hK.comp_clm T.kerᗮ.subtypeL) A B
      (fun u => hest u) (ker_orthogonal_restriction_injective T)

lemma closed_range_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : IsClosed (Set.range T) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  rw [←ker_orthogonal_restriction_range T]
  exact hD.isClosed_range (T.domRestrict T.kerᗮ).uniformContinuous

lemma selfAdjoint_range_eq_ker_orthogonal (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (hrange : IsClosed (Set.range T)) : T.range=T.kerᗮ := by
  have hh := T.orthogonal_ker
  rw [hT.adjoint_eq] at hh
  rw [hrange.submodule_topologicalClosure_eq] at hh
  exact hh.symm

end

section
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma selfAdjoint_fredholm_of_compact_estimate (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (K : E→L[ℂ]G) (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : T.IsFredholm := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : FiniteDimensional ℂ T.ker := finiteDimensional_ker_of_compact_estimate T K hK A B hest
  let : T.kerᗮ.CoFG :=
    (T.kerᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm).symm.finiteDimensional
  have hrange := closed_range_of_compact_estimate T K hK A B hest
  have heq := selfAdjoint_range_eq_ker_orthogonal T hT hrange
  let : T.range.CoFG := heq.symm ▸ (inferInstance : T.kerᗮ.CoFG)
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  have hstrict : Topology.IsStrictMap T :=
    ((T.isStrictMap_isClosed_range_iff_restrict T.kerᗮ T.ker.isClosed_orthogonal).mpr
      ⟨(hD.isClosedEmbedding (T.domRestrict T.kerᗮ).uniformContinuous).isEmbedding.isStrictMap,
       by
         change IsClosed (Set.range (T.domRestrict T.kerᗮ))
         exact hD.isClosed_range (T.domRestrict T.kerᗮ).uniformContinuous⟩).1
  exact {
    isStrictMap := hstrict
    isClosed_range := hrange
    finite_ker := inferInstance
    finite_coker := inferInstance
    closedComplemented_ker := Submodule.ClosedComplemented.of_isCompl_isClosed T.ker.isCompl_orthogonal
      T.isClosed_ker T.ker.isClosed_orthogonal
  }

end


lemma scalar_compact_energy_estimate (m g n t k spectralParam C : ℝ)
    (_hn : 0≤n) (_ht : 0≤t) (hspectralParam : 0≤spectralParam) (hspectralParamone : spectralParam<1) (hC : 0≤C)
    (hspace : n^2=m^2+g^2) (hcore : m^2≤g^2+C*k^2)
    (hform : g^2-spectralParam*m^2≤n*t) :
    n^2≤(4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2 := by
  have hd : 0<1-spectralParam := sub_pos.mpr hspectralParamone
  have hlow : (1-spectralParam)/2*n^2≤n*t+C*k^2 := by
    nlinarith [mul_nonneg (show 0≤1+spectralParam by linarith) (sub_nonneg.mpr hcore),
      mul_nonneg hd.le (mul_nonneg hC (sq_nonneg k))]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0≤4*(1-spectralParam) by positivity)
  have hsq : (1-spectralParam)^2*n^2≤4*t^2+4*(1-spectralParam)*C*k^2 := by
    nlinarith [sq_nonneg ((1-spectralParam)*n-2*t)]
  have he : (4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2=
      (4*t^2+4*(1-spectralParam)*C*k^2)/(1-spectralParam)^2 := by
    field_simp [hd.ne']
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by nlinarith [hsq])


end CubicEisenstein


namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

theorem halfCanonicalPadding_budget (ε C : ℝ) (hε : 0<ε) (hC : 0≤C) :
    0<canonicalPadding ε C/2 ∧ canonicalPadding ε C/2≤(1:ℝ)/1000 ∧
    3000*(canonicalPadding ε C/2)≤(1:ℝ)/80 ∧
    3001*C*(canonicalPadding ε C/2)≤ε/2 := by
  have h:=canonicalPadding_budget ε C hε hC
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  have hceta : 0≤3001*C*canonicalPadding ε C :=
    mul_nonneg (mul_nonneg (by norm_num) hC) h.1.le
  nlinarith [h.2.2.2.2.1]


end SecondPassArithmetic


open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss
open ActualEisensteinCubic

theorem shortCompletedSum_nonpos (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (hH : H₀≤0) :
    shortCompletedSum Ψ W X H₀=0 := by
  unfold shortCompletedSum
  calc
    _ = ∑'I : Ideal ActualEisensteinCubic.O,(0:ℂ) := tsum_congr (fun I=>if_neg (not_lt_of_ge (hH.trans (Nat.cast_nonneg (Ideal.absNorm I)))))
    _ = 0 := tsum_zero

end CompletedGauss


end

end OAI

end


