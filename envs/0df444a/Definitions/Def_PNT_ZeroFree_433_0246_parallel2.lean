-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0246_parallel2
-- name    : PNT_ZeroFree_433_0246_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:40:05.426298+00:00
-- url     : https://prove2.me/theorems/915aadcd-a136-4f38-801a-87b0d773ee93
-- title:
--   Zero-free region foundations: Eisenstein.IntegralCover [0246_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.IntegralCover
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/IntegralCover.lean#L89-L660

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel2
import Definitions.Def_PNT_ZeroFree_433_0134
import Definitions.Def_PNT_ZeroFree_433_0137
import Definitions.Def_PNT_ZeroFree_433_0180_parallel2
import Definitions.Def_PNT_ZeroFree_433_0200_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0236_parallel2
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel2
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0243_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0244_parallel3
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0251_parallel1
import Definitions.Def_PNT_ZeroFree_433_0257_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel2
import Definitions.Def_PNT_ZeroFree_433_0267_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel3

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/IntegralCover.lean
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
open MeasureTheory Filter
open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


lemma onceCusp_q_as_scale (t:Eisˣ) (l:Fin 3) :
    onceCuspScale (t*ramifiedOmegaUnit^l.val)=onceCuspScale t*omega^l.val := by
  simp only [onceCuspScale,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
  ring

lemma onceCusp_q_congr_scale (t:Eisˣ) (l:Fin 3) :
    (3:Eis)∣onceCuspScale t*omega^l.val-onceCuspScale t := by
  obtain ⟨b,hb⟩:=halfPrimary_omega_pow l.val
  have he:onceCuspScale t*omega^l.val-onceCuspScale t=
      (onceCuspScale t*(omega-1))*b:=by
    linear_combination onceCuspScale t*hb
  rw [he]
  exact (onceCusp_scale_lambda t).mul_right b

lemma onceCusp_q_dvd_three (t:Eisˣ) (l:Fin 3) :
    onceCuspScale t*omega^l.val∣(3:Eis) := by
  rw [←onceCusp_q_as_scale]
  exact ⟨onceCuspComplement _,(onceCusp_scale_complement _).symm⟩

lemma onceCusp_q_trace_dvd (t:Eisˣ) (l:Fin 3) :
    (3:Eis)∣ramifiedTraceLambda*(onceCuspScale t*omega^l.val) := by
  refine ⟨-(t:Eis)*omega^l.val,?_⟩
  unfold onceCuspScale
  linear_combination (t:Eis)*omega^l.val*ramifiedTraceLambda_square

lemma onceCusp_q_dvd_frequency (t:Eisˣ) (l:Fin 3) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) : onceCuspScale t*omega^l.val∣h := by
  have hd:(3:Eis)∣h-onceCuspScale t*omega^l.val:=by
    convert! dvd_sub hfreq (onceCusp_q_congr_scale t l) using 1 ;ring
  have hh:onceCuspScale t*omega^l.val∣h-onceCuspScale t*omega^l.val:=
    (onceCusp_q_dvd_three t l).trans hd
  simpa only [sub_add_cancel] using dvd_add hh (dvd_refl (onceCuspScale t*omega^l.val))

lemma onceCusp_period_congruence (t:Eisˣ) (l:Fin 3) (h:Eis) (j:ℕ)
    (hfreq:(3:Eis)∣h-onceCuspScale t) :
    (3:Eis)∣h+ramifiedAffineParameter j 1*(onceCuspScale t*omega^l.val) := by
  have hd:(3:Eis)∣h-onceCuspScale t*omega^l.val:=by
    convert! dvd_sub hfreq (onceCusp_q_congr_scale t l) using 1 ;ring
  have ht:=(onceCusp_q_trace_dvd t l).mul_left (j:Eis)
  convert! dvd_add hd ht using 1 ; simp only [ramifiedAffineParameter,Nat.cast_one] ;ring

def onceCuspFrequencyQuotient (t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (l:Fin 3) : Eis :=
  Classical.choose (onceCusp_q_dvd_frequency t l h hfreq)

lemma onceCuspFrequencyQuotient_spec (t:Eisˣ) (h:Eis)
    (hfreq:(3:Eis)∣h-onceCuspScale t) (l:Fin 3) :
    h=(onceCuspScale t*omega^l.val)*onceCuspFrequencyQuotient t h hfreq l :=
  Classical.choose_spec (onceCusp_q_dvd_frequency t l h hfreq)


lemma onceCuspRayIndex_spec (u t:Eisˣ) (l:Fin 3) :
    (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=omega^(onceCuspRayIndex u t l).val*ramifiedTraceLambda ∨
      (↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=-(omega^(onceCuspRayIndex u t l).val*ramifiedTraceLambda) := by
  have he:(↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val)=
      (onceCuspRayUnit u t l:Eis)*ramifiedTraceLambda:=by
    simp only [onceCuspRayUnit,onceCuspScale,Units.val_mul,Units.val_pow_eq_pow_val,ramifiedOmegaUnit_val]
    ring
  have hh:=Classical.choose_spec (unit_eq_sign_omega (onceCuspRayUnit u t l))
  change (onceCuspRayUnit u t l:Eis)=omega^(onceCuspRayIndex u t l).val ∨
    (onceCuspRayUnit u t l:Eis)=-(omega^(onceCuspRayIndex u t l).val) at hh
  rw [he]
  rcases hh with hh|hh
  · exact Or.inl (by rw [hh])
  · exact Or.inr (by rw [hh];ring)

def onceCuspGaussSeries (u t:Eisˣ) (h:Eis) (hfreq:(3:Eis)∣h-onceCuspScale t) (s:ℂ) : ℂ :=
  ∑l:Fin 3,if (3:Eis)∣onceCuspFrequencyQuotient t h hfreq l+
    ramifiedAffineParameter (onceCuspRayIndex u t l).val 1 then
      (3:ℂ)*(3:ℂ)^(-s)*ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding (onceCuspScale t*omega^l.val))*
        unramifiedCubicGaussSeries s
          (3*((↑u⁻¹:Eis)^2*(onceCuspScale t*omega^l.val))^2*onceCuspFrequencyQuotient t h hfreq l) else 0


end


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding


end CubicEisenstein


open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O


lemma integralCoverMap_measurable {H K : Subgroup (SL(2,ActualEisensteinCubic.O))} (hHK : H≤K) :
    Measurable (integralCoverMap hHK) := by
  apply measurable_from_quotient.mpr
  exact measurable_integralOrbitProjection K


def integralCoverSheet (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) : Set HyperbolicSpace :=
  (fun w=>integralCoverRep H K q • w) ⁻¹' hyperbolicFundamentalSet K

def integralCoverDomain (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) : Set HyperbolicSpace :=
  ⋃q : IntegralCoverCosets H K,integralCoverSheet H K q

lemma integralCoverSheet_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K) :
    MeasurableSet (integralCoverSheet H K q) :=
  (measurable_const_smul (integralCoverRep H K q)) (hyperbolicFundamentalSet_measurable K)

lemma integralCoverDomain_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K] :
    MeasurableSet (integralCoverDomain H K) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  exact MeasurableSet.iUnion (integralCoverSheet_measurable H K)

lemma fundamental_reduction_unique (K : Subgroup (SL(2,ActualEisensteinCubic.O))) (hK : K≤CubicKubota.levelThree)
    (r s : K) (w : HyperbolicSpace) (hr : r•w∈hyperbolicFundamentalSet K)
    (hs : s•w∈hyperbolicFundamentalSet K) : r=s := by
  have he : s•w=r•w := by
    have hh := hyperbolicFundamentalSet_orbit_unique K (r•w) hr (s*r⁻¹)
      (by simpa only [mul_smul,inv_smul_smul] using hs)
    simpa only [mul_smul,inv_smul_smul] using hh
  have hfix : (r⁻¹*s)•w=w := by rw [mul_smul,he,inv_smul_smul]
  exact inv_mul_eq_one.mp (subgroup_action_free K hK _ w hfix)

lemma integralCoverSheet_pairwiseDisjoint (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hK : K≤CubicKubota.levelThree) : Pairwise (fun q r=>Disjoint (integralCoverSheet H K q) (integralCoverSheet H K r)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro w hwq hwr
  have he := fundamental_reduction_unique K hK (integralCoverRep H K q)
    (integralCoverRep H K r) w hwq hwr
  apply hqr
  exact Quotient.out_injective he


lemma integralCover_inclusion_smul {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (h : H) (w : HyperbolicSpace) :
    (Subgroup.inclusion hHK h)•w=h•w := rfl


end CubicEisenstein

end

end OAI

end


