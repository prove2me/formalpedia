-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1
-- name    : PNT_ZeroFree_433_0224_parallel1_1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:56:16.067992+00:00
-- url     : https://prove2.me/theorems/43dcaec1-1e22-4627-b216-cd89bffd67ae
-- title:
--   Zero-free region foundations: Eisenstein.ScatteringResidues [0224_parallel1_1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ScatteringResidues
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringResidues.lean#L85-L486

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0008
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0015
import Definitions.Def_PNT_ZeroFree_433_0019
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1
import Definitions.Def_PNT_ZeroFree_433_0068_1_1_1
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0085
import Definitions.Def_PNT_ZeroFree_433_0100
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0220_parallel1
import Definitions.Def_PNT_ZeroFree_433_0221_parallel2
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringResidues.lean
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

lemma scalar_residue_sub_continuous (f g : ℂ→ℂ) (z r : ℂ)
    (hf : Tendsto (fun s => (s-z)*f s) (𝓝[≠] z) (𝓝 r)) (hg : ContinuousAt g z) :
    Tendsto (fun s => (s-z)*(f s-g s)) (𝓝[≠] z) (𝓝 r) := by
  have hlin : Tendsto (fun s : ℂ => s-z) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [id_eq,sub_self] using (tendsto_id.sub_const z).mono_left
      (show 𝓝[≠] z≤𝓝 z from nhdsWithin_le_nhds)
  have hz : Tendsto (fun s => (s-z)*g s) (𝓝[≠] z) (𝓝 (0:ℂ)) := by
    simpa only [zero_mul] using hlin.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [mul_sub,sub_zero] using hf.sub hz


local notation "O" => ActualEisensteinCubic.O


end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O


lemma periodDomain_integrable_of_continuous (f : ℂ→ℂ) (hf : Continuous f) :
    IntegrableOn f periodDomain volume := by
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:ℂ) (∑i,‖periodBasis i‖))).mono_set
  intro z hz
  simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz


end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding


section ProductSections
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {«μ» : Measure α} {ν : Measure β} [SFinite «μ»] [SFinite ν]

lemma complex_memLp_two_sections {f : α × β → ℂ} (hf : MemLp f 2 («μ».prod ν)) :
    ∀ᵐx ∂«μ», MemLp (fun y => f (x,y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    hf.norm.integrable_sq.prod_right_ae] with x hx hi
  exact (memLp_two_iff_integrable_sq_norm hx).mpr hi

end ProductSections


end

section

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma third_character_eq_one_iff_basis (ψ:AddChar (Eis⧸Ideal.span {(3:Eis)}) ℂ) :
    ψ=1 ↔ ψ (Ideal.Quotient.mk _ (1:Eis))=1 ∧
      ψ (Ideal.Quotient.mk _ omega)=1 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h1,hw⟩
    ext x
    obtain ⟨z,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [←ActualEisensteinCoordinates.eval_coords z]
    change ψ (Ideal.Quotient.mk _
      (((ActualEisensteinCoordinates.coords z).1:Eis)+
       ((ActualEisensteinCoordinates.coords z).2:Eis)*omega))=1
    rw [map_add,AddChar.map_add_eq_mul]
    have hA:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        ((ActualEisensteinCoordinates.coords z).1:Eis)=
        (ActualEisensteinCoordinates.coords z).1 • Ideal.Quotient.mk _ (1:Eis):=by
      rw [←map_zsmul]
      simp
    have hB:Ideal.Quotient.mk (Ideal.span {(3:Eis)})
        (((ActualEisensteinCoordinates.coords z).2:Eis)*omega)=
        (ActualEisensteinCoordinates.coords z).2 • Ideal.Quotient.mk _ omega:=by
      rw [←map_zsmul]
      simp only [zsmul_eq_mul]
    rw [hA,hB,AddChar.map_zsmul_eq_zpow,AddChar.map_zsmul_eq_zpow,h1,hw]
    simp


end


end CubicEisenstein

end

end OAI

end


