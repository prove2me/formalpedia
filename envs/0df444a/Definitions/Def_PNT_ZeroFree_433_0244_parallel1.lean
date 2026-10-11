-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0244_parallel1
-- name    : PNT_ZeroFree_433_0244_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:35:13.867273+00:00
-- url     : https://prove2.me/theorems/c5c3b8fb-c25a-447a-949c-6c76407f7ce3
-- title:
--   Zero-free region foundations: Reciprocity.RamifiedCuspPhases [0244_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reciprocity.RamifiedCuspPhases
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reciprocity/RamifiedCuspPhases.lean#L566-L689

import Definitions.Def_PNT_ZeroFree_433_0244_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
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


open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ConcreteTraceCRT EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O


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


