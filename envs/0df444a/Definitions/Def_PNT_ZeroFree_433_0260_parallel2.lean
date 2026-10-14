-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0260_parallel2
-- name    : PNT_ZeroFree_433_0260_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:21:42.176341+00:00
-- url     : https://prove2.me/theorems/1b985403-26fe-44af-9931-029814ef0874
-- title:
--   Zero-free region foundations: Eisenstein.SourceMellinInversion [0260_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean#L435-L569

import Definitions.Def_PNT_ZeroFree_433_0260_parallel2_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SourceMellinInversion.lean
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
open scoped Classical BigOperators Topology

namespace CompletedGauss


open Filter MeasureTheory
open scoped Classical BigOperators Topology ContDiff

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O


theorem completedT_initial_mellin (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hWc : HasCompactSupport W :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  rw [completedT_eq_mellin_index Ψ W hWc X hX]
  have h := weightedMellin_inversion completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2)
    (completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num))
    (Vstar W) a b ha (Vstar_support W a b hsupp) (Vstar_contDiff W a b ha hsupp hW) X hX
  have hd (t : ℝ) : completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
    unfold completedDirichletSeries
    apply tsum_congr
    intro p
    congr 2
    ring
  simpa only [hd,Complex.ofReal_div,Complex.ofReal_ofNat] using h

end

section
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O


lemma completedDirichletTerm_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) (p : CompletedMellinIndex) :
    completedMellinCoefficient Ψ p*(completedMellinLength p:ℂ)^(1/2-s)=
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  have ha : Ideal.absNorm p.1.1≠0 := fun h=>p.1.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hb : Ideal.absNorm p.2.1≠0 := fun h=>p.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  unfold completedMellinCoefficient completedMellinLength
  change (columnWeight Ψ p.1.1/(Real.sqrt (Ideal.absNorm p.1.1:ℝ):ℂ)*
    (star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3/(Ideal.absNorm p.2.1:ℂ)))*
    (((Ideal.absNorm p.1.1:ℝ)*(Ideal.absNorm p.2.1:ℝ)^3:ℝ):ℂ)^(1/2-s)=_
  rw [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_natCast]
  rw [nat_half_shift_product _ _ ha hb]
  ring

theorem completedDirichletSeries_expanded (Ψ : ActualEisensteinCubic.O→*ℂ) (s : ℂ) :
    completedDirichletSeries Ψ s=∑'p : CompletedMellinIndex,
      columnWeight Ψ p.1.1*star (FiniteGaussPhase.angularFactor (primaryGenerator p.2.1))^3*
      Ψ (primaryGenerator p.2.1)^3*(Ideal.absNorm p.2.1:ℂ)^(1/2-3*s)*
      (Ideal.absNorm p.1.1:ℂ)^(-s) := by
  unfold completedDirichletSeries
  exact tsum_congr (completedDirichletTerm_expanded Ψ s)

end

open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O


lemma completedDirichletSeries_initial (Ψ : ActualEisensteinCubic.O→*ℂ) (t : ℝ) :
    completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)=
      ∑'p : CompletedMellinIndex,completedMellinCoefficient Ψ p*
        (completedMellinLength p:ℂ)^(-((3/2:ℂ)+t*Complex.I)) := by
  unfold completedDirichletSeries
  apply tsum_congr
  intro p
  congr 2
  ring

theorem completedT_initial_mellin_integrable (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) :
    Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*
      (X:ℂ)^((3/2:ℂ)+t*Complex.I)*completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I)) := by
  have hsum := completedMellinCoefficient_summable Ψ hΨ (3/2) (by norm_num)
  have hc := weighted_vertical_series_continuous completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hb := weighted_vertical_series_norm completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) (3/2) hsum
  have hmi : Integrable (fun t : ℝ=>mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)) := by
    simpa only [Complex.VerticalIntegrable,Complex.ofReal_div,Complex.ofReal_ofNat] using
      (compactMellin_vertical_integrable (Vstar W) a b ha (Vstar_support W a b hsupp)
        (Vstar_contDiff W a b ha hsupp hW) (3/2))
  have hbase := vertical_power_mul_integrable _ hmi X (3/2) hX
  have hi := hbase.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,completedDirichletSeries_initial,
    mul_comm (mellin (Vstar W) _)] using hi

end CompletedGauss


end

end OAI

end


