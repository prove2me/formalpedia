-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0285_parallel1
-- name    : PNT_ZeroFree_433_0285_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:42:50.030602+00:00
-- url     : https://prove2.me/theorems/fcb88cdb-4f8e-4d5f-88ab-674b81665c9c
-- title:
--   Zero-free region foundations: RowCompletion.ControlledPrimeStrata [0285_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.RowCompletion.ControlledPrimeStrata
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/RowCompletion/ControlledPrimeStrata.lean#L282-L365

import Definitions.Def_PNT_ZeroFree_433_0285_parallel1_1

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


open scoped BigOperators Classical ContDiff

namespace CubicEisenstein


open scoped BigOperators Classical MatrixGroups

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CubicKubota
local notation "Eis" => ActualEisensteinCubic.O


lemma breveE_finset_sum {ι:Type*} (s:Finset ι) (z:ι→ℂ) :
    ShortDraftTrace.breveE (∑i∈s,z i)=∏i∈s,ShortDraftTrace.breveE (z i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,Finset.prod_empty,AddChar.map_zero_eq_one]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,AddChar.map_add_eq_mul,ih]


end CubicEisenstein

open scoped BigOperators Classical ContDiff

namespace CompletedGauss
open ActualEisensteinCubic CubicEisenstein CompletedDyadic
local notation "Eis" => ActualEisensteinCubic.O

def unextractedCuspCoefficient {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ) (m:ℕ) (I J:Ideal Eis) : ℂ :=
  σ m*η m I J*reflectedBranch P hg j e (primaryGenerator I) (primaryGenerator J)/
    ((ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ):ℝ):ℂ)

lemma unextractedCuspCoefficient_norm {ι:Type*} [Fintype ι]
    (P:ι→Ideal Eis) [∀i,(P i).IsMaximal] (hg:∀i,lambda∉P i)
    (j:ι→ℕ) (e:ι→Fin 3) (ρ q:ℝ) (hρ:0<ρ) (hq:1≤q)
    (η:ℕ→Ideal Eis→Ideal Eis→ℂ) (σ:ℕ→ℂ)
    (hη:∀m I J,‖η m I J‖≤1) (hσ:∀m,‖σ m‖≤1)
    (m:ℕ) (I J:NonzeroDualIdeal) :
    ‖unextractedCuspCoefficient P hg j e ρ q η σ m I.val J.val‖≤
      (Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
        Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ))/ρ := by
  let C:ℝ:=Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
  have hC:0≤C:=by dsimp only [C];positivity
  have hr:0<ramifiedScale ρ q m:=ramifiedScale_pos ρ q hρ (lt_of_lt_of_le zero_lt_one hq) m
  have hn:1≤(Ideal.absNorm I.val:ℝ):=norm_at_least_one I.val I.property
  have hb:1≤(Ideal.absNorm J.val:ℝ):=norm_at_least_one J.val J.property
  have hs:1≤Real.sqrt (Ideal.absNorm I.val:ℝ):=by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    simpa using hn
  have hd:ρ≤ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ)*(Ideal.absNorm J.val:ℝ) := by
    calc
      ρ≤ramifiedScale ρ q m:=le_mul_of_one_le_right hρ.le (one_le_pow₀ hq)
      _≤ramifiedScale ρ q m*Real.sqrt (Ideal.absNorm I.val:ℝ):=le_mul_of_one_le_right hr.le hs
      _≤_:=le_mul_of_one_le_right (by positivity) hb
  have hp:‖σ m‖*‖η m I.val J.val‖≤1:=(mul_le_of_le_one_left (norm_nonneg _)
    (hσ m)).trans (hη m I.val J.val)
  have hh:‖σ m‖*‖η m I.val J.val‖*
      ‖reflectedBranch P hg j e (primaryGenerator I.val) (primaryGenerator J.val)‖≤C := by
    have ht:=mul_le_mul hp (reflectedBranch_norm_bound P hg j e (primaryGenerator I.val) (primaryGenerator J.val))
      (norm_nonneg _) zero_le_one
    simpa only [one_mul] using ht
  rw [unextractedCuspCoefficient,norm_div,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  exact (div_le_div_of_nonneg_right hh (by positivity)).trans
    (div_le_div_of_nonneg_left hC hρ hd)


end CompletedGauss


end

end OAI

end


