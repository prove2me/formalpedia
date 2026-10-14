-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1
-- name    : PNT_ZeroFree_433_0224_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:57:17.774114+00:00
-- url     : https://prove2.me/theorems/bcafb2c9-bd4d-4dee-8b36-4e301f5401fa
-- title:
--   Zero-free region foundations: Eisenstein.ScatteringResidues [0224_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.ScatteringResidues
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/ScatteringResidues.lean#L488-L521

import Definitions.Def_PNT_ZeroFree_433_0224_parallel1_1_1

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

open scoped BigOperators Classical
open EisensteinEmbedding (omega3)
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss CubicRamified
local notation "Eis" => ActualEisensteinCubic.O


lemma omega3_pow_exp_eq_one_iff (t:ℕ) (b:ℤ) :
    omega3^t*Complex.exp (2*Real.pi*Complex.I*(b:ℂ)/3)=1 ↔
      (3:ℤ)∣(t:ℤ)+b := by
  have hω:omega3=Complex.exp (2*Real.pi*Complex.I/3):=by
    rw [←TraceLambdaPhase.exp_minus_four_pi_div_three]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1,?_⟩
    push_cast
    ring
  rw [hω,←Complex.exp_nat_mul,←Complex.exp_add]
  have he:(t:ℂ)*(2*Real.pi*Complex.I/3)+2*Real.pi*Complex.I*(b:ℂ)/3=
      2*Real.pi*Complex.I*(((t:ℤ)+b:ℤ):ℂ)/3:=by push_cast;ring
  rw [he]
  constructor
  · intro hh
    have hh':Complex.exp (2*Real.pi*Complex.I*((((t:ℤ)+b:ℤ):ℂ)/3))=1:=by
      convert! hh using 1 ;ring_nf
    obtain ⟨v,hv⟩:=GeneralPrimitiveTrace.complex_exp_trace_integer hh'
    have hc:(((t:ℤ)+b:ℤ):ℂ)=3*(v:ℂ):=by linear_combination 3*hv
    have hi:(t:ℤ)+b=3*v:=by exact_mod_cast hc
    exact ⟨v,hi⟩
  · rintro ⟨v,hv⟩
    rw [hv]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨v,?_⟩
    push_cast
    ring

lemma eisEmbedding_omega_actual : eisEmbedding omega=omega3 := by
  have hω:omega=ActualEisensteinCoordinates.eval 0 1:=by
    simp only [ActualEisensteinCoordinates.eval,Int.cast_zero,Int.cast_one,zero_add,one_mul]
    rfl
  rw [hω,eisEmbedding_eval]
  norm_num


end


end CubicEisenstein

end

end OAI

end


