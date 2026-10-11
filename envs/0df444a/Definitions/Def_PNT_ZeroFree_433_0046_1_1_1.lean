-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0046_1_1_1
-- name    : PNT_ZeroFree_433_0046_1_1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:45:46.42099+00:00
-- url     : https://prove2.me/theorems/3ffe51c0-cbc8-405a-a75f-22c753d5eaf7
-- title:
--   Zero-free region foundations: GaussSum.SquarePhaseFactorization [0046_1_1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.SquarePhaseFactorization
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean#L72-L143

import Definitions.Def_PNT_ZeroFree_433_0035
import Definitions.Def_PNT_ZeroFree_433_0036
import Definitions.Def_PNT_ZeroFree_433_0044

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/SquarePhaseFactorization.lean
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

namespace ActualEisensteinCubic

theorem primary_associated_eq (x y : O) (hxy : Associated x y)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) : x = y := by
  obtain ⟨u, hu⟩ := hxy
  have huprimary : lambda ^ 2 ∣ (u : O) - 1 := by
    have heq : (u : O) - 1 = (y - 1) - (x - 1) * (u : O) := by
      rw [← hu]
      ring
    rw [heq]
    exact dvd_sub hy (dvd_mul_of_dvd_left hx _)
  have huone : (u : O) = 1 := A3_primary_unit_eq_one _ u.isUnit huprimary
  simpa only [huone, mul_one] using hu

theorem primary_multiset_prod (s : Multiset O)
    (hs : ∀ x ∈ s, lambda ^ 2 ∣ x - 1) : lambda ^ 2 ∣ s.prod - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hb := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.prod_cons]
    have heq : a * s.prod - 1 = (a - 1) * s.prod + (s.prod - 1) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

theorem primary_maximal_divisor_good (t : O) (ht : lambda ^ 2 ∣ t - 1)
    (P : Ideal O) [P.IsMaximal] (htP : t ∈ P) : lambda ∉ P := by
  intro hlam
  have hlam2 : lambda ^ 2 ∈ P := by
    simpa only [pow_two] using P.mul_mem_left lambda hlam
  have hsub : t - 1 ∈ P := Ideal.mem_of_dvd P ht hlam2
  have hone : (1 : O) ∈ P := by simpa using P.sub_mem htP hsub
  exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
    ((Ideal.eq_top_iff_one _).mpr hone)

theorem exists_primary_prime_factorization (t : O) (ht0 : t ≠ 0)
    (ht : lambda ^ 2 ∣ t - 1) :
    ∃ s : Multiset O, s.prod = t ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
  classical
  obtain ⟨f, hf, hft⟩ := UniqueFactorizationMonoid.exists_prime_factors t ht0
  have hfgood : ∀ r ∈ f, lambda ∉ (Ideal.span {r} : Ideal O) := by
    intro r hr
    have hp := hf r hr
    let : (Ideal.span {r} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    apply primary_maximal_divisor_good t ht
    exact Ideal.mem_span_singleton.mpr ((Multiset.dvd_prod hr).trans hft.dvd)
  have hreplace : ∃ s : Multiset O, Associated s.prod f.prod ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
    clear hft
    induction f using Multiset.induction_on with
    | empty => exact ⟨0, Associated.refl _, by simp⟩
    | @cons a f ih =>
      have ha := hf a (Multiset.mem_cons_self _ _)
      let : (Ideal.span {a} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
      obtain ⟨r, hrspan, hrprimary, _⟩ := cubicJacobi_exists_primary_generator
        (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have har : Associated a r := Ideal.span_singleton_eq_span_singleton.mp hrspan
      obtain ⟨s, hsf, hs⟩ := ih
        (fun r hr => hf r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hfgood r (Multiset.mem_cons_of_mem hr))
      refine ⟨r ::ₘ s, ?_, ?_⟩
      · simpa only [Multiset.prod_cons] using har.symm.mul_mul hsf
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨har.prime_iff.mp ha, hrprimary⟩
        · exact hs x hx
  obtain ⟨s, hsf, hs⟩ := hreplace
  refine ⟨s, ?_, hs⟩
  exact primary_associated_eq _ _ (hsf.trans hft)
    (primary_multiset_prod s (fun r hr => (hs r hr).2)) ht


end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT


end IdealGaussCRT

namespace QuadraticGaussRay


open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates


open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates


end QuadraticGaussRay

end

end OAI

end


