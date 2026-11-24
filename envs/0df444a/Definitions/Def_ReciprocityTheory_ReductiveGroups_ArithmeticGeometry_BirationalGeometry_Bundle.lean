-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:34.552053+00:00
-- url     : https://prove2.me/theorems/0aa50633-ad42-4e96-9fa0-23149cfc451a
-- title:
--   Bundle
-- statement:
--   Definitions and structural lemmas for Bundle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/Bundle.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
section Chart
variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}
def chartRing (x : ι → Ω) (i : ι) : Subalgebra o Ω :=
  Algebra.adjoin o (Set.range fun j => x j / x i)
structure ChartBundle (x : ι → Ω) (r : ℕ) (E : Type*) [AddCommGroup E] [Module Ω E] where

  lat : ι → AddSubgroup E

  stable : ∀ i, ∀ a ∈ chartRing o x i, ∀ e ∈ lat i, a • e ∈ lat i

  frame : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing o x i) ∧
    (∀ l, c l ∈ chartRing o x i) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ lat i) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing o x i) ∧ e = ∑ q, a q • b q

  overlap : ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ lat i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ lat j
variable {o}
def globalSec {x : ι → Ω} {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o x r E) : AddSubgroup E :=
  ⨅ (i) (_ : x i ≠ 0), B.lat i
theorem div_mem_chartRing (x : ι → Ω) (i j : ι) :
    x j / x i ∈ chartRing o x i :=
  Algebra.subset_adjoin ⟨j, rfl⟩
theorem exists_pow_mul_mem_chartRing (x : ι → Ω) (i j : ι) (hi : x i ≠ 0)
    {a : Ω} (ha : a ∈ chartRing o x i) :
    ∃ m : ℕ, (x i / x j) ^ m * a ∈ chartRing o x j := by
  have hij : x i / x j ∈ chartRing o x j := div_mem_chartRing x j i
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : x i / x j * (x k / x i) = x k / x j := by field_simp
    rw [pow_one, this]
    exact div_mem_chartRing x j k
  | algebraMap r =>
    exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y + z) =
        (x i / x j) ^ n * ((x i / x j) ^ m * y) + (x i / x j) ^ m * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hij _) hm) (mul_mem (pow_mem hij _) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : (x i / x j) ^ (m + n) * (y * z) = ((x i / x j) ^ m * y) * ((x i / x j) ^ n * z) := by
      ring
    rw [this]
    exact mul_mem hm hn
variable (o)
def lineLat (x : ι → Ω) (d : ℕ) (i : ι) : AddSubgroup Ω :=
  ((Subalgebra.toSubmodule (chartRing o x i)).map (LinearMap.mulRight o (x i ^ d))).toAddSubgroup
variable {o}
theorem mem_lineLat (x : ι → Ω) (d : ℕ) (i : ι) (e : Ω) :
    e ∈ lineLat o x d i ↔ ∃ a ∈ chartRing o x i, a * x i ^ d = e := by
  simp [lineLat]
variable (o)
def lineBundle (x : ι → Ω) (d : ℕ) : ChartBundle o x 1 Ω where
  lat := lineLat o x d
  stable i a ha e he := by
    obtain ⟨c, hc, rfl⟩ := (mem_lineLat x d i e).1 he
    refine (mem_lineLat x d i _).2 ⟨a * c, mul_mem ha hc, ?_⟩
    rw [smul_eq_mul, mul_assoc]
  frame i hi := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    refine ⟨fun _ => x i ^ d, ?_, ?_, ?_⟩
    · rw [linearIndependent_unique_iff]
      exact pow_ne_zero _ hi
    · rw [Set.range_const]
      exact Ideal.span_singleton_eq_top.2 (isUnit_iff_ne_zero.2 (pow_ne_zero _ hi))
    · intro e
      rw [mem_lineLat]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨fun _ => a, fun _ => ha, by simp⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a 0, ha 0, by simp⟩
  overlap i j hi hj e he := by
    obtain ⟨a, ha, rfl⟩ := (mem_lineLat x d i e).1 he
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_chartRing x i j hi ha
    refine ⟨m, (mem_lineLat x d j _).2 ⟨(x i / x j) ^ m * a * (x i / x j) ^ d,
      mul_mem hm (pow_mem (div_mem_chartRing x j i) _), ?_⟩⟩
    rw [smul_eq_mul, div_pow, div_pow]
    field_simp
end Chart
end ReciprocityTheory.ChartRestriction.G.Geo


