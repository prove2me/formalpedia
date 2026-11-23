-- Prove2me | Definitions.Def_GroundTheory_FunctionField_PlaceDefs
-- name    : GroundTheory_FunctionField_PlaceDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:09.021584+00:00
-- url     : https://prove2.me/theorems/aeb7a34a-ca92-4ec2-bd65-49f0601571ea
-- title:
--   Place Defs
-- statement:
--   Definitions and structural lemmas for Place Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
section FunctionField
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
class IsFunctionField : Prop where
  exists_transcendental_finiteDimensional :
    ∃ x : K, Transcendental k x ∧ FiniteDimensional (IntermediateField.adjoin k {x}) K
variable {k K}
open scoped IntermediateField.algebraAdjoinAdjoin in

theorem isTranscendenceBasis_singleton {y : K} (hy : Transcendental k y)
    (hfin : FiniteDimensional (IntermediateField.adjoin k {y}) K) :
    IsTranscendenceBasis k ((↑) : ({y} : Set K) → K) := by
  rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
  refine ⟨(algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).2 hy, ?_⟩
  rw [Subtype.range_coe]
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k {y}) K :=
    Algebra.IsAlgebraic.of_finite _ _
  exact Algebra.IsAlgebraic.trans (Algebra.adjoin k {y}) (IntermediateField.adjoin k {y}) K
theorem trdeg_eq_one [IsFunctionField k K] : Algebra.trdeg k K = 1 := by
  obtain ⟨y, hy, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  rw [← (isTranscendenceBasis_singleton hy hfin).cardinalMk_eq_trdeg, Cardinal.mk_singleton]
theorem essFiniteType [IsFunctionField k K] : Algebra.EssFiniteType k K := by
  obtain ⟨y, -, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have : Algebra.EssFiniteType k (IntermediateField.adjoin k {y}) :=
    IntermediateField.essFiniteType_iff.2 (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton y))
  exact Algebra.EssFiniteType.comp k (IntermediateField.adjoin k {y}) K
theorem finiteDimensional_adjoin [IsFunctionField k K] {x : K} (hx : Transcendental k x) :
    FiniteDimensional (IntermediateField.adjoin k {x}) K := by
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx)
      (by rw [trdeg_eq_one, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have := essFiniteType (k := k) (K := K)
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K :=
    Algebra.EssFiniteType.of_comp k _ K
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic
end FunctionField
open Polynomial
section Place
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
@[ext]
structure Place where

  ring : ValuationSubring K
  ne_top : ring ≠ ⊤
  algebraMap_mem : ∀ c : k, algebraMap k K c ∈ ring
namespace Place
variable {k K} (v : Place k K)
instance : Algebra k v.ring :=
  (RingHom.codRestrict (algebraMap k K) v.ring v.algebraMap_mem).toAlgebra
@[simp]
theorem coe_algebraMap_apply (c : k) : ((algebraMap k v.ring c : v.ring) : K) = algebraMap k K c :=
  rfl
instance : IsScalarTower k v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl
abbrev ResidueField := IsLocalRing.ResidueField v.ring
theorem valuation_algebraMap {c : k} (hc : c ≠ 0) : v.ring.valuation (algebraMap k K c) = 1 :=
  (v.ring.valuation_eq_one_iff (algebraMap k v.ring c)).1 ((IsUnit.mk0 c hc).map _)
theorem valuation_aeval_le_one {x : K} (hx : x ∈ v.ring) (p : k[X]) :
    v.ring.valuation (aeval x p) ≤ 1 := by
  have h : aeval x p = algebraMap v.ring K (aeval (⟨x, hx⟩ : v.ring) p) :=
    Polynomial.aeval_algebraMap_apply K (⟨x, hx⟩ : v.ring) p
  rw [h]
  exact v.ring.valuation_le_one _
theorem valuation_eq_one_of_sub_lt {z : K} {a : k} (ha : a ≠ 0)
    (h : v.ring.valuation (z - algebraMap k K a) < 1) : v.ring.valuation z = 1 := by
  rw [← v.valuation_algebraMap ha] at h ⊢
  exact Valuation.map_eq_of_sub_lt _ h
theorem exists_aeval_div_pow {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) (p : k[X])
    (hp : p ≠ 0) :
    ∃ m : ℕ, ∃ a : k, a ≠ 0 ∧ v.ring.valuation (aeval x p / x ^ m - algebraMap k K a) < 1 := by
  have hxO : x ∈ v.ring := (v.ring.valuation_le_one_iff x).1 hx.le
  revert hp
  induction p using Polynomial.recOnHorner with
  | M0 => intro h; exact absurd rfl h
  | MC p a hp0 ha _ =>
    intro _
    refine ⟨0, a, ha, ?_⟩
    obtain ⟨q, rfl⟩ : X ∣ p := Polynomial.X_dvd_iff.2 hp0
    rw [pow_zero, div_one, map_add, aeval_C, add_sub_cancel_right, map_mul, aeval_X, map_mul]
    calc v.ring.valuation x * v.ring.valuation (aeval x q) ≤ v.ring.valuation x * 1 :=
          mul_le_mul' le_rfl (v.valuation_aeval_le_one hxO q)
      _ < 1 := by rwa [mul_one]
  | MX p hp0 ih =>
    intro _
    obtain ⟨m, a, ha, h⟩ := ih hp0
    refine ⟨m + 1, a, ha, ?_⟩
    have : aeval x (p * X) / x ^ (m + 1) = aeval x p / x ^ m := by
      rw [map_mul, aeval_X, pow_succ, mul_div_mul_right _ _ hx0]
    rwa [this]
theorem transcendental_of_valuation_lt_one {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) :
    Transcendental k x := by
  rintro ⟨p, hp, hpx⟩
  obtain ⟨m, a, ha, h⟩ := v.exists_aeval_div_pow hx0 hx p hp
  have h1 := v.valuation_eq_one_of_sub_lt ha h
  rw [hpx, zero_div, map_zero] at h1
  exact zero_ne_one h1
theorem exists_zpow_of_mem_adjoin {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) {c : K}
    (hc : c ∈ IntermediateField.adjoin k {x}) (hc0 : c ≠ 0) :
    ∃ m : ℤ, ∃ a : k, a ≠ 0 ∧ v.ring.valuation (c / x ^ m - algebraMap k K a) < 1 := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k c).1 hc
  have hr : r ≠ 0 := by rintro rfl; simp at hc0
  have hs : s ≠ 0 := by rintro rfl; simp at hc0
  obtain ⟨m₁, a₁, ha₁, h₁⟩ := v.exists_aeval_div_pow hx0 hx r hr
  obtain ⟨m₂, a₂, ha₂, h₂⟩ := v.exists_aeval_div_pow hx0 hx s hs
  have hz₂ := v.valuation_eq_one_of_sub_lt ha₂ h₂
  have hs0 : aeval x s ≠ 0 := by
    intro h; rw [h, zero_div, map_zero] at hz₂; exact zero_ne_one hz₂
  have hz₂0 : aeval x s / x ^ m₂ ≠ 0 := div_ne_zero hs0 (pow_ne_zero _ hx0)
  have ha₂' : algebraMap k K a₂ ≠ 0 := (_root_.map_ne_zero _).2 ha₂
  refine ⟨(m₁ : ℤ) - m₂, a₁ / a₂, div_ne_zero ha₁ ha₂, ?_⟩
  have key : aeval x r / aeval x s / x ^ ((m₁ : ℤ) - m₂) - algebraMap k K (a₁ / a₂) =
      ((aeval x r / x ^ m₁ - algebraMap k K a₁) * algebraMap k K a₂ -
          algebraMap k K a₁ * (aeval x s / x ^ m₂ - algebraMap k K a₂)) /
        (aeval x s / x ^ m₂ * algebraMap k K a₂) := by
    rw [map_div₀, zpow_sub₀ hx0, zpow_natCast, zpow_natCast]
    field_simp
    ring
  rw [key, map_div₀, map_mul, hz₂, v.valuation_algebraMap ha₂, one_mul, div_one]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, v.valuation_algebraMap ha₂, mul_one]; exact h₁
  · rw [map_mul, v.valuation_algebraMap ha₁, one_mul]; exact h₂
theorem exists_valuation_eq_zpow {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1) {c : K}
    (hc : c ∈ IntermediateField.adjoin k {x}) (hc0 : c ≠ 0) :
    ∃ m : ℤ, v.ring.valuation c = v.ring.valuation x ^ m := by
  obtain ⟨m, a, ha, h⟩ := v.exists_zpow_of_mem_adjoin hx0 hx hc hc0
  refine ⟨m, ?_⟩
  have h1 := v.valuation_eq_one_of_sub_lt ha h
  rw [map_div₀, map_zpow₀] at h1
  have hxm : v.ring.valuation x ^ m ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 hx0)
  exact (div_eq_one_iff_eq hxm).1 h1
theorem exists_valuation_lt_one_ne_zero : ∃ x : K, x ≠ 0 ∧ v.ring.valuation x < 1 := by
  obtain ⟨z, hz⟩ : ∃ z, z ∉ v.ring := by
    by_contra h
    push Not at h
    exact v.ne_top (eq_top_iff.2 fun z _ => h z)
  have hz0 : z ≠ 0 := fun h => hz (h ▸ v.ring.zero_mem)
  exact ⟨z⁻¹, inv_ne_zero hz0,
    v.ring.mem_nonunits_iff.1 (v.ring.inv_mem_nonunits_iff.2 (Or.inr hz))⟩
theorem linearIndependent_of_valuation {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1)
    {ι : Type*} [Fintype ι] (a : ι → K)
    (hlow : ∀ i, v.ring.valuation x < v.ring.valuation (a i))
    (hup : ∀ i, v.ring.valuation (a i) ≤ 1)
    (hinj : Function.Injective fun i => v.ring.valuation (a i)) :
    LinearIndependent (IntermediateField.adjoin k {x}) a := by
  classical
  set V := v.ring.valuation
  have hX0 : 0 < V x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)
  have aux : ∀ i j (m n : ℤ), m < n → V (a i) * V x ^ m = V (a j) * V x ^ n → False := by
    intro i j m n hmn h
    have h1 : V x ^ n ≤ V x ^ (m + 1) := (zpow_right_strictAnti₀ hX0 hx).antitone (by omega)
    have h2 : V (a i) * V x ^ m ≤ V x * V x ^ m := by
      rw [h]
      calc V (a j) * V x ^ n ≤ 1 * V x ^ (m + 1) := mul_le_mul' (hup j) h1
        _ = V x * V x ^ m := by rw [one_mul, zpow_add_one₀ hX0.ne', mul_comm]
    have hm : 0 < V x ^ m := zpow_pos hX0 m
    exact absurd (le_of_mul_le_mul_right h2 hm) (not_le.2 (hlow i))
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  let s := Finset.univ.filter fun i => g i ≠ 0
  have hs : s.Nonempty := ⟨i₀, by simp [s, hi₀]⟩
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => V ((g i : K) * a i)) hs
  have hterm : ∀ i ∈ s, ∃ m : ℤ, V ((g i : K) * a i) = V (a i) * V x ^ m := by
    intro i hi
    have hgi : (g i : K) ≠ 0 := by
      have : g i ≠ 0 := by simpa [s] using hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨m, hm⟩ := v.exists_valuation_eq_zpow hx0 hx (g i).2 hgi
    exact ⟨m, by rw [map_mul, hm, mul_comm]⟩
  have hlt : ∀ i ∈ s \ {j}, V ((g i : K) * a i) < V ((g j : K) * a j) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    refine lt_of_le_of_ne (hmax i hi.1) ?_
    intro heq
    obtain ⟨m, hm⟩ := hterm i hi.1
    obtain ⟨n, hn⟩ := hterm j hj
    rw [hm, hn] at heq
    rcases lt_trichotomy m n with h | h | h
    · exact aux i j m n h heq
    · subst h
      exact hi.2 (hinj (mul_right_cancel₀ (zpow_ne_zero _ hX0.ne') heq))
    · exact aux j i n m h heq.symm
  have hsum : ∑ i, g i • a i = ∑ i ∈ s, (g i : K) * a i := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rfl
    · push Not at h
      rw [h, zero_smul]
  have hval := V.map_sum_eq_of_lt hj hlt
  rw [← hsum, hg, map_zero] at hval
  obtain ⟨n, hn⟩ := hterm j hj
  rw [hn] at hval
  have haj : V (a j) ≠ 0 := (lt_trans hX0 (hlow j)).ne'
  exact mul_ne_zero haj (zpow_ne_zero _ hX0.ne') hval.symm
theorem linearIndependent_of_residue {x : K} (hx0 : x ≠ 0) (hx : v.ring.valuation x < 1)
    {ι : Type*} [Fintype ι] (z : ι → v.ring)
    (hz : LinearIndependent k fun i => IsLocalRing.residue v.ring (z i)) :
    LinearIndependent (IntermediateField.adjoin k {x}) fun i => (z i : K) := by
  classical
  set V := v.ring.valuation
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨j, -, hmax⟩ := Finset.univ.exists_max_image (fun i => V (g i : K)) ⟨i₀, Finset.mem_univ _⟩
  have hgi₀ : (g i₀ : K) ≠ 0 := fun h => hi₀ (Subtype.ext h)
  have hgj : (g j : K) ≠ 0 := by
    intro h
    have := hmax i₀ (Finset.mem_univ _)
    rw [h, map_zero] at this
    exact hgi₀ ((Valuation.zero_iff _).1 (le_antisymm this zero_le))
  have hVj : 0 < V (g j : K) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hgj)
  have hle : ∀ i, V ((g i : K) / g j) ≤ 1 := fun i => by
    rw [map_div₀]; exact (div_le_one₀ hVj).2 (hmax i (Finset.mem_univ _))
  have hh : ∀ i, ∃ b : k, V ((g i : K) / g j - algebraMap k K b) < 1 := by
    intro i
    rcases (hle i).lt_or_eq with hlt | heq
    · exact ⟨0, by rwa [map_zero, sub_zero]⟩
    · have hne : (g i : K) / g j ≠ 0 := by
        intro h; rw [h, map_zero] at heq; exact zero_ne_one heq
      have hmem : (g i : K) / g j ∈ IntermediateField.adjoin k {x} := div_mem (g i).2 (g j).2
      obtain ⟨m, a, ha, h⟩ := v.exists_zpow_of_mem_adjoin hx0 hx hmem hne
      have h1 := v.valuation_eq_one_of_sub_lt ha h
      rw [map_div₀, map_zpow₀, heq, one_div, inv_eq_one,
        zpow_eq_one_iff_right₀ zero_le hx.ne] at h1
      subst h1
      exact ⟨a, by simpa using h⟩
  choose b hb using hh
  let y : ι → v.ring := fun i => ⟨(g i : K) / g j, (v.ring.valuation_le_one_iff _).1 (hle i)⟩
  have hres : ∀ i, IsLocalRing.residue v.ring (y i) = algebraMap k v.ResidueField (b i) := by
    intro i
    rw [IsScalarTower.algebraMap_apply k v.ring v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq,
      ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, v.ring.valuation_lt_one_iff]
    exact hb i
  have hsum0 : ∑ i, y i * z i = 0 := by
    apply Subtype.ext
    have : ∑ i, (g i : K) / g j * (z i : K) = (∑ i, g i • (z i : K)) / g j := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def]
      simp only [IntermediateField.algebraMap_apply]
      ring
    simpa [y, hg] using this
  have hcomb : ∑ i, b i • IsLocalRing.residue v.ring (z i) = 0 := by
    have := congrArg (IsLocalRing.residue v.ring) hsum0
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hres, Algebra.smul_def]
  have hbj := (Fintype.linearIndependent_iff.1 hz) b hcomb j
  have := hb j
  rw [hbj, map_zero, sub_zero, div_self hgj, map_one] at this
  exact lt_irrefl _ this
theorem isNoetherianRing [IsFunctionField k K] : IsNoetherianRing v.ring := by
  rw [isNoetherianRing_iff, isNoetherian_iff', WellFoundedGT, isWellFounded_iff,
    RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => ?_⟩
  have hf : ∀ n, f n < f (n + 1) := fun n => f.map_rel_iff.2 (Nat.lt_succ_self n)
  choose b hb1 hb2 using fun n => SetLike.exists_of_lt (hf n)
  set V := v.ring.valuation
  have hstep : ∀ n, V (b n : K) < V (b (n + 1) : K) := by
    intro n
    by_contra hle
    push Not at hle
    apply hb2 (n + 1)
    by_cases h0 : (b n : K) = 0
    · have h1 : (b (n + 1) : K) = 0 := by
        rw [h0, map_zero] at hle
        exact (Valuation.zero_iff _).1 (le_antisymm hle zero_le)
      rw [show b (n + 1) = 0 from Subtype.ext h1]
      exact zero_mem _
    · have hc : (b (n + 1) : K) / b n ∈ v.ring := by
        rw [← v.ring.valuation_le_one_iff, map_div₀]
        exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h0))).2 hle
      have heq : b (n + 1) = b n * ⟨_, hc⟩ := Subtype.ext (by
        change (b (n + 1) : K) = b n * ((b (n + 1) : K) / b n)
        rw [mul_div_cancel₀ _ h0])
      rw [heq]
      exact Ideal.mul_mem_right _ _ (hb1 n)
  have hmono : StrictMono fun n => V (b n : K) := strictMono_nat_of_lt_succ hstep
  have hb0 : (b 0 : K) ≠ 0 := by
    intro h
    apply hb2 0
    rw [show b 0 = 0 from Subtype.ext h]
    exact zero_mem _
  have hb0lt : V (b 0 : K) < 1 := lt_of_lt_of_le (hstep 0) (v.ring.valuation_le_one _)
  have := finiteDimensional_adjoin (v.transcendental_of_valuation_lt_one hb0 hb0lt)
  have hli := v.linearIndependent_of_valuation hb0 hb0lt
    (fun i : Fin (Module.finrank (IntermediateField.adjoin k {(b 0 : K)}) K + 1) =>
      (b ((i : ℕ) + 1) : K))
    (fun i => hmono (Nat.succ_pos _)) (fun i => v.ring.valuation_le_one _)
    (fun i j h => Fin.ext (by simpa using hmono.injective h))
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega
instance [IsFunctionField k K] : IsDiscreteValuationRing v.ring := by
  have hN := v.isNoetherianRing
  have : IsPrincipalIdealRing v.ring := ((IsBezout.TFAE (R := v.ring)).out 0 1).1 hN
  refine { (inferInstance : IsPrincipalIdealRing v.ring), (inferInstance : IsLocalRing v.ring) with
    not_a_field' := ?_ }
  obtain ⟨x, hx0, hx⟩ := v.exists_valuation_lt_one_ne_zero
  have hxO : x ∈ v.ring := (v.ring.valuation_le_one_iff x).1 hx.le
  intro h
  have hmem : (⟨x, hxO⟩ : v.ring) ∈ IsLocalRing.maximalIdeal v.ring :=
    (v.ring.valuation_lt_one_iff _).2 hx
  rw [h, Ideal.mem_bot] at hmem
  exact hx0 (congrArg Subtype.val hmem)
instance [IsFunctionField k K] : FiniteDimensional k v.ResidueField := by
  obtain ⟨x, hx0, hx⟩ := v.exists_valuation_lt_one_ne_zero
  have := finiteDimensional_adjoin (v.transcendental_of_valuation_lt_one hx0 hx)
  apply Module.rank_lt_aleph0_iff.1
  refine lt_of_le_of_lt
    (rank_le (n := Module.finrank (IntermediateField.adjoin k {x}) K) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0)
  choose z hz using fun r : v.ResidueField => IsLocalRing.residue_surjective r
  have hli := v.linearIndependent_of_residue hx0 hx (fun i : s => z i) (by simpa [hz] using hs)
  simpa using hli.fintype_card_le_finrank
noncomputable def deg : ℕ := Module.finrank k v.ResidueField
section Valuation
variable [IsFunctionField k K]
def heightOneSpectrum : IsDedekindDomain.HeightOneSpectrum v.ring where
  asIdeal := IsLocalRing.maximalIdeal v.ring
  isPrime := (IsLocalRing.maximalIdeal.isMaximal v.ring).isPrime
  ne_bot := IsDiscreteValuationRing.not_a_field v.ring
@[simp]
theorem heightOneSpectrum_asIdeal :
    v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.ring :=
  rfl
noncomputable def valuation : Valuation K ℤᵐ⁰ := v.heightOneSpectrum.valuation K
noncomputable def ord (x : K) : ℤ := -WithZero.log (v.valuation x)
@[simp]
theorem ord_zero : v.ord 0 = 0 := by simp [ord]
@[simp]
theorem ord_one : v.ord 1 = 0 := by simp [ord]
theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : v.ord (x * y) = v.ord x + v.ord y := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff v.valuation).2 hx)
    ((Valuation.ne_zero_iff v.valuation).2 hy)]
  ring
noncomputable def ordHom : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (v.ord x)
  map_one' := by simp
  map_mul' x y := by
    simp only [Units.val_mul, v.ord_mul x.ne_zero y.ne_zero, ofAdd_add]
end Valuation
end Place
end Place
end GroundTheory.FunctionField


