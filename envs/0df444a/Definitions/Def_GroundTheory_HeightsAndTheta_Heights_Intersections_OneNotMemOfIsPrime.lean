-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:37.395087+00:00
-- url     : https://prove2.me/theorems/ac46e6a6-110c-4bcb-87a6-2028962398a5
-- title:
--   One Not Mem Of Is Prime
-- statement:
--   Definitions and structural lemmas for One Not Mem Of Is Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OneNotMemOfIsPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
namespace regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
section Forms
theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm
theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [support_one, Finset.mem_singleton] at hm
  subst hm
  simp
theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]
theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k
theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [support_neg] at hm
  exact hf m hm k
end Forms
section Loc
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
def fracHom : MRing ι →+* FractionRing (MRing ι ⧸ P) :=
  (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))).comp (Ideal.Quotient.mk P)
theorem fracHom_apply (u : MRing ι) :
    fracHom P u = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) :=
  rfl
variable {P} in
theorem fracHom_eq_zero_iff {u : MRing ι} : fracHom P u = 0 ↔ u ∈ P := by
  rw [fracHom_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
theorem one_notMem_of_isPrime : (1 : MRing ι) ∉ W :=
  (Ideal.ne_top_iff_one W).mp (Ideal.IsPrime.ne_top ‹_›)
variable {P W} in

theorem mem_locRing_iff (hPW : P ≤ W) {x : FractionRing (MRing ι ⧸ P)} :
    x ∈ locRing P W ↔ ∃ (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧
      x * fracHom P v = fracHom P u := by
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
      exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
    | zero => exact ⟨0, 1, 0, homog_zero 0, homog_one, one_notMem_of_isPrime W, by simp⟩
    | one => exact ⟨1, 1, 0, homog_one, homog_one, one_notMem_of_isPrime W, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := hx
      obtain ⟨u', v', a', hu', hv', hvW', hy⟩ := hy
      refine ⟨u * v' + u' * v, v * v', a + a', homog_add (homog_mul hu hv') ?_, homog_mul hv hv', ?_, ?_⟩
      · rw [add_comm a a']
        exact homog_mul hu' hv
      · exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hvW hvW'
      · simp only [map_add, map_mul]
        rw [← hx, ← hy]
        ring
    | neg x _ hx =>
      obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := hx
      exact ⟨-u, v, a, homog_neg hu, hv, hvW, by rw [map_neg, ← hx, neg_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := hx
      obtain ⟨u', v', a', hu', hv', hvW', hy⟩ := hy
      refine ⟨u * u', v * v', a + a', homog_mul hu hu', homog_mul hv hv', ?_, ?_⟩
      · exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hvW hvW'
      · simp only [map_mul]
        rw [← hx, ← hy]
        ring
  · rintro ⟨u, v, a, hu, hv, hvW, hx⟩
    have hv' : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => hvW (hPW h)
    refine Subring.subset_closure ⟨u, v, a, hv', hvW, hu, hv, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hx
variable {P W} in

theorem div_mem_locRing (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hv : IsMultiHomog v a) (hvW : v ∉ W) : fracHom P u / fracHom P v ∈ locRing P W := by
  refine (mem_locRing_iff hPW).mpr ⟨u, v, a, hu, hv, hvW, div_mul_cancel₀ _ ?_⟩
  rw [Ne, fracHom_eq_zero_iff]
  exact fun h => hvW (hPW h)
variable {P W} in

theorem isUnit_iff (hPW : P ≤ W) (x : locRing P W) {u v : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hv : IsMultiHomog v a) (hvW : v ∉ W)
    (hx : (x : FractionRing (MRing ι ⧸ P)) * fracHom P v = fracHom P u) : IsUnit x ↔ u ∉ W := by
  constructor
  · intro hunit huW
    obtain ⟨y, hxy⟩ := hunit.exists_right_inv
    obtain ⟨u', v', a', -, -, hvW', hy⟩ := (mem_locRing_iff hPW).mp y.2
    have h1 : (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 :=
      congrArg Subtype.val hxy
    have h2 : fracHom P (u * u' - v * v') = 0 := by
      rw [map_sub, map_mul, map_mul, ← hx, ← hy]
      linear_combination (fracHom P v * fracHom P v') * h1
    rw [fracHom_eq_zero_iff] at h2
    have hvv : v * v' ∈ W := by
      have := W.sub_mem (W.mul_mem_right u' huW) (hPW h2)
      simpa using this
    exact (Ideal.IsPrime.mem_or_mem ‹_› hvv).elim hvW hvW'
  · intro huW
    have hu0 : fracHom P u ≠ 0 := by
      rw [Ne, fracHom_eq_zero_iff]
      exact fun h => huW (hPW h)
    have hv0 : fracHom P v ≠ 0 := by
      rw [Ne, fracHom_eq_zero_iff]
      exact fun h => hvW (hPW h)
    refine IsUnit.of_mul_eq_one (⟨_, div_mem_locRing hPW hv hu huW⟩ : locRing P W) (Subtype.ext ?_)
    change (x : FractionRing (MRing ι ⧸ P)) * (fracHom P v / fracHom P u) = 1
    rw [eq_div_of_mul_eq hv0 hx]
    field_simp
variable {P W} in

theorem isLocalRing (hPW : P ≤ W) : IsLocalRing (locRing P W) := by
  refine IsLocalRing.of_nonunits_add fun x y hx hy hxy => ?_
  obtain ⟨u, v, a, hu, hv, hvW, hx'⟩ := (mem_locRing_iff hPW).mp x.2
  obtain ⟨u', v', a', hu', hv', hvW', hy'⟩ := (mem_locRing_iff hPW).mp y.2
  have huW : u ∈ W := by
    by_contra h
    exact hx ((isUnit_iff hPW x hu hv hvW hx').mpr h)
  have hu'W : u' ∈ W := by
    by_contra h
    exact hy ((isUnit_iff hPW y hu' hv' hvW' hy').mpr h)
  have hnum : IsMultiHomog (u * v' + u' * v) (a + a') := by
    refine homog_add (homog_mul hu hv') ?_
    rw [add_comm a a']
    exact homog_mul hu' hv
  have hden : v * v' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hvW hvW'
  have heq : ((x + y : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P (v * v') =
      fracHom P (u * v' + u' * v) := by
    change ((x : FractionRing (MRing ι ⧸ P)) + y) * _ = _
    simp only [map_add, map_mul]
    rw [← hx', ← hy']
    ring
  exact (isUnit_iff hPW (x + y) hnum (homog_mul hv hv') hden heq).mp hxy
    (W.add_mem (W.mul_mem_right _ huW) (W.mul_mem_right _ hu'W))
end Loc
end regularityLocalFlat_holds
end
end GroundTheory.Heights₂.Heights.Inter


