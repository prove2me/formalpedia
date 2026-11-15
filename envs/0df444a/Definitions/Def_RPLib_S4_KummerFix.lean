-- Prove2me | Definitions.Def_RPLib_S4_KummerFix
-- name    : RPLib_S4_KummerFix
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:12:12.711443+00:00
-- url     : https://prove2.me/theorems/33356f4f-8ea0-4225-9c88-a10a2e116d10
-- title:
--   The fixed field of the geometric fundamental group is the union of the constant levels
-- statement:
--   For $K$ of characteristic $p$ and $K_U$ the maximal extension unramified over $A$, the file proves by the infinite Galois correspondence that $x \in K_U$ is fixed by the geometric fundamental group (automorphisms fixing every constant) if and only if $x \in K(\mathbb{F}_{p^k})$ for some $k > 0$, and that a unit $\alpha$ is a Kummer radical for the geometric group ($\alpha^N$ fixed) if and only if $$\alpha^N \in K(\mathbb{F}_{p^k}) \text{ for some } k > 0.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8; J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter IV, Section 1

import Mathlib
import Definitions.Def_RPLib_S4_KummerConst

/-!
# S4-Kummer, part K5a: the fixed field of `π₁^geo` is the union of the constant levels

`pi1geo A K q` (automorphisms of `K_U` fixing every constant) has fixed field `⋃_k K(𝔽_{p^k}) ∩ K_U`
(infinite Galois correspondence on `K_U / K`):

* `fixed_iff_mem_constLevel`: `x ∈ K_U` is fixed by `π₁^geo` iff `x ∈ constLevel K p k` for some `k > 0`;
* `mem_rad_pi1geo_iff`: `α ∈ rad π₁^geo N` iff `α ^ N` lies in some constant level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Kummer

open CurveCoh Polynomial

noncomputable section

/-- `y ^ b ^ n = y` implies `y ^ b ^ (n * j) = y`. -/
theorem pow_pow_mul_eq {L : Type*} [Monoid L] {y : L} {b n : ℕ} (h : y ^ b ^ n = y) (j : ℕ) :
    y ^ b ^ (n * j) = y := by
  induction j with
  | zero => simp
  | succ j ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/-- Generic: an automorphism fixing a set fixes the field it generates. -/
theorem mem_fixingSubgroup_adjoin' {K E : Type*} [Field K] [Field E] [Algebra K E] {S : Set E}
    {σ : E ≃ₐ[K] E} (h : ∀ x ∈ S, σ x = x) : σ ∈ (IntermediateField.adjoin K S).fixingSubgroup := by
  have hle : IntermediateField.adjoin K S ≤
      IntermediateField.fixedField (_root_.fixingSubgroup (E ≃ₐ[K] E) S) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    exact (_root_.mem_fixingSubgroup_iff _).1 hf x hx
  exact (IntermediateField.le_iff_le _ _).1 hle ((_root_.mem_fixingSubgroup_iff _).2 h)

section Fix

variable (A K : Type) [CommRing A] [Field K] [Algebra A K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- The constants of `K_U` (of level `q`) generate an intermediate field of `K_U / K`. -/
def constFieldU (q : ℕ) : IntermediateField K (maxUnram A K) :=
  IntermediateField.adjoin K {x | IsConst q x}

theorem fixingSubgroup_constFieldU (q : ℕ) : (constFieldU A K q).fixingSubgroup = pi1geo A K q := by
  ext σ
  constructor
  · intro hσ
    rw [mem_pi1geo]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff ..).1 hσ x (IntermediateField.subset_adjoin K _ hx)
  · intro hσ
    exact mem_fixingSubgroup_adjoin' fun x hx => (mem_pi1geo A K q σ).1 hσ x hx

variable {A K}

/-- Elements of `K_U` fixed by `π₁^geo` lie in a constant level `K(𝔽_{q^k})`. -/
theorem exists_constLevel_of_fixed {e : ℕ} (he : 0 < e) {x : maxUnram A K}
    (hx : ∀ σ ∈ pi1geo A K (p ^ e), σ x = x) :
    ∃ k, 0 < k ∧ (x : AlgebraicClosure K) ∈ constLevel K p (e * k) := by
  have hmem : x ∈ IntermediateField.fixedField (constFieldU A K (p ^ e)).fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [fixingSubgroup_constFieldU] at hσ
    exact hx σ hσ
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  obtain ⟨T, hT, hxT⟩ := IntermediateField.exists_finset_of_mem_adjoin hmem
  have hc : ∀ y ∈ T, IsConst (p ^ e) y := fun y hy => hT hy
  choose! n hn hpow using hc
  refine ⟨∏ y ∈ T, n y, Finset.prod_pos fun y hy => hn y hy, ?_⟩
  have hle : (IntermediateField.adjoin K (T : Set (maxUnram A K))).map (maxUnram A K).val ≤
      constLevel K p (e * ∏ y ∈ T, n y) := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hk : 0 < e * ∏ y ∈ T, n y := Nat.mul_pos he (Finset.prod_pos fun y hy => hn y hy)
    refine mem_constLevel hk ?_
    obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem n hy
    have h1 := pow_pow_mul_eq (hpow y hy) j
    rw [← hj, ← pow_mul] at h1
    show ((y : AlgebraicClosure K)) ^ p ^ (e * ∏ y ∈ T, n y) = y
    rw [← SubmonoidClass.coe_pow, h1]
  exact hle ⟨x, hxT, rfl⟩

/-- Elements of a constant level are fixed by `π₁^geo`. -/
theorem fixed_of_mem_constLevel {e k : ℕ} (he : 0 < e) (hk : 0 < k) {x : maxUnram A K}
    (hx : (x : AlgebraicClosure K) ∈ constLevel K p k) : ∀ σ ∈ pi1geo A K (p ^ e), σ x = x := by
  intro σ hσ
  let C : IntermediateField K (maxUnram A K) :=
    IntermediateField.adjoin K {y : maxUnram A K | y ^ p ^ k = y}
  have hσC : σ ∈ C.fixingSubgroup := by
    refine mem_fixingSubgroup_adjoin' ?_
    intro y hy
    refine (mem_pi1geo A K _ σ).1 hσ y ⟨k, hk, ?_⟩
    have hy' : y ^ p ^ k = y := hy
    rw [← pow_mul, mul_comm e k]
    exact pow_pow_mul_eq hy' e
  have hxC : x ∈ C := by
    have hle : constLevel K p k ≤ C.map (maxUnram A K).val := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.2 fun r hr => ?_
      have hr' : r ^ p ^ k = r := by
        rw [mem_rootSet] at hr
        simpa [sub_eq_zero] using hr.2
      refine IntermediateField.subset_adjoin K _ ⟨⟨r, mem_maxUnram_of_pow A hk hr'⟩, ?_, rfl⟩
      exact Subtype.ext hr'
    obtain ⟨y, hy, hyx⟩ := hle hx
    rwa [show y = x from Subtype.ext hyx] at hy
  exact (IntermediateField.mem_fixingSubgroup_iff ..).1 hσC x hxC

/-- **Fixed field of `π₁^geo`.** -/
theorem fixed_iff_mem_constLevel {e : ℕ} (he : 0 < e) (x : maxUnram A K) :
    (∀ σ ∈ pi1geo A K (p ^ e), σ x = x) ↔ ∃ k, 0 < k ∧ (x : AlgebraicClosure K) ∈ constLevel K p k := by
  constructor
  · intro hx
    obtain ⟨k, hk, h⟩ := exists_constLevel_of_fixed he hx
    exact ⟨e * k, Nat.mul_pos he hk, h⟩
  · rintro ⟨k, hk, h⟩
    exact fixed_of_mem_constLevel he hk h

/-- **Kummer radicals for `π₁^geo`**: `α ∈ rad π₁^geo N` iff `α ^ N` lies in a constant level. -/
theorem mem_rad_pi1geo_iff {e : ℕ} (he : 0 < e) (N : ℕ) (α : (maxUnram A K)ˣ) :
    α ∈ rad (pi1geo A K (p ^ e)) N ↔
      ∃ k, 0 < k ∧ (((α : maxUnram A K) ^ N : maxUnram A K) : AlgebraicClosure K) ∈ constLevel K p k :=
  (mem_rad _ _ α).trans (fixed_iff_mem_constLevel he _)

/-- `α ∈ K_U` is fixed by `π₁^geo` iff it is a unit of a constant level. -/
theorem mem_fixUnits_pi1geo_iff {e : ℕ} (he : 0 < e) (α : (maxUnram A K)ˣ) :
    α ∈ fixUnits (pi1geo A K (p ^ e)) ↔
      ∃ k, 0 < k ∧ ((α : maxUnram A K) : AlgebraicClosure K) ∈ constLevel K p k :=
  (mem_fixUnits _ α).trans (fixed_iff_mem_constLevel he _)

end Fix

end

end Kummer
end RamanujanPetersson


