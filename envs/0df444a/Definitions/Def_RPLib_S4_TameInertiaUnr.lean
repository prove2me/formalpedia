-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaUnr
-- name    : RPLib_S4_TameInertiaUnr
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:02:23.924083+00:00
-- url     : https://prove2.me/theorems/a040be1e-5f99-42d6-ba07-5a3d69ce21ea
-- title:
--   A unit-derivative criterion for unramified extensions
-- statement:
--   Let $G \in A[X]$ be monic and suppose every root $y \in \overline{K}$ of $G$ satisfies $$y\, G'(y) = u$$ for one unit $u$ of $A$. The file proves that the field generated over $K$ by the roots of $G$ is a finite Galois extension unramified over $A$, so every root lies in $K_U$. Proof: two distinct roots $a \ne b$ in the integral closure give $a G'(a) = (a - b)\, a\, G_2(a)$, so $a - b$ is a unit, while an inertia element moving $a$ would put $a - \sigma a$ in a prime.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter III, Section 2 (different and discriminant); J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter III

import Mathlib
import Definitions.Def_RPLib_S4_GalCover

/-!
# Tame inertia, part Unr: the unit-derivative criterion (S4-PD item (2), T5)

If `G ∈ A[X]` is monic and every root `y ∈ K̄` of `G` satisfies `y · G'(y) = u` for one unit `u` of `A`, then
the field generated over `K` by the roots of `G` is unramified over `A` (`udField_mem_unramSet`), so every root
lies in `K_U` (`mem_maxUnram_of_ud`). Proof: two distinct roots `a ≠ b` of `G` in the integral closure `S`
give `G = (X - a)(X - b) G₂` over `S`, so `a · G'(a) = (a - b) · a · G₂(a)` and `a - b` is a unit of `S`;
an inertia element moving `a` would put `a - σ a` in a prime.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson
namespace TameInertia

noncomputable section

section Unr

variable (A K : Type) [CommRing A] [Field K] [Algebra A K]

/-- The field generated over `K` by the roots of `G ∈ A[X]` in `K̄`. -/
abbrev udField (G : A[X]) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K ((G.map (algebraMap A K)).rootSet (AlgebraicClosure K))

instance udField_isSplittingField (G : A[X]) :
    (G.map (algebraMap A K)).IsSplittingField K (udField A K G) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance udField_finiteDimensional (G : A[X]) : FiniteDimensional K (udField A K G) :=
  IsSplittingField.finiteDimensional _ (G.map (algebraMap A K))

variable {A K}

/-- The unit-derivative hypothesis makes `G` separable over `K`. -/
theorem ud_separable {G : A[X]} (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A)) :
    (G.map (algebraMap A K)).Separable := by
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K) _ _).2 fun y => ?_
  by_cases hy : aeval y (G.map (algebraMap A K)) = 0
  · right
    rw [aeval_map_algebraMap] at hy
    rw [derivative_map, aeval_map_algebraMap]
    intro h0
    have h := hu y hy
    rw [h0, mul_zero] at h
    exact (u.isUnit.map (algebraMap A (AlgebraicClosure K))).ne_zero h.symm
  · exact Or.inl hy

/-- **T5.** The unit-derivative criterion: `K(roots of G)` is a finite Galois extension unramified over `A`. -/
theorem udField_mem_unramSet {G : A[X]} (hG : G.Monic) (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A)) :
    udField A K G ∈ unramSet A K := by
  have : IsGalois K (udField A K G) := IsGalois.of_separable_splitting_field (ud_separable u hu)
  refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  let L := udField A K G
  let S := integralClosure A L
  let ι : L →ₐ[A] AlgebraicClosure K := (IntermediateField.val L).restrictScalars A
  let φ : S →ₐ[A] AlgebraicClosure K := ι.comp (integralClosure A L).val
  have hι : Function.Injective ι := fun x y h => Subtype.ext h
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (Subtype.ext h)
  have hrootS : ∀ s : S, aeval (φ s) G = 0 → aeval s G = 0 := fun s hs =>
    hφ (by rw [← aeval_algHom_apply, map_zero]; exact hs)
  have hunitS : ∀ s : S, aeval (φ s) G = 0 → s * aeval s (derivative G) = algebraMap A S (u : A) :=
    fun s hs => hφ (by rw [map_mul, ← aeval_algHom_apply, AlgHom.commutes]; exact hu _ hs)
  -- every root `z ∈ L` is fixed by `τ`
  have hfixL : ∀ z : L, aeval (ι z) G = 0 → τ z = z := by
    intro z hz'
    have hz : aeval z G = 0 := hι (by rw [← aeval_algHom_apply, map_zero]; exact hz')
    have hτz : aeval (τ z) G = 0 := by
      have h := aeval_algHom_apply (((τ : L →ₐ[K] L)).restrictScalars A) z G
      rw [hz, map_zero] at h
      exact h
    have hint : IsIntegral A z := ⟨G, hG, by rw [← aeval_def]; exact hz⟩
    let a : S := ⟨z, hint⟩
    obtain ⟨b, hbdef⟩ : ∃ b : S, b = τ • a := ⟨_, rfl⟩
    have ha : aeval (φ a) G = 0 := hz'
    have hb : aeval (φ b) G = 0 := by
      rw [hbdef]
      show aeval (ι (τ z)) G = 0
      rw [aeval_algHom_apply, hτz, map_zero]
    by_contra hne
    have hba : b ≠ a := by
      intro h
      rw [hbdef] at h
      exact hne (congrArg Subtype.val h)
    have hra : (G.map (algebraMap A S)).IsRoot a := by
      rw [IsRoot.def, eval_map_algebraMap]; exact hrootS a ha
    have hrb : (G.map (algebraMap A S)).IsRoot b := by
      rw [IsRoot.def, eval_map_algebraMap]; exact hrootS b hb
    obtain ⟨G1, hG1⟩ := dvd_iff_isRoot.2 hra
    have hrb1 : G1.IsRoot b := by
      have h := hrb
      rw [IsRoot.def, hG1, eval_mul, eval_sub, eval_X, eval_C] at h
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hba)
    obtain ⟨G2, hG2⟩ := dvd_iff_isRoot.2 hrb1
    have hder : eval a (derivative (G.map (algebraMap A S))) = (a - b) * eval a G2 := by
      rw [hG1, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, hG2,
        eval_mul, eval_sub, eval_X, eval_C]
    have hd : eval a (derivative (G.map (algebraMap A S))) = aeval a (derivative G) := by
      rw [derivative_map, eval_map_algebraMap]
    have hkey : (a - b) * (a * eval a G2) = algebraMap A S (u : A) := by
      rw [← hunitS a ha, ← hd, hder]; ring
    have hunit : IsUnit (a - b) := by
      have h : IsUnit (algebraMap A S (u : A)) := u.isUnit.map _
      rw [← hkey] at h
      exact isUnit_of_mul_isUnit_left h
    have hmem : a - b ∈ Q := by
      have h : τ • a - a ∈ Q := AddSubgroup.mem_inertia.1 hτ a
      rw [← hbdef] at h
      rw [← neg_sub]
      exact Q.neg_mem h
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hmem hunit)
  refine AlgEquiv.ext fun z => AlgHom.congr_fun (IntermediateField.adjoin_algHom_ext (F := K)
    (φ₁ := (τ : L →ₐ[K] L)) (φ₂ := AlgHom.id K L) fun y hy => ?_) z
  have h := (mem_rootSet.1 hy).2
  rw [aeval_map_algebraMap] at h
  exact hfixL ⟨y, IntermediateField.subset_adjoin K _ hy⟩ h

theorem udField_le_maxUnram {G : A[X]} (hG : G.Monic) (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A)) :
    udField A K G ≤ maxUnram A K := by
  rw [maxUnram_eq_sSup]
  exact le_sSup (udField_mem_unramSet hG u hu)

/-- Every root of a unit-derivative polynomial lies in `K_U`. -/
theorem mem_maxUnram_of_ud {G : A[X]} (hG : G.Monic) (u : Aˣ)
    (hu : ∀ y : AlgebraicClosure K, aeval y G = 0 →
      y * aeval y (derivative G) = algebraMap A (AlgebraicClosure K) (u : A))
    {y : AlgebraicClosure K} (hy : aeval y G = 0) : y ∈ maxUnram A K := by
  refine udField_le_maxUnram hG u hu (IntermediateField.subset_adjoin K _ ?_)
  rw [mem_rootSet]
  refine ⟨(hG.map (algebraMap A K)).ne_zero, ?_⟩
  rw [aeval_map_algebraMap]
  exact hy

end Unr

end

end TameInertia
end RamanujanPetersson


