-- Prove2me | Definitions.Def_RPLib_S4_ArtinSchreierField
-- name    : RPLib_S4_ArtinSchreierField
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:20:57.840369+00:00
-- url     : https://prove2.me/theorems/ddaf66db-3abb-40a2-b5f0-832baa4b10dc
-- title:
--   The Artin-Schreier field of $y - y^q = f$ is a Galois extension unramified over the base ring
-- statement:
--   Let $A$ be an $\mathbb{F}_q$-algebra that is a Dedekind-type domain with fraction field $K$, and $f \in A$. In any field containing $\mathbb{F}_q$ the solutions of $z^q = z$ are exactly the elements of $\mathbb{F}_q$. The polynomial $$Y^q - Y + f \in K[Y]$$ is separable; the file constructs its splitting field $L$, proves that $L/K$ is finite Galois, that its roots $y$ satisfy $y^q = y - f$ and differ from each other by elements of $\mathbb{F}_q$, and that every prime of the integral closure of $A$ in $L$ has trivial inertia, so $L$ belongs to the set of covers unramified over $A$ of the Galois-cover library (for $A = \mathbb{F}_q[x]$: the Artin-Schreier cover of the affine line).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.7 (Artin-Schreier extensions); N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_GalCover

/-!
# S4-ArtinSchreier (K1), part 1: the Artin-Schreier field of `y - y^q = f` is unramified (Katz pp.12-13)
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson
namespace ArtinSchreier

section Basic

variable (Fq : Type) [Field Fq] [Fintype Fq]

theorem one_lt_card : 1 < Fintype.card Fq := Fintype.one_lt_card

/-- In a field containing `F_q`, the solutions of `z^q = z` are the elements of `F_q`. -/
theorem exists_algebraMap_eq_of_pow_card {F : Type} [Field F] [Algebra Fq F] {z : F}
    (hz : z ^ Fintype.card Fq = z) : ∃ c : Fq, algebraMap Fq F c = z := by
  classical
  by_contra h
  push_neg at h
  set P : F[X] := X ^ Fintype.card Fq - X with hPdef
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F (one_lt_card Fq)
  have hdeg : P.natDegree = Fintype.card Fq :=
    FiniteField.X_pow_card_sub_X_natDegree_eq F (one_lt_card Fq)
  have hroot : ∀ w : F, w ^ Fintype.card Fq = w → w ∈ P.roots.toFinset := by
    intro w hw
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, hPdef]
    simp [hw]
  have hsub : insert z (Finset.univ.image (algebraMap Fq F)) ⊆ P.roots.toFinset := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | ⟨c, -, rfl⟩
    · exact hroot _ hz
    · exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have hz' : z ∉ Finset.univ.image (algebraMap Fq F) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hz', Finset.card_image_of_injective _ (algebraMap Fq F).injective,
    Finset.card_univ] at hcard
  have h2 := (Multiset.toFinset_card_le P.roots).trans (card_roots' P)
  omega

/-- Iterating `y^q = y - f`: `y^(q^i) = y - Σ_{j<i} f^(q^j)`. -/
theorem frob_iterate_root {R : Type} [CommRing R] [Algebra Fq R] {y f : R}
    (hy : y ^ Fintype.card Fq = y - f) (i : ℕ) :
    y ^ (Fintype.card Fq ^ i) = y - ∑ j ∈ Finset.range i, f ^ (Fintype.card Fq ^ j) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hF : ∀ x : R, FiniteField.frobeniusAlgHom Fq R x = x ^ Fintype.card Fq := fun _ => rfl
    have key : (y - ∑ j ∈ Finset.range i, f ^ (Fintype.card Fq ^ j)) ^ Fintype.card Fq =
        y ^ Fintype.card Fq - ∑ j ∈ Finset.range i, (f ^ (Fintype.card Fq ^ j)) ^ Fintype.card Fq := by
      rw [← hF, map_sub, map_sum]
      simp only [hF]
    rw [pow_succ, pow_mul, ih, key, hy, Finset.sum_range_succ']
    simp only [← pow_mul, ← pow_succ, pow_zero, pow_one]
    ring

end Basic

section Field

variable (Fq : Type) [Field Fq] [Fintype Fq]
variable (A K : Type) [CommRing A] [Field K] [Algebra A K] [Algebra Fq A] [Algebra Fq K]
  [IsScalarTower Fq A K]

/-- The Artin-Schreier polynomial `X^q - X + f`: its roots `y` satisfy `y - y^q = f`
(Katz's sign-changed Artin-Schreier map `x ↦ x - x^q`). -/
noncomputable def asPoly (f : A) : K[X] := X ^ Fintype.card Fq - X + C (algebraMap A K f)

theorem cast_card_eq_zero : ((Fintype.card Fq : ℕ) : K) = 0 := by
  rw [← map_natCast (algebraMap Fq K), FiniteField.cast_card_eq_zero, map_zero]

theorem asPoly_ne_zero (f : A) : asPoly Fq A K f ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [asPoly, natDegree_add_C, FiniteField.X_pow_card_sub_X_natDegree_eq K (one_lt_card Fq),
    natDegree_zero] at this
  exact (Nat.zero_lt_of_lt (one_lt_card Fq)).ne' this

theorem asPoly_separable (f : A) : (asPoly Fq A K f).Separable := by
  refine ⟨0, -1, ?_⟩
  have hd : derivative (asPoly Fq A K f) = -1 := by
    simp [asPoly, derivative_X_pow, cast_card_eq_zero Fq K]
  rw [hd]
  ring

/-- The splitting field of `X^q - X + f` inside `K̄`. -/
noncomputable def asField (f : A) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K ((asPoly Fq A K f).rootSet (AlgebraicClosure K))

instance asField_isSplittingField (f : A) :
    (asPoly Fq A K f).IsSplittingField K (asField Fq A K f) :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance asField_finiteDimensional (f : A) : FiniteDimensional K (asField Fq A K f) :=
  IsSplittingField.finiteDimensional _ (asPoly Fq A K f)

instance asField_isGalois (f : A) : IsGalois K (asField Fq A K f) :=
  IsGalois.of_separable_splitting_field (asPoly_separable Fq A K f)

theorem root_pow_card {f : A} {y : AlgebraicClosure K}
    (hy : y ∈ (asPoly Fq A K f).rootSet (AlgebraicClosure K)) :
    y ^ Fintype.card Fq = y - algebraMap A (AlgebraicClosure K) f := by
  rw [mem_rootSet] at hy
  have h := hy.2
  simp only [asPoly, map_add, map_sub, map_pow, aeval_X, aeval_C] at h
  rw [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K)]
  linear_combination h

theorem mem_rootSet_of_pow_card {f : A} {y : AlgebraicClosure K}
    (hy : y ^ Fintype.card Fq = y - algebraMap A (AlgebraicClosure K) f) :
    y ∈ (asPoly Fq A K f).rootSet (AlgebraicClosure K) := by
  rw [mem_rootSet]
  refine ⟨asPoly_ne_zero Fq A K f, ?_⟩
  simp only [asPoly, map_add, map_sub, map_pow, aeval_X, aeval_C]
  rw [← IsScalarTower.algebraMap_apply A K (AlgebraicClosure K), hy]
  ring

theorem asPolyA_monic (f : A) : (X ^ Fintype.card Fq - X + C f : A[X]).Monic := by
  have h1 : (1 : WithBot ℕ) < (Fintype.card Fq : WithBot ℕ) := by exact_mod_cast one_lt_card Fq
  have h0 : (0 : WithBot ℕ) < (Fintype.card Fq : WithBot ℕ) :=
    by exact_mod_cast Nat.zero_lt_of_lt (one_lt_card Fq)
  have he : (X ^ Fintype.card Fq - X + C f : A[X]) = X ^ Fintype.card Fq + (C f - X) := by ring
  rw [he]
  exact monic_X_pow_add ((degree_sub_le _ _).trans_lt
    (max_lt (degree_C_le.trans_lt h0) (degree_X_le.trans_lt h1)))

/-- Every inertia group of `Gal(L/K)` on the integral closure of `A` in `L = K(y)` is trivial:
`σ y - y` is a `q`-th power fixed point lying in the prime, hence `0`. -/
theorem asField_mem_unramSet (f : A) : asField Fq A K f ∈ unramSet A K := by
  refine ⟨inferInstance, inferInstance, fun Q hQ => ?_⟩
  rw [eq_bot_iff]
  intro τ hτ
  rw [Subgroup.mem_bot]
  obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ y : asField Fq A K f,
      σ (y : AlgebraicClosure K) = ((τ y : asField Fq A K f) : AlgebraicClosure K) :=
    ⟨τ.liftNormal (AlgebraicClosure K), fun y => τ.liftNormal_commutes (AlgebraicClosure K) y⟩
  have hF : ∀ x : AlgebraicClosure K,
      FiniteField.frobeniusAlgHom Fq (AlgebraicClosure K) x = x ^ Fintype.card Fq := fun _ => rfl
  have hσA : σ (algebraMap A (AlgebraicClosure K) f) = algebraMap A (AlgebraicClosure K) f := by
    rw [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K), AlgEquiv.commutes]
  have hfix : ∀ y ∈ (asPoly Fq A K f).rootSet (AlgebraicClosure K), σ y = y := by
    intro y hy
    have hyL : y ∈ asField Fq A K f := IntermediateField.subset_adjoin K _ hy
    have hroot := root_pow_card Fq A K hy
    have hint : IsIntegral A (⟨y, hyL⟩ : asField Fq A K f) := by
      refine ⟨X ^ Fintype.card Fq - X + C f, asPolyA_monic Fq A f, ?_⟩
      apply Subtype.ext
      simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
      push_cast
      rw [hroot]
      simp only [IsScalarTower.algebraMap_apply A K (AlgebraicClosure K)]
      first
        | exact neg_add_eq_zero.mpr rfl
        | (simp; rfl)
        | (rw [IsScalarTower.algebraMap_apply A K (asField Fq A K f)]; simp)
    let yI : integralClosure A (asField Fq A K f) := ⟨⟨y, hyL⟩, hint⟩
    have hmem : τ • yI - yI ∈ Q := hτ yI
    have hzval : (((τ • yI - yI : integralClosure A (asField Fq A K f)) : asField Fq A K f) :
        AlgebraicClosure K) = σ y - y := by
      show ((τ ⟨y, hyL⟩ : asField Fq A K f) : AlgebraicClosure K) - y = σ y - y
      rw [hσ ⟨y, hyL⟩]
    have hσq : (σ y) ^ Fintype.card Fq = σ y - algebraMap A (AlgebraicClosure K) f := by
      rw [← map_pow, hroot, map_sub, hσA]
    have hzq : (σ y - y) ^ Fintype.card Fq = σ y - y := by
      rw [← hF, map_sub, hF, hF, hσq, hroot]
      ring
    by_contra hne
    have hz0 : σ y - y ≠ 0 := sub_ne_zero.mpr hne
    have hz1 : (σ y - y) ^ (Fintype.card Fq - 1) = 1 := by
      have : (σ y - y) ^ (Fintype.card Fq - 1) * (σ y - y) = 1 * (σ y - y) := by
        rw [← pow_succ, Nat.sub_add_cancel (one_lt_card Fq).le, one_mul, hzq]
      exact mul_right_cancel₀ hz0 this
    have hw1 : (τ • yI - yI) ^ (Fintype.card Fq - 1) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      have h := hz1
      rw [← hzval] at h
      simpa using h
    have h1 : (1 : integralClosure A (asField Fq A K f)) ∈ Q := by
      rw [← hw1]
      exact Q.pow_mem_of_mem hmem _ (Nat.sub_pos_of_lt (one_lt_card Fq))
    exact hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
  have hle : Algebra.adjoin K ((asPoly Fq A K f).rootSet (AlgebraicClosure K)) ≤
      AlgHom.equalizer σ.toAlgHom (AlgHom.id K (AlgebraicClosure K)) :=
    Algebra.adjoin_le fun y hy => hfix y hy
  ext y
  rw [AlgEquiv.one_apply, ← hσ]
  have hy : (y : AlgebraicClosure K) ∈ Algebra.adjoin K ((asPoly Fq A K f).rootSet (AlgebraicClosure K)) := by
    have h : (y : AlgebraicClosure K) ∈ (IntermediateField.adjoin K
        ((asPoly Fq A K f).rootSet (AlgebraicClosure K))).toSubalgebra := y.2
    rwa [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      fun x hx => isAlgebraic_of_mem_rootSet hx] at h
  exact hle hy

end Field

end ArtinSchreier
end RamanujanPetersson


