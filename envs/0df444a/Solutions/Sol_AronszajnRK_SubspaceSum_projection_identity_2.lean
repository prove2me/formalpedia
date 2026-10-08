-- Prove2me | solution 2 for AronszajnRK.SubspaceSum.projection_identity
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:58:28.153241+00:00
-- url     : https://prove2.me/submissions/24d34069-7713-4fa5-8267-aaa8a94a2745

import Mathlib
import Definitions.Def_AronszajnRK_SubspaceSum_sumProjection

/-!
# Aronszajn §12, Eq. (1): the finite projection identity

Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §12, Eq. (1),
p. 375 (PDF p. 39).

Write `Pᵢ` for the orthogonal projection onto the closed subspace `Fᵢ` and `P` for the
projection onto the closed join `F₁ ⊔ F₂`.  Setting `Q = (P - P₁)(P - P₂)`,
`S = P₂P₁`, `T = P₁P₂`, we show for every `m ≥ 1`:

`Q ^ m = P - ∑ k < m, (P₁ S ^ k + P₂ T ^ k - S ^ (k+1) - T ^ (k+1)) - S ^ m`.

## Proof architecture

The identity is decomposed into a purely algebraic core and a small analytic shell.

* **Algebraic core** (`AronszajnRing.projection_identity`): in any ring, elements
  `P, P₁, P₂` satisfying the seven orthogonal-projection relations
  `P² = P`, `Pᵢ² = Pᵢ`, `P Pᵢ = Pᵢ`, `Pᵢ P = Pᵢ` obey the identity.  The proof is a
  word-reduction computation: every power of `S = P₂P₁` annihilates `Q` from the left;
  the four families `P₁SᵏQ`, `P₂TᵏQ`, `Sᵏ⁺¹Q`, `Tᵏ⁺¹Q` reduce to short two-term
  expressions (`P₁SᵏQ = 0`, `P₂TᵏQ = -(Sᵏ⁺¹) + P₂Tᵏ⁺¹`, `Tᵏ⁺¹Q = -(P₁Sᵏ⁺¹) + Tᵏ⁺²`);
  and the recursion `Q^{m+1} = (P - ∑_{k<m} f k)·Q` telescopes through
  `∑_{k<m} (g k + f (k+1)) = S - S^{m+1}`.
* **Analytic shell** (`ProjAux`): the seven relations for orthogonal projections of a
  complex Hilbert space.  `P Pᵢ = Pᵢ` holds because `Fᵢ ⊆ F₁ ⊔ F₂`; `Pᵢ P = Pᵢ` because
  the join-defect `x - Px` is orthogonal to the join, hence to `Fᵢ`, and is therefore
  killed by `Pᵢ`; idempotence is characteristic of orthogonal projections.
-/

namespace AronszajnRing

variable {R : Type*} [Ring R]

/-- The master identity, purely algebraic. -/
theorem projection_identity (P P₁ P₂ : R) (m : ℕ) (hm : 1 ≤ m)
    (hPP : P * P = P) (hP₁P₁ : P₁ * P₁ = P₁) (hP₂P₂ : P₂ * P₂ = P₂)
    (hPP₁ : P * P₁ = P₁) (hPP₂ : P * P₂ = P₂)
    (hP₁P : P₁ * P = P₁) (hP₂P : P₂ * P = P₂) :
    (((P - P₁) * (P - P₂))) ^ m =
      P - (∑ k ∈ Finset.range m,
        (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
          (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) -
        (P₂ * P₁) ^ m := by
  classical
  set S := P₂ * P₁ with hS
  set T := P₁ * P₂ with hT
  set Q := (P - P₁) * (P - P₂) with hQ
  -- ### basic word reductions
  have hSP : S * P = S := by rw [hS, mul_assoc, hP₁P]
  have hSP₂ : S * P₂ = P₂ * T := by rw [hS, hT, mul_assoc]
  have hSP₁ : S * P₁ = S := by rw [hS, mul_assoc, hP₁P₁]
  have hST : S * T = P₂ * T := by
    have hmid : P₁ * (P₁ * P₂) = P₁ * P₂ := by rw [← mul_assoc, hP₁P₁]
    rw [hS, hT, mul_assoc, hmid]
  have hTP : T * P = T := by rw [hT, mul_assoc, hP₂P]
  have hTP₂ : T * P₂ = T := by rw [hT, mul_assoc, hP₂P₂]
  have hTP₁ : T * P₁ = P₁ * S := by rw [hT, hS, mul_assoc]
  have hPT : P * T = T := by rw [hT, ← mul_assoc, hPP₁, ← hT]
  -- ### expansion of Q
  have hQexp : Q = P - P₂ - P₁ + T := by
    rw [hQ]
    have e : (P - P₁) * (P - P₂) = P * P - P₁ * P - (P * P₂ - P₁ * P₂) := by
      rw [mul_sub, sub_mul, sub_mul]
    rw [e, hPP, hPP₂, hP₁P, hT]
    abel
  -- ### P * Q = Q
  have hPQ : P * Q = Q := by
    rw [hQexp, mul_add, mul_sub, mul_sub, hPP, hPP₂, hPP₁, hPT, ← hQexp]
  -- ### S annihilates Q from the left
  have hSQ : S * Q = 0 := by
    rw [hQexp, mul_add, mul_sub, mul_sub, hSP, hSP₂, hSP₁, hST]
    abel
  have hSpowQ : ∀ j : ℕ, S ^ (j + 1) * Q = 0 := by
    intro j
    induction j with
    | zero => simpa [pow_one] using hSQ
    | succ j ih => rw [pow_succ, mul_assoc, hSQ, mul_zero]
  -- ### words: (P₁ * S ^ k) against P, P₂, P₁, T
  have w1 : ∀ k : ℕ, P₁ * S ^ k * P = P₁ * S ^ k := by
    intro k
    induction k with
    | zero => simpa using hP₁P
    | succ k _ => rw [pow_succ, mul_assoc, mul_assoc, hSP]
  have w2 : ∀ k : ℕ, P₁ * S ^ k * P₂ = T ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp only [pow_zero, mul_one, Nat.zero_add, pow_one, hT]
    | succ k ih =>
      rw [pow_succ, pow_succ, mul_assoc, mul_assoc, hSP₂, ← mul_assoc, ← mul_assoc, ih]
  have w3 : ∀ k : ℕ, P₁ * S ^ k * P₁ = P₁ * S ^ k := by
    intro k
    induction k with
    | zero => simpa using hP₁P₁
    | succ k _ => rw [pow_succ, mul_assoc, mul_assoc, hSP₁]
  have w4 : ∀ k : ℕ, P₁ * S ^ k * T = T ^ (k + 1) := by
    intro k
    conv_lhs => rw [hT, ← mul_assoc]
    rw [w3 k, w2 k]
  -- ### words: (P₂ * T ^ k) against P, P₂, P₁, T
  have v1 : ∀ k : ℕ, P₂ * T ^ k * P = P₂ * T ^ k := by
    intro k
    induction k with
    | zero => simpa using hP₂P
    | succ k _ => rw [pow_succ, mul_assoc, mul_assoc, hTP]
  have v2 : ∀ k : ℕ, P₂ * T ^ k * P₂ = P₂ * T ^ k := by
    intro k
    induction k with
    | zero => simpa using hP₂P₂
    | succ k _ => rw [pow_succ, mul_assoc, mul_assoc, hTP₂]
  have v3 : ∀ k : ℕ, P₂ * T ^ k * P₁ = S ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp only [pow_zero, mul_one, Nat.zero_add, pow_one, hS]
    | succ k ih =>
      rw [pow_succ, pow_succ, mul_assoc, mul_assoc, hTP₁, ← mul_assoc, ← mul_assoc, ih]
  have v4 : ∀ k : ℕ, P₂ * T ^ k * T = P₂ * T ^ (k + 1) := by
    intro k
    calc P₂ * T ^ k * T = P₂ * (T ^ k * T) := mul_assoc _ _ _
      _ = P₂ * T ^ (k + 1) := by rw [pow_succ]
  -- ### words: T ^ k against P₁
  have u1 : ∀ k : ℕ, T ^ k * P₁ = P₁ * S ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, mul_assoc, hTP₁, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  -- ### pointwise expansion of `X * Q`
  have hExp : ∀ X : R, X * Q = X * P - X * P₂ - X * P₁ + X * T := by
    intro X
    rw [hQexp, mul_add, mul_sub, mul_sub]
  -- ### T * Q
  have hTQ : T * Q = -(P₁ * S) + T * T := by
    rw [hExp, hTP, hTP₂, hTP₁]
    abel
  -- ### higher powers of T against Q
  have hTpowQ : ∀ j : ℕ, T ^ (j + 1) * Q = -(P₁ * S ^ (j + 1)) + T ^ (j + 1 + 1) := by
    intro j
    induction j with
    | zero => simpa [pow_one, pow_two] using hTQ
    | succ j ih =>
      rw [pow_succ, mul_assoc, hTQ, mul_add, mul_neg, ← mul_assoc, u1, mul_assoc,
        ← pow_succ, ← mul_assoc, ← pow_succ, ← pow_succ]
  -- ### the summand family F and the correction family g
  set F : ℕ → R := fun k => P₁ * S ^ k + P₂ * T ^ k - S ^ (k + 1) - T ^ (k + 1) with hF
  set g : ℕ → R := fun k => S ^ (k + 1) - P₁ * S ^ (k + 1) - P₂ * T ^ (k + 1)
    + T ^ (k + 1 + 1) with hg
  -- ### each summand kills `Q` up to `- g k`
  have key : ∀ k : ℕ, F k * Q = -(g k) := by
    intro k
    have hA : P₁ * S ^ k * Q = 0 := by
      rw [hExp, w1 k, w2 k, w3 k, w4 k]; abel
    have hB : P₂ * T ^ k * Q = -(S ^ (k + 1)) + P₂ * T ^ (k + 1) := by
      rw [hExp, v1 k, v2 k, v3 k, v4 k]; abel
    have hC : S ^ (k + 1) * Q = 0 := hSpowQ k
    have hD : T ^ (k + 1) * Q = -(P₁ * S ^ (k + 1)) + T ^ (k + 1 + 1) := hTpowQ k
    have hDistr : ∀ A B C D : R,
        (A + B - C - D) * Q = A * Q + B * Q - C * Q - D * Q := by
      intro A B C D; rw [sub_mul, sub_mul, add_mul]
    show (P₁ * S ^ k + P₂ * T ^ k - S ^ (k + 1) - T ^ (k + 1)) * Q
        = -(S ^ (k + 1) - P₁ * S ^ (k + 1) - P₂ * T ^ (k + 1) + T ^ (k + 1 + 1))
    rw [hDistr, hA, hB, hC, hD]
    abel
  -- ### base case m = 1
  have hbase : Q ^ 1 = P - ∑ k ∈ Finset.range 1, F k - S ^ 1 := by
    rw [Finset.sum_range_one]
    show Q ^ 1 = P - (P₁ * S ^ 0 + P₂ * T ^ 0 - S ^ (0 + 1) - T ^ (0 + 1)) - S ^ 1
    simp only [pow_one, pow_zero, mul_one, Nat.zero_add]
    rw [hQexp]
    abel
  -- ### telescoping relation
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), g k
      + ∑ k ∈ Finset.range (n + 1), F (k + 1) = S ^ 1 - S ^ (n + 1 + 1) := by
    intro n
    have h : ∀ k ∈ Finset.range (n + 1), g k + F (k + 1) = S ^ (k + 1) - S ^ (k + 1 + 1) := by
      intro k _
      show (S ^ (k + 1) - P₁ * S ^ (k + 1) - P₂ * T ^ (k + 1) + T ^ (k + 1 + 1))
          + (P₁ * S ^ (k + 1) + P₂ * T ^ (k + 1) - S ^ (k + 1 + 1) - T ^ (k + 1 + 1))
          = S ^ (k + 1) - S ^ (k + 1 + 1)
      abel
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl h]
    exact Finset.sum_range_sub' (fun k => S ^ (k + 1)) (n + 1)
  -- ### main induction
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  clear hm
  induction n with
  | zero => show Q ^ (0 + 1) = _; exact hbase
  | succ n ih =>
    -- ih : Q ^ (n+1) = P - ∑ range (n+1) F - S ^ (n+1)
    have hgoal : Q + ∑ k ∈ Finset.range (n + 1), g k
        = P - ∑ k ∈ Finset.range (n + 1 + 1), F k - S ^ (n + 1 + 1) := by
      have hP' : P = Q + F 0 + S ^ 1 := by
        have h1 := hbase
        rw [Finset.sum_range_one, pow_one] at h1
        rw [h1]; abel
      have hsum : ∑ k ∈ Finset.range (n + 1 + 1), F k
          = ∑ k ∈ Finset.range (n + 1), F (k + 1) + F 0 := Finset.sum_range_succ' F (n + 1)
      rw [hP', hsum]
      have ht := htel n
      have rearr : Q + F 0 + S ^ 1
          - (∑ k ∈ Finset.range (n + 1), F (k + 1) + F 0) - S ^ (n + 1 + 1)
          = Q + ∑ k ∈ Finset.range (n + 1), g k := by
        calc Q + F 0 + S ^ 1 - (∑ k ∈ Finset.range (n + 1), F (k + 1) + F 0) - S ^ (n + 1 + 1)
            = Q + (S ^ 1 - S ^ (n + 1 + 1) - ∑ k ∈ Finset.range (n + 1), F (k + 1)) := by abel
          _ = Q + (∑ k ∈ Finset.range (n + 1), g k
              + ∑ k ∈ Finset.range (n + 1), F (k + 1)
              - ∑ k ∈ Finset.range (n + 1), F (k + 1)) := by rw [ht]
          _ = Q + ∑ k ∈ Finset.range (n + 1), g k := by abel
      rw [rearr]
    rw [pow_succ, ih, sub_mul, sub_mul, hSpowQ n, sub_zero, hPQ,
      Finset.sum_mul, Finset.sum_congr rfl (fun k _ => key k),
      Finset.sum_neg_distrib, sub_neg_eq_add]
    exact hgoal

end AronszajnRing

open AronszajnRK.SubspaceSum

open scoped InnerProductSpace

namespace ProjAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (F₁ F₂ : ClosedSubmodule ℂ E)

/-- Self-adjointness of an orthogonal projection. -/
lemma inner_symm {U : Submodule ℂ E} [U.HasOrthogonalProjection] (x y : E) :
    inner ℂ (U.starProjection x) y = inner ℂ x (U.starProjection y) := by
  have h1 : ⟪x - U.starProjection x, U.starProjection y⟫_ℂ = 0 :=
    U.starProjection_inner_eq_zero x (U.starProjection y)
      (Submodule.starProjection_apply_mem U y)
  have h2 : ⟪U.starProjection x, y - U.starProjection y⟫_ℂ = 0 := by
    rw [← inner_conj_symm, U.starProjection_inner_eq_zero y (U.starProjection x)
      (Submodule.starProjection_apply_mem U x), map_zero]
  calc inner ℂ (U.starProjection x) y
      = inner ℂ (U.starProjection x) (U.starProjection y + (y - U.starProjection y)) := by
        rw [inner_add_right, inner_sub_right]; ring
    _ = inner ℂ (U.starProjection x) (U.starProjection y) := by
        rw [inner_add_right, h2, add_zero]
    _ = inner ℂ (U.starProjection x) (U.starProjection y)
        + inner ℂ (x - U.starProjection x) (U.starProjection y) := by
        rw [h1, add_zero]
    _ = inner ℂ x (U.starProjection y) := by
        rw [← inner_add_left]; congr 1; abel

/-- Membership in the closed join from membership in a factor. -/
lemma mem_join_left {x : E} (hx : x ∈ (F₁ : Submodule ℂ E)) :
    x ∈ ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) := by
  have heq : ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E)
      = Submodule.closure (((F₁ : Submodule ℂ E)) ⊔ ((F₂ : Submodule ℂ E))) := rfl
  rw [heq]
  have hset : x ∈ (((F₁ : Submodule ℂ E)) ⊔ ((F₂ : Submodule ℂ E))) :=
    Submodule.mem_sup.mpr ⟨x, hx, 0, Submodule.zero_mem _, add_zero _⟩
  exact subset_closure (SetLike.mem_coe.2 hset)

lemma mem_join_right {x : E} (hx : x ∈ (F₂ : Submodule ℂ E)) :
    x ∈ ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) := by
  have heq : ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E)
      = Submodule.closure (((F₁ : Submodule ℂ E)) ⊔ ((F₂ : Submodule ℂ E))) := rfl
  rw [heq]
  have hset : x ∈ (((F₁ : Submodule ℂ E)) ⊔ ((F₂ : Submodule ℂ E))) :=
    Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, x, hx, zero_add _⟩
  exact subset_closure (SetLike.mem_coe.2 hset)

/-- The join projection fixes both factor projections. -/
lemma join_proj₁ (x : E) :
    sumProjection F₁ F₂ (((F₁ : Submodule ℂ E).starProjection) x)
      = ((F₁ : Submodule ℂ E).starProjection) x := by
  show ((↑(F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E)).starProjection
      (((F₁ : Submodule ℂ E).starProjection) x)
    = ((F₁ : Submodule ℂ E).starProjection) x
  have hmem : ((F₁ : Submodule ℂ E).starProjection) x ∈ (F₁ : Submodule ℂ E) :=
    Submodule.starProjection_apply_mem _ x
  exact Submodule.starProjection_eq_self_iff.mpr (mem_join_left F₁ F₂ hmem)

lemma join_proj₂ (x : E) :
    sumProjection F₁ F₂ (((F₂ : Submodule ℂ E).starProjection) x)
      = ((F₂ : Submodule ℂ E).starProjection) x := by
  show ((↑(F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E)).starProjection
      (((F₂ : Submodule ℂ E).starProjection) x)
    = ((F₂ : Submodule ℂ E).starProjection) x
  have hmem : ((F₂ : Submodule ℂ E).starProjection) x ∈ (F₂ : Submodule ℂ E) :=
    Submodule.starProjection_apply_mem _ x
  exact Submodule.starProjection_eq_self_iff.mpr (mem_join_right F₁ F₂ hmem)


/-- The factors sit inside the closed join (as submodules). -/
lemma le_join_left : (F₁ : Submodule ℂ E) ≤ ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) :=
  fun x hx => mem_join_left F₁ F₂ hx

/-- A vector in the join's orthogonal is in each factor's orthogonal. -/
lemma ortho_join_le_ortho₁ {x : E}
    (hx : x ∈ Submodule.orthogonal ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E)) :
    x ∈ Submodule.orthogonal (F₁ : Submodule ℂ E) :=
  Submodule.orthogonal_le (le_join_left F₁ F₂) hx

/-- `x - P x` lies in the join's orthogonal. -/
lemma sub_join_proj_mem_ortho (x : E) :
    x - sumProjection F₁ F₂ x
      ∈ Submodule.orthogonal ((F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E) := by
  have h : ∀ U : Submodule ℂ E, [U.HasOrthogonalProjection] ->
      x - U.starProjection x ∈ Submodule.orthogonal U :=
    fun U _ => U.sub_starProjection_mem_orthogonal x
  exact h _

/-- A vector orthogonal to `U` projects to zero. -/
lemma starProjection_of_mem_orthogonal {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    {v : E} (hv : v ∈ Submodule.orthogonal U) : U.starProjection v = 0 :=
  U.eq_starProjection_of_mem_orthogonal' U.zero_mem hv (zero_add v).symm

/-- The factor projections kill the join-defect. -/
lemma factor_proj_sub_join₁ (x : E) :
    ((F₁ : Submodule ℂ E).starProjection) (x - sumProjection F₁ F₂ x) = 0 :=
  starProjection_of_mem_orthogonal (ortho_join_le_ortho₁ F₁ F₂ (sub_join_proj_mem_ortho F₁ F₂ x))

lemma factor_proj_sub_join₂ (x : E) :
    ((F₂ : Submodule ℂ E).starProjection) (x - sumProjection F₁ F₂ x) = 0 :=
  starProjection_of_mem_orthogonal
    (Submodule.orthogonal_le (fun x hx => mem_join_right F₁ F₂ hx)
      (sub_join_proj_mem_ortho F₁ F₂ x))

/-! ### The seven operator relations -/

/-- `P * P = P`: idempotence of the join projection. -/
lemma join_proj_mul_self :
    sumProjection F₁ F₂ * sumProjection F₁ F₂ = sumProjection F₁ F₂ := by
  ext x
  exact Submodule.eq_starProjection_of_mem_orthogonal'
    (Submodule.starProjection_apply_mem ((↑(F₁ ⊔ F₂ : ClosedSubmodule ℂ E) : Submodule ℂ E)) x)
    (Submodule.zero_mem _) (by simp)

/-- `P₁ * P = P₁`: the factor projection factors through the join. -/
lemma proj₁_mul_join :
    ((F₁ : Submodule ℂ E).starProjection) * sumProjection F₁ F₂
      = ((F₁ : Submodule ℂ E).starProjection) := by
  ext x
  have hf := factor_proj_sub_join₁ F₁ F₂ x
  have hsplit : sumProjection F₁ F₂ x = x - (x - sumProjection F₁ F₂ x) := by
    rw [sub_sub_cancel]
  show ((F₁ : Submodule ℂ E).starProjection) (sumProjection F₁ F₂ x)
      = ((F₁ : Submodule ℂ E).starProjection) x
  rw [hsplit, map_sub, hf, sub_zero]

lemma proj₂_mul_join :
    ((F₂ : Submodule ℂ E).starProjection) * sumProjection F₁ F₂
      = ((F₂ : Submodule ℂ E).starProjection) := by
  ext x
  have hf := factor_proj_sub_join₂ F₁ F₂ x
  have hsplit : sumProjection F₁ F₂ x = x - (x - sumProjection F₁ F₂ x) := by
    rw [sub_sub_cancel]
  show ((F₂ : Submodule ℂ E).starProjection) (sumProjection F₁ F₂ x)
      = ((F₂ : Submodule ℂ E).starProjection) x
  rw [hsplit, map_sub, hf, sub_zero]

/-- `P * P₁ = P₁`: the join projection fixes each factor projection. -/
lemma join_mul_proj₁ :
    sumProjection F₁ F₂ * ((F₁ : Submodule ℂ E).starProjection)
      = ((F₁ : Submodule ℂ E).starProjection) := by
  ext x
  exact join_proj₁ F₁ F₂ x

lemma join_mul_proj₂ :
    sumProjection F₁ F₂ * ((F₂ : Submodule ℂ E).starProjection)
      = ((F₂ : Submodule ℂ E).starProjection) := by
  ext x
  exact join_proj₂ F₁ F₂ x

/-- `P₁ * P₁ = P₁`: idempotence of a factor projection. -/
lemma proj₁_mul_self :
    ((F₁ : Submodule ℂ E).starProjection) * ((F₁ : Submodule ℂ E).starProjection)
      = ((F₁ : Submodule ℂ E).starProjection) := by
  ext x
  show ((F₁ : Submodule ℂ E).starProjection) (((F₁ : Submodule ℂ E).starProjection) x)
      = ((F₁ : Submodule ℂ E).starProjection) x
  have hmem : ((F₁ : Submodule ℂ E).starProjection) x ∈ (F₁ : Submodule ℂ E) :=
    Submodule.starProjection_apply_mem ((F₁ : Submodule ℂ E)) x
  exact Submodule.eq_starProjection_of_mem_orthogonal' hmem (Submodule.zero_mem _) (by simp)

lemma proj₂_mul_self :
    ((F₂ : Submodule ℂ E).starProjection) * ((F₂ : Submodule ℂ E).starProjection)
      = ((F₂ : Submodule ℂ E).starProjection) := by
  ext x
  show ((F₂ : Submodule ℂ E).starProjection) (((F₂ : Submodule ℂ E).starProjection) x)
      = ((F₂ : Submodule ℂ E).starProjection) x
  have hmem : ((F₂ : Submodule ℂ E).starProjection) x ∈ (F₂ : Submodule ℂ E) :=
    Submodule.starProjection_apply_mem ((F₂ : Submodule ℂ E)) x
  exact Submodule.eq_starProjection_of_mem_orthogonal' hmem (Submodule.zero_mem _) (by simp)

end ProjAux


namespace AronszajnRK.SubspaceSum

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§12, Eq. (1), p. 375 (PDF p. 39). The finite projection identity for m ≥ 1.
The `Finset.range m` index `k` represents the paper's index `k+1`. -/
theorem projection_identity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (m : ℕ) (hm : 1 ≤ m) :
    let P : E →L[ℂ] E := sumProjection F₁ F₂
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    ((P - P₁) * (P - P₂)) ^ m =
      P - (∑ k ∈ Finset.range m,
        (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
          (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) -
        (P₂ * P₁) ^ m :=
  AronszajnRing.projection_identity (sumProjection F₁ F₂)
    ((F₁ : Submodule ℂ E).starProjection) ((F₂ : Submodule ℂ E).starProjection) m hm
    (ProjAux.join_proj_mul_self F₁ F₂)
    (ProjAux.proj₁_mul_self F₁)
    (ProjAux.proj₂_mul_self F₂)
    (ProjAux.join_mul_proj₁ F₁ F₂)
    (ProjAux.join_mul_proj₂ F₁ F₂)
    (ProjAux.proj₁_mul_join F₁ F₂)
    (ProjAux.proj₂_mul_join F₁ F₂)

end AronszajnRK.SubspaceSum

/-- Solution entry point. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (F₁ F₂ : ClosedSubmodule ℂ E) (m : ℕ) (hm : 1 ≤ m) :
    let P : E →L[ℂ] E := AronszajnRK.SubspaceSum.sumProjection F₁ F₂
    let P₁ : E →L[ℂ] E := (F₁ : Submodule ℂ E).starProjection
    let P₂ : E →L[ℂ] E := (F₂ : Submodule ℂ E).starProjection
    ((P - P₁) * (P - P₂)) ^ m =
      P - (∑ k ∈ Finset.range m,
        (P₁ * (P₂ * P₁) ^ k + P₂ * (P₁ * P₂) ^ k -
          (P₂ * P₁) ^ (k + 1) - (P₁ * P₂) ^ (k + 1))) -
        (P₂ * P₁) ^ m :=
  AronszajnRK.SubspaceSum.projection_identity F₁ F₂ m hm
