-- Prove2me | Definitions.Def_tangent_projection_algebra
-- name    : tangent_projection_algebra
-- status  : Definition
-- author  : @Grace
-- created : 2026-06-22T02:08:15.658271+00:00
-- url     : https://prove2.me/theorems/d5ee6d5c-d77f-42cc-a6ea-78e0cb389440
-- title:
--   Algebra of the SVD tangent-space projections
-- statement:
--   Structural algebra of the SVD tangent-space projections from Candes-Recht matrix completion (Section 3). For the left/right/two-sided singular projections (kernels P_c(i,a)=sum_k u_k(i)u_k(a) and P_r(b,j)=sum_k v_k(b)v_k(j)), this file establishes: kernel symmetry and idempotence; the composition multiplication table for L,R,T=LR=RL under the Frobenius inner product (LL=L, RR=R, LR=RL=T, LT=TL=RT=TR=TT=T); additivity/subtractivity (linearity) of each projection; self-adjointness of each piece and of the full tangent projection P_T with respect to matrixInner; and idempotence P_T P_T=P_T. These are the reusable structural lemmas underlying the orthogonal decomposition R^{n1 x n2}=T (+) T_perp.
-- source:
--   Candes, Emmanuel J. and Recht, Benjamin, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, Section 3.

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion
open scoped BigOperators

namespace TangentAlgebra

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- column projector kernel -/
noncomputable def Pc (S : SVD M r) (i a : Fin n1) : Real := ∑ k : Fin r, S.u k i * S.u k a
/-- row projector kernel -/
noncomputable def Pr (S : SVD M r) (b j : Fin n2) : Real := ∑ k : Fin r, S.v k b * S.v k j

lemma Pc_symm (S : SVD M r) (i a : Fin n1) : Pc S i a = Pc S a i := by
  unfold Pc; exact Finset.sum_congr rfl (fun k _ => by ring)

lemma Pr_symm (S : SVD M r) (b j : Fin n2) : Pr S b j = Pr S j b := by
  unfold Pr; exact Finset.sum_congr rfl (fun k _ => by ring)

-- idempotence: ∑_a Pc i a * Pc a j = Pc i j
lemma Pc_idem (S : SVD M r) (i j : Fin n1) :
    ∑ a : Fin n1, Pc S i a * Pc S a j = Pc S i j := by
  unfold Pc
  have : ∀ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.u l j)
      = ∑ k : Fin r, ∑ l : Fin r, S.u k i * S.u l j * (S.u k a * S.u l a) := by
    intro a
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [Finset.sum_congr rfl (fun a _ => this a)]
  have step : ∑ a : Fin n1, ∑ k : Fin r, ∑ l : Fin r, S.u k i * S.u l j * (S.u k a * S.u l a)
      = ∑ k : Fin r, ∑ l : Fin r, S.u k i * S.u l j * (∑ a : Fin n1, S.u k a * S.u l a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [step]
  have orth : ∀ k l : Fin r, (∑ a : Fin n1, S.u k a * S.u l a) = if k = l then 1 else 0 :=
    S.u_orthonormal
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by rw [orth k l]))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl; rw [if_neg (Ne.symm hl)]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

-- idempotence for the row kernel: ∑_b Pr i b * Pr b j = Pr i j
lemma Pr_idem (S : SVD M r) (i j : Fin n2) :
    ∑ b : Fin n2, Pr S i b * Pr S b j = Pr S i j := by
  unfold Pr
  have : ∀ b : Fin n2, (∑ k : Fin r, S.v k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j)
      = ∑ k : Fin r, ∑ l : Fin r, S.v k i * S.v l j * (S.v k b * S.v l b) := by
    intro b
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [Finset.sum_congr rfl (fun b _ => this b)]
  have step : ∑ b : Fin n2, ∑ k : Fin r, ∑ l : Fin r, S.v k i * S.v l j * (S.v k b * S.v l b)
      = ∑ k : Fin r, ∑ l : Fin r, S.v k i * S.v l j * (∑ b : Fin n2, S.v k b * S.v l b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [step]
  have orth : ∀ k l : Fin r, (∑ b : Fin n2, S.v k b * S.v l b) = if k = l then 1 else 0 :=
    S.v_orthonormal
  rw [Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by rw [orth k l]))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl; rw [if_neg (Ne.symm hl)]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

/-! ### Rewrite the three projections in kernel form. -/

lemma left_apply (S : SVD M r) (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    leftSingularProjection S X i j = ∑ a : Fin n1, Pc S i a * X a j := rfl

lemma right_apply (S : SVD M r) (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    rightSingularProjection S X i j = ∑ b : Fin n2, X i b * Pr S b j := rfl

lemma two_apply (S : SVD M r) (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    twoSidedSingularProjection S X i j
      = ∑ a : Fin n1, ∑ b : Fin n2, Pc S i a * X a b * Pr S b j := rfl

/-! ### matrixInner bilinearity helpers. -/

lemma inner_sub_left {n1 n2 : Nat} (A B C : RealMatrix n1 n2) :
    matrixInner (A - B) C = matrixInner A C - matrixInner B C := by
  unfold matrixInner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Matrix.sub_apply]; ring

lemma inner_sub_right {n1 n2 : Nat} (A B C : RealMatrix n1 n2) :
    matrixInner A (B - C) = matrixInner A B - matrixInner A C := by
  unfold matrixInner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Matrix.sub_apply]; ring

lemma inner_add_left {n1 n2 : Nat} (A B C : RealMatrix n1 n2) :
    matrixInner (A + B) C = matrixInner A C + matrixInner B C := by
  unfold matrixInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Matrix.add_apply]; ring

lemma inner_add_right {n1 n2 : Nat} (A B C : RealMatrix n1 n2) :
    matrixInner A (B + C) = matrixInner A B + matrixInner A C := by
  unfold matrixInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Matrix.add_apply]; ring

/-! ### Self-adjointness of each piece. -/

lemma left_selfadjoint (S : SVD M r) (Y H : RealMatrix n1 n2) :
    matrixInner (leftSingularProjection S Y) H
      = matrixInner Y (leftSingularProjection S H) := by
  unfold matrixInner
  have lhs : ∑ i : Fin n1, ∑ j : Fin n2, leftSingularProjection S Y i j * H i j
      = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2, Pc S i a * Y a j * H i j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [left_apply, Finset.sum_mul]
  have rhs : ∑ i : Fin n1, ∑ j : Fin n2, Y i j * leftSingularProjection S H i j
      = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2, Pc S i a * Y i j * H a j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [left_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => by ring)
  rw [lhs, rhs]
  -- swap the i,a outer sums on the LHS and use symmetry of Pc
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pc_symm S i a]

lemma right_selfadjoint (S : SVD M r) (Y H : RealMatrix n1 n2) :
    matrixInner (rightSingularProjection S Y) H
      = matrixInner Y (rightSingularProjection S H) := by
  unfold matrixInner
  have lhs : ∑ i : Fin n1, ∑ j : Fin n2, rightSingularProjection S Y i j * H i j
      = ∑ i : Fin n1, ∑ j : Fin n2, ∑ b : Fin n2, Y i b * Pr S b j * H i j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [right_apply, Finset.sum_mul]
  have rhs : ∑ i : Fin n1, ∑ j : Fin n2, Y i j * rightSingularProjection S H i j
      = ∑ i : Fin n1, ∑ j : Fin n2, ∑ b : Fin n2, Y i j * H i b * Pr S b j := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [right_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => by ring)
  rw [lhs, rhs]
  -- for each i, swap j and b and use Pr symmetry
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Pr_symm S b j]; ring

/-- Canonical fully-expanded form of the two-sided self-adjointness identity:
both `⟨T Y, H⟩` and `⟨Y, T H⟩` equal this. -/
lemma two_canonical_lhs (S : SVD M r) (Y H : RealMatrix n1 n2) :
    ∑ i : Fin n1, ∑ j : Fin n2, twoSidedSingularProjection S Y i j * H i j
      = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2, ∑ b : Fin n2,
          Pc S i a * Pr S b j * Y a b * H i j := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- ∑_j (∑_a ∑_b Pc i a * Y a b * Pr b j) * H i j
  rw [show (∑ j : Fin n2, twoSidedSingularProjection S Y i j * H i j)
        = ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            Pc S i a * Pr S b j * Y a b * H i j from ?_]
  · rw [Finset.sum_comm]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [two_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => by ring)

lemma two_canonical_rhs (S : SVD M r) (Y H : RealMatrix n1 n2) :
    ∑ i : Fin n1, ∑ j : Fin n2, Y i j * twoSidedSingularProjection S H i j
      = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2, ∑ b : Fin n2,
          Pc S i a * Pr S b j * Y i j * H a b := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (∑ j : Fin n2, Y i j * twoSidedSingularProjection S H i j)
        = ∑ j : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            Pc S i a * Pr S b j * Y i j * H a b from ?_]
  · rw [Finset.sum_comm]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [two_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => by ring)

lemma two_selfadjoint (S : SVD M r) (Y H : RealMatrix n1 n2) :
    matrixInner (twoSidedSingularProjection S Y) H
      = matrixInner Y (twoSidedSingularProjection S H) := by
  unfold matrixInner
  rw [two_canonical_lhs, two_canonical_rhs]
  -- LHS: ∑ i ∑ a ∑ j ∑ b  Pc i a * Pr b j * Y a b * H i j
  -- RHS: ∑ i ∑ a ∑ j ∑ b  Pc i a * Pr b j * Y i j * H a b
  -- Rewrite LHS summand with kernel symmetry to expose the i↔a, j↔b reindex.
  rw [show (∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2, ∑ b : Fin n2,
          Pc S i a * Pr S b j * Y a b * H i j)
        = ∑ i : Fin n1, ∑ a : Fin n1, ∑ j : Fin n2, ∑ b : Fin n2,
          Pc S a i * Pr S j b * Y a b * H i j from ?_]
  · -- Now LHS = ∑ i a j b, Pc a i * Pr j b * Y a b * H i j; reindex i↔a, j↔b ↦ RHS.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Pc_symm S i a, Pr_symm S b j]

/-! ### Composition rules for the three pieces (as matrix equalities). -/

-- L ∘ L = L
lemma LL (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  simp only [left_apply]
  have : ∀ a : Fin n1, Pc S i a * (∑ c : Fin n1, Pc S a c * X c j)
      = ∑ c : Fin n1, Pc S i a * Pc S a c * X c j := by
    intro a; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun c _ => by ring)
  rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.sum_mul, Pc_idem]

-- R ∘ R = R
lemma RR (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  simp only [right_apply]
  have : ∀ b : Fin n2, (∑ c : Fin n2, X i c * Pr S c b) * Pr S b j
      = ∑ c : Fin n2, X i c * (Pr S c b * Pr S b j) := by
    intro b; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun c _ => by ring)
  rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [← Finset.mul_sum, Pr_idem]

-- L ∘ R = T
lemma LR (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (rightSingularProjection S X) = twoSidedSingularProjection S X := by
  funext i j
  rw [left_apply, two_apply]
  -- ∑ a, Pc i a * (∑ b, X a b * Pr b j)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [right_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _ => by ring)

-- R ∘ L = T
lemma RL (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (leftSingularProjection S X) = twoSidedSingularProjection S X := by
  funext i j
  rw [right_apply, two_apply]
  -- LHS: ∑ b, (∑ a Pc i a * X a b) * Pr b j
  rw [show (∑ b : Fin n2, leftSingularProjection S X i b * Pr S b j)
        = ∑ b : Fin n2, ∑ a : Fin n1, Pc S i a * X a b * Pr S b j from
      Finset.sum_congr rfl (fun b _ => by rw [left_apply, Finset.sum_mul])]
  rw [Finset.sum_comm]

-- L ∘ T = T
lemma LT (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  funext i j
  simp only [left_apply, two_apply]
  -- Expand LHS to the nested form ∑ a ∑ c ∑ b.
  rw [show (∑ a : Fin n1, Pc S i a *
            ∑ c : Fin n1, ∑ b : Fin n2, Pc S a c * X c b * Pr S b j)
        = ∑ a : Fin n1, ∑ c : Fin n1, ∑ b : Fin n2,
            Pc S i a * Pc S a c * X c b * Pr S b j from
      Finset.sum_congr rfl (fun a _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun c _ => by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)))]
  -- Reorder to ∑ c ∑ b ∑ a and factor.
  rw [Finset.sum_comm]  -- a,c → c,a
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]  -- a,b → b,a (for this c)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [show (∑ a : Fin n1, Pc S i a * Pc S a c * X c b * Pr S b j)
        = (∑ a : Fin n1, Pc S i a * Pc S a c) * X c b * Pr S b j from by
      rw [Finset.sum_mul, Finset.sum_mul], Pc_idem]

-- T ∘ L = T
lemma TL (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (leftSingularProjection S X) = twoSidedSingularProjection S X := by
  funext i j
  simp only [two_apply, left_apply]
  -- Swap a,b on both sides so b is outermost.
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- ∑ a, Pc i a * (∑ c, Pc a c * X c b) * Pr b j = ∑ a, Pc i a * X a b * Pr b j
  rw [show (∑ a : Fin n1, Pc S i a * (∑ c : Fin n1, Pc S a c * X c b) * Pr S b j)
        = ∑ a : Fin n1, ∑ c : Fin n1, (Pc S i a * Pc S a c) * X c b * Pr S b j from
      Finset.sum_congr rfl (fun a _ => by
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun c _ => by ring))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [show (∑ a : Fin n1, Pc S i a * Pc S a c * X c b * Pr S b j)
        = (∑ a : Fin n1, Pc S i a * Pc S a c) * X c b * Pr S b j from by
      rw [Finset.sum_mul, Finset.sum_mul], Pc_idem]

-- R ∘ T = T
lemma RT (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  funext i j
  simp only [right_apply, two_apply]
  -- LHS: ∑ b, (∑ a ∑ c, Pc i a * X a c * Pr c b) * Pr b j
  rw [show (∑ b : Fin n2, (∑ a : Fin n1, ∑ c : Fin n2, Pc S i a * X a c * Pr S c b) * Pr S b j)
        = ∑ a : Fin n1, ∑ c : Fin n2, ∑ b : Fin n2,
            Pc S i a * X a c * (Pr S c b * Pr S b j) from ?_]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [show (∑ b : Fin n2, Pc S i a * X a c * (Pr S c b * Pr S b j))
          = Pc S i a * X a c * (∑ b : Fin n2, Pr S c b * Pr S b j) from by
        rw [Finset.mul_sum], Pr_idem]
  · -- distribute the Pr b j and reorder b,a,c → a,c,b
    rw [show (∑ b : Fin n2, (∑ a : Fin n1, ∑ c : Fin n2, Pc S i a * X a c * Pr S c b) * Pr S b j)
          = ∑ b : Fin n2, ∑ a : Fin n1, ∑ c : Fin n2,
              Pc S i a * X a c * (Pr S c b * Pr S b j) from
        Finset.sum_congr rfl (fun b _ => by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun a _ => by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun c _ => by ring)))]
    -- now ∑ b ∑ a ∑ c → ∑ a ∑ c ∑ b
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]

-- T ∘ R = T
lemma TR (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (rightSingularProjection S X) = twoSidedSingularProjection S X := by
  funext i j
  simp only [two_apply, right_apply]
  -- LHS: ∑ a ∑ b, Pc i a * (∑ c, X a c * Pr c b) * Pr b j ; a is preserved
  refine Finset.sum_congr rfl (fun a _ => ?_)
  -- ∑ b, Pc i a * (∑ c, X a c * Pr c b) * Pr b j = ∑ c, Pc i a * X a c * Pr c j
  rw [show (∑ b : Fin n2, Pc S i a * (∑ c : Fin n2, X a c * Pr S c b) * Pr S b j)
        = ∑ c : Fin n2, ∑ b : Fin n2, Pc S i a * X a c * (Pr S c b * Pr S b j) from ?_]
  · refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [show (∑ b : Fin n2, Pc S i a * X a c * (Pr S c b * Pr S b j))
          = Pc S i a * X a c * (∑ b : Fin n2, Pr S c b * Pr S b j) from by
        rw [Finset.mul_sum], Pr_idem]
  · rw [show (∑ b : Fin n2, Pc S i a * (∑ c : Fin n2, X a c * Pr S c b) * Pr S b j)
          = ∑ b : Fin n2, ∑ c : Fin n2, Pc S i a * X a c * (Pr S c b * Pr S b j) from
        Finset.sum_congr rfl (fun b _ => by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun c _ => by ring))]
    rw [Finset.sum_comm]

-- T ∘ T = T  (via T = R∘L, then L∘T = T and R∘T = T)
lemma TT (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X) = twoSidedSingularProjection S X := by
  rw [← RL S (twoSidedSingularProjection S X), LT, RT]

/-! ### Linearity of the three pieces (additivity / subtractivity). -/

lemma L_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B)
      = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j; simp only [left_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => by ring)

lemma L_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B)
      = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j; simp only [left_apply, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun a _ => by ring)

lemma R_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B)
      = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j; simp only [right_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun b _ => by ring)

lemma R_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B)
      = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j; simp only [right_apply, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun b _ => by ring)

lemma T_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j; simp only [two_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun b _ => by ring)

lemma T_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j; simp only [two_apply, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun b _ => by ring)

/-! ### Idempotence of the tangent projection. -/

lemma tangent_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  -- Unfold the inner tangent projection, distribute each outer piece, collapse.
  conv_lhs => rw [show tangentProjection S X
        = leftSingularProjection S X + rightSingularProjection S X
            - twoSidedSingularProjection S X from rfl]
  rw [tangentProjection, L_sub, L_add, R_sub, R_add, T_sub, T_add,
    LL, LR, LT, RL, RR, RT, TL, TR, TT, tangentProjection]
  abel

/-! ### Self-adjointness of the full tangent projection. -/

lemma tangent_selfadjoint (S : SVD M r) (Y H : RealMatrix n1 n2) :
    matrixInner (tangentProjection S Y) H = matrixInner Y (tangentProjection S H) := by
  unfold tangentProjection
  rw [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    left_selfadjoint, right_selfadjoint, two_selfadjoint]

end TangentAlgebra


