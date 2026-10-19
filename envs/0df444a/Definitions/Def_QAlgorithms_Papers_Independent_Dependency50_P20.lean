-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20
-- name    : QAlgorithms_Papers_Independent_Dependency50_P20
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:12:51.161748+00:00
-- url     : https://prove2.me/theorems/f0d03fba-6da4-40da-8cf5-f6bb9d802533
-- title:
--   Definitions for The Zero Set of a Real Analytic Function
-- statement:
--   The objects the formalized statements of *The Zero Set of a Real Analytic Function* (arXiv:1512.07276) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ambient`: The real Euclidean space used in Proposition 0, PDF p. 1.
--   - `zeroSet`: The zero set inside the specified domain, equation (1), PDF p. 1.
--   - `regularZeroSet`: The regular zero set from equation (2), PDF p. 1. The gradient uses the Euclidean inner product; its norm is required to be nonzero.
--   - `coordinatePartial`: One coordinate partial derivative in the standard Euclidean basis, as used in equations (6)–(7), PDF p. 2.
--   - `multiIndexOrder`: Total order of a multi-index, PDF p. 2.
--   - `mixedPartial`: The unnormalized mixed coordinate derivative D^t from PDF p. 2. Coordinates are listed in increasing order, with coordinate j repeated t j times. Right folding gives D_0^(t_0) ... D_(d-1)^(t_(d-1)); for smooth functions on an open domain this is independent of the chosen ordering. Order zero is f itself. No factorial or Taylor coefficient normalization is used.
--   - `isQuasianalyticClass`: Germ-level meaning of a real quasianalytic class in Remark (iii), PDF p. 3. Members are smooth on U, the zero function belongs to the class, and equality of all coordinate derivatives at a point implies equality on a neighborhood of that point contained in U. Global identity and zero-set nullity are not assumed.
--   - `denjoyCarlemanWeight`: Weight assumptions in the explicit example in Remark (iii), PDF p. 3. Positive weights are normalized at zero, nondecreasing, unbounded in the stated limit sense, and log-convex. For positive weights the displayed multiplicative inequality is exactly discrete convexity of log M. The last condition is the printed series starting at n = 1, expressed by its first N partial sums tending to positive infinity, rather than a real-valued tsum.
--   - `inDenjoyCarlemanClass`: Membership in C_M(U), Remark (iii), PDF p. 3. For every compact subset K of U, the positive constants are chosen before both the multi-index and the point. The bound is C_K R_K^|t| M(|t|), with no factorial.
-- source:
--   The Zero Set of a Real Analytic Function, arXiv:1512.07276v1, https://arxiv.org/abs/1512.07276v1

import Mathlib

/-!
Statements from Boris S. Mityagin, *The Zero Set of a Real Analytic Function*,
arXiv:1512.07276v1, PDF pp. 1–3. All new definitions are local to this paper.
The positive-dimensional convention is explicit in every source theorem.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace QAlgorithms.Papers.Independent.Dependency50.P20

/-- The real Euclidean space used in Proposition 0, PDF p. 1. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The zero set inside the specified domain, equation (1), PDF p. 1. -/
def zeroSet {d : ℕ} (U : Set (Ambient d)) (f : Ambient d → ℝ) : Set (Ambient d) :=
  {x | x ∈ U ∧ f x = 0}

example {d : ℕ} (U : Set (Ambient d)) :
    zeroSet U (fun _ => (1 : ℝ)) = ∅ := by
  simp [zeroSet]

/-- The regular zero set from equation (2), PDF p. 1. The gradient uses the
Euclidean inner product; its norm is required to be nonzero. -/
noncomputable def regularZeroSet {d : ℕ} (U : Set (Ambient d))
    (f : Ambient d → ℝ) : Set (Ambient d) :=
  {x | x ∈ U ∧ f x = 0 ∧ ‖gradient f x‖ ≠ 0}

example {d : ℕ} (U : Set (Ambient d)) :
    regularZeroSet U (fun _ => (0 : ℝ)) = ∅ := by
  simp [regularZeroSet, gradient_fun_const]

/-- One coordinate partial derivative in the standard Euclidean basis,
as used in equations (6)–(7), PDF p. 2. -/
noncomputable def coordinatePartial {d : ℕ} (j : Fin d)
    (f : Ambient d → ℝ) : Ambient d → ℝ :=
  fun x => fderiv ℝ f x (EuclideanSpace.single j 1)

example {d : ℕ} (j : Fin d) (c : ℝ) :
    coordinatePartial j (fun _ => c) = fun _ => 0 := by
  funext x
  simp [coordinatePartial]

/-- Total order of a multi-index, PDF p. 2. -/
def multiIndexOrder {d : ℕ} (t : Fin d → ℕ) : ℕ :=
  ∑ j, t j

example : multiIndexOrder (fun _ : Fin 1 => 2) = 2 := by
  simp [multiIndexOrder]

/-- The unnormalized mixed coordinate derivative D^t from PDF p. 2.
Coordinates are listed in increasing order, with coordinate j repeated t j times.
Right folding gives D_0^(t_0) ... D_(d-1)^(t_(d-1)); for smooth functions on an
open domain this is independent of the chosen ordering. Order zero is f itself.
No factorial or Taylor coefficient normalization is used. -/
noncomputable def mixedPartial {d : ℕ} (t : Fin d → ℕ)
    (f : Ambient d → ℝ) : Ambient d → ℝ :=
  ((List.finRange d).flatMap (fun j => List.replicate (t j) j)).foldr
    (fun j g => coordinatePartial j g) f

example (f : Ambient 1 → ℝ) : mixedPartial (fun _ => 0) f = f := by
  rfl

example (f : Ambient 1 → ℝ) :
    mixedPartial (fun _ => 2) f = coordinatePartial 0 (coordinatePartial 0 f) := by
  rfl

/-- Germ-level meaning of a real quasianalytic class in Remark (iii), PDF p. 3.
Members are smooth on U, the zero function belongs to the class, and equality
of all coordinate derivatives at a point implies equality on a neighborhood of
that point contained in U. Global identity and zero-set nullity are not assumed. -/
def isQuasianalyticClass {d : ℕ} (U : Set (Ambient d))
    (C : Set (Ambient d → ℝ)) : Prop :=
  (fun _ => (0 : ℝ)) ∈ C ∧
  (∀ f ∈ C, ContDiffOn ℝ ∞ f U) ∧
  ∀ f ∈ C, ∀ g ∈ C, ∀ x ∈ U,
    (∀ t : Fin d → ℕ, mixedPartial t f x = mixedPartial t g x) →
    ∃ V : Set (Ambient d), IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ EqOn f g V

example {d : ℕ} (U : Set (Ambient d)) (hU : IsOpen U) :
    isQuasianalyticClass U ({fun _ : Ambient d => (0 : ℝ)} : Set (Ambient d → ℝ)) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro f hf
    have hf0 : f = fun _ => (0 : ℝ) := Set.mem_singleton_iff.mp hf
    subst f
    exact contDiffOn_const
  · intro f hf g hg x hx hjet
    have hf0 : f = fun _ => (0 : ℝ) := Set.mem_singleton_iff.mp hf
    have hg0 : g = fun _ => (0 : ℝ) := Set.mem_singleton_iff.mp hg
    refine ⟨U, hU, hx, Subset.rfl, ?_⟩
    intro y hy
    rw [hf0, hg0]

/-- Weight assumptions in the explicit example in Remark (iii), PDF p. 3.
Positive weights are normalized at zero, nondecreasing, unbounded in the stated
limit sense, and log-convex. For positive weights the displayed multiplicative
inequality is exactly discrete convexity of log M. The last condition is the
printed series starting at n = 1, expressed by its first N partial sums tending
to positive infinity, rather than a real-valued tsum. -/
def denjoyCarlemanWeight (M : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 < M n) ∧
  M 0 = 1 ∧
  Monotone M ∧
  Tendsto M atTop atTop ∧
  (∀ n : ℕ, (M (n + 1)) ^ 2 ≤ M n * M (n + 2)) ∧
  Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, M (n + 1) / M (n + 2))
    atTop atTop

example : ¬ denjoyCarlemanWeight (fun _ => 0) := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h.1 0)

/-- Membership in C_M(U), Remark (iii), PDF p. 3. For every compact subset K
of U, the positive constants are chosen before both the multi-index and the
point. The bound is C_K R_K^|t| M(|t|), with no factorial. -/
def inDenjoyCarlemanClass {d : ℕ} (M : ℕ → ℝ) (U : Set (Ambient d))
    (f : Ambient d → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f U ∧
  ∀ K : Set (Ambient d), IsCompact K → K ⊆ U →
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
      ∀ (t : Fin d → ℕ) (x : Ambient d), x ∈ K →
        |mixedPartial t f x| ≤ C * R ^ (multiIndexOrder t) * M (multiIndexOrder t)

example {d : ℕ} (M : ℕ → ℝ) (f : Ambient d → ℝ) :
    inDenjoyCarlemanClass M (∅ : Set (Ambient d)) f := by
  refine ⟨contDiffOn_empty, ?_⟩
  intro K hK hKU
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro t x hx
  exact (hKU hx).elim

end QAlgorithms.Papers.Independent.Dependency50.P20


