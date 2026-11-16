-- Prove2me | Definitions.Def_BinarySketchTruncation_Opposite_Supplement_UnateEvaluation
-- name    : BinarySketchTruncation_Opposite_Supplement_UnateEvaluation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:05:09.792832+00:00
-- url     : https://prove2.me/theorems/88712110-70a3-45a5-82b1-3ae1198d20ff
-- title:
--   Unate Boolean functions, joint-mass simulation and minimum evaluation errors
-- statement:
--   Let Z be uniform on 𝔽₂ⁿ and let f : 𝔽₂ⁿ → {0,1}. The function f is unate when there is one fixed d ∈ 𝔽₂ⁿ such that z ↦ f(z ⊕ d) is non-decreasing in every coordinate. Constant functions are included. For a statistic s with finite alphabet T, define its joint masses and minimum evaluation error by
--
--   $$
--   J_s(h,t)=\Pr\{f(Z)=h,\ s(Z)=t\},\qquad
--   e_f(s)=\min_{g:T\to\{0,1\}}\Pr\{g(s(Z))\ne f(Z)\}.
--   $$
--
--   An observation s dominates an observation t for the function value when one row-stochastic kernel K, normalized even on unobserved inputs, satisfies
--
--   $$
--   J_t(h,y)=\sum_x J_s(h,x)K(x,y)\qquad(h=0,1).
--   $$
--
--   For nonconstant f, division by the positive mass of each function value gives exactly the published conditional Blackwell comparison. Joint masses also cover constant f. The decoder minimum is a literal minimum of a nonempty finite set. The optimal linear and projection errors are the infima of e_f over full-row-rank k-by-n matrices and over embeddings of k coordinates into n coordinates, respectively. For k ≤ n these are nonempty finite optimizations; Theorem 2 additionally asserts their attainment. If k > n both feasible types are empty and Lean's real infimum returns zero; no assertion in Theorem 2 uses that case.
--
--   These definitions preserve the source's experiment comparison as well as its optimal-error consequence. Bit, vectors, row rank, information sets and stochastic kernels are the published base definitions; this file does not redefine them.
-- source:
--   Robinson D.H. Cung, Adway Girish, Emre Telatar, STOC 2027 submission #341 (October 2026), pp. 8–10 (PDF pp. 9–11), §4, Definition 5, Eq. (3), Theorem 2; p. 5 (PDF p. 6), Eq. (1)

import Mathlib
import Definitions.Def_BinarySketchTruncation_Opposite_Supplement_UniformFinite

namespace BinarySketchTruncation.Opposite.Supplement

/-- Definition 5: a single fixed translation makes the function increasing
in every coordinate; false ≤ true is the usual order on Bool. -/
def IsUnate {n : ℕ} (f : Vec n → Bool) : Prop :=
  ∃ d : Vec n, ∀ (z : Vec n) (i : Fin n),
    f (Function.update z i 0 + d) ≤ f (Function.update z i 1 + d)

/-- Joint mass of the function value and the observation, under uniform Z. -/
noncomputable def functionJointMass {n : ℕ} {T : Type}
    (f : Vec n → Bool) (s : Vec n → T) (h : Bool) (t : T) : ℝ :=
  uniformProbability (fun z => f z = h ∧ s z = t)

/-- Exact simulation of the joint masses by one kernel serving both function
values. Unlike conditional PMFs this also applies to constant functions. -/
def FunctionDominates {n : ℕ} {S T : Type} [Fintype S] [Fintype T]
    (f : Vec n → Bool) (s : Vec n → S) (t : Vec n → T) : Prop :=
  ∃ K : S → T → ℝ, RowStochastic K ∧ ∀ h y,
    functionJointMass f t h y = ∑ x, functionJointMass f s h x * K x y

/-- Equation (3): the attained minimum over every deterministic Boolean decoder. -/
noncomputable def minimumError {n : ℕ} {T : Type} [Fintype T]
    (f : Vec n → Bool) (s : Vec n → T) : ℝ := by
  classical
  exact (Finset.univ.image (fun g : T → Bool =>
    uniformProbability (fun z => g (s z) ≠ f z))).min'
      (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- The finite rank-k optimization. For k ≤ n the feasible set is nonempty.
Theorem 2 explicitly asserts attainment, in addition to equality of the values. -/
noncomputable def optimalLinearError {n : ℕ} (f : Vec n → Bool) (k : ℕ) : ℝ :=
  ⨅ A : {A : Matrix (Fin k) (Fin n) Bit // FullRowRank A},
    minimumError f (fun z => A.val.mulVec z)

/-- Ordered k-element coordinate sets. Reordering the observed coordinates
just reindexes decoders, so this has the same minimum as unordered subsets. -/
noncomputable def optimalProjectionError {n : ℕ} (f : Vec n → Bool) (k : ℕ) : ℝ :=
  ⨅ e : Fin k ↪ Fin n, minimumError f (fun z => z ∘ e)

end BinarySketchTruncation.Opposite.Supplement


