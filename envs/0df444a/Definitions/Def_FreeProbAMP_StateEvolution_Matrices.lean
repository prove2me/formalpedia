-- Prove2me | Definitions.Def_FreeProbAMP_StateEvolution_Matrices
-- name    : FreeProbAMP_StateEvolution_Matrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:24:09.258901+00:00
-- url     : https://prove2.me/theorems/3047f633-8e99-4c76-af8c-cd87a3527b3c
-- title:
--   Normalized GOE operators and Euclidean matrix norms
-- statement:
--   Let $A_1,\ldots,A_n$ be independent samples from the referenced normalized GOE law on real symmetric $d\times d$ matrices. Its off-diagonal and diagonal variances are $1/d$ and $2/d$. For $d,n>0$ define
--
--   $$\tau_d(M)=\frac{\operatorname{Tr}M}{d},\quad\langle M,N\rangle_d=\tau_d(MN),\quad
--   \langle x,y\rangle_n=\frac1n\sum_i x_i y_i,$$
--   $$A(x)=\frac1{\sqrt n}\sum_i x_iA_i,\qquad (A^*M)_i=\sqrt n\,\tau_d(A_iM),\qquad\alpha_d=\frac{2n}{d^2}.$$
--
--   The vector and matrix quadratic norms are the square roots of their self-inner-products. The operator norm is the Euclidean induced matrix norm, defined as the supremum over vectors of Euclidean norm at most one. Every such finite-matrix supremum is over a bounded nonempty set. Complexification permits arbitrary complex polynomial coefficients and preserves the spectral norm of every real matrix.
--
--   Finite column maps, their adjoints and Gram matrices are defined from the indicated inner product. Projection onto a column span is its unique orthogonal projection when that inner product is positive definite on the span; in particular this covers the real vector and symmetric-matrix spaces used here, including rank-deficient spans. These are the shared matrix and finite-history interfaces, with no boundedness or invertibility hypotheses imposed on the AMP input.
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 2, (1.1)–(1.3); pp. 22–23, (4.1)–(4.5)

import Mathlib
import Definitions.Def_RandMatDisc_goe
import Definitions.Def_FreeProbAMP_StateEvolution_Empirical

open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

abbrev RMat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev CMat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

instance (d : ℕ) : MeasurableSpace (RMat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))

instance (d : ℕ) : MeasurableSpace (CMat d) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℂ))

def traceN {d : ℕ} (M : RMat d) : ℝ := M.trace / d

def matInner {d : ℕ} (M N : RMat d) : ℝ := traceN (M*N)
def vecInner {n : ℕ} (x y : Fin n → ℝ) : ℝ := avg n (fun i => x i*y i)
def vecNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (vecInner x x)
def matNorm2 {d : ℕ} (M : RMat d) : ℝ := Real.sqrt (matInner M M)

def complexify {d : ℕ} (M : RMat d) : CMat d := fun i j => (M i j : ℂ)

def ctraceN {d : ℕ} (M : CMat d) : ℂ := M.trace / d

/-- The Euclidean operator norm. The defining set is nonempty and bounded for every finite matrix. -/
def copNorm {d : ℕ} (M : CMat d) : ℝ :=
  sSup {r : ℝ | ∃ x : Fin d → ℂ, (∑ j, ‖x j‖ ^ 2) ≤ 1 ∧
    r = Real.sqrt (∑ i, ‖∑ j, M i j * x j‖ ^ 2)}

def opNorm {d : ℕ} (M : RMat d) : ℝ := copNorm (complexify M)

def aspect (n d : ℕ) : ℝ := 2 * n / (d : ℝ)^2

def applyA {n d : ℕ} (A : Fin n → RMat d) (x : Fin n → ℝ) : RMat d :=
  (Real.sqrt n)⁻¹ • ∑ i, x i • A i

def applyAdj {n d : ℕ} (A : Fin n → RMat d) (M : RMat d) : Fin n → ℝ :=
  fun i => Real.sqrt n * traceN (A i * M)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The general GOE object is the published law, with joint independence of matrix samples. -/
def GOEArray {n d : ℕ} (μ : Measure Ω) (A : Ω → Fin n → RMat d) : Prop :=
  Measurable A ∧ iIndepFun (fun i ω => A ω i) μ ∧
    ∀ i, μ.map (fun ω => A ω i) = RandMatDisc.goe d

/-- A column map, written as a finite sum. -/
def columns {p : ℕ} {B : Type*} [AddCommMonoid B] [Module ℝ B]
    (Q : Fin p → B) (c : Fin p → ℝ) : B := ∑ j, c j • Q j

def gram {p : ℕ} {B : Type*} (ip : B → B → ℝ) (Q : Fin p → B) : RMat p :=
  fun i j => ip (Q i) (Q j)

def adjColumns {p : ℕ} {B : Type*} (ip : B → B → ℝ) (Q : Fin p → B) (x : B) : Fin p → ℝ :=
  fun i => ip (Q i) x

/-- Orthogonal projection through the finite-dimensional span; works also at rank deficiency.
The minimizer is unique, so this definition makes no arbitrary basis convention. -/
def spanProjection {p : ℕ} {B : Type*} [AddCommGroup B] [Module ℝ B]
    (ip : B → B → ℝ) (Q : Fin p → B) (x : B) : B := by
  classical
  exact if h : ∃ y : B, (∃ c, y = columns Q c) ∧ ∀ i, ip (Q i) (x-y) = 0
  then h.choose else 0

end FreeProbAMP.StateEvolution


