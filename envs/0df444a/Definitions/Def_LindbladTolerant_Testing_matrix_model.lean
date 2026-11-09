-- Prove2me | Definitions.Def_LindbladTolerant_Testing_matrix_model
-- name    : LindbladTolerant_Testing_matrix_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:48:15.414436+00:00
-- url     : https://prove2.me/theorems/3ee82d7c-2be2-44d3-9ac0-d6f38248afa1
-- title:
--   Finite quantum matrices, normalized Choi operators, and norms
-- statement:
--   Let $I$ be a finite computational-basis index set of size $d$. Operators are complex square matrices, and linear maps on operators are represented by their coefficients in the matrix-unit basis. The system factor comes first. Ordinary trace and matrix Schatten norms are unnormalized; the trace norm is the published definition imported here.
--
--   For a matrix $X$ and a linear map $g$, the normalized vectorization, normalized Choi operator, superoperator Frobenius norm, and diamond norm are
--   $$
--   |X\rangle\!\rangle_{ij}=X_{ij}/\sqrt d,\qquad J(g)_{(i,r),(j,s)}=g_{(i,j),(r,s)}/d,
--   $$
--   $$
--   \|g\|_F^2=d^{-2}\sum_{i,j,r,s}|g_{(i,j),(r,s)}|^2,\qquad
--   \|g\|_\diamond=\sup_{X\ne0}\frac{\|(g\otimes\mathrm{Id})(X)\|_1}{\|X\|_1}.
--   $$
--   The stabilized diamond norm uses an isomorphic reference. The supremum is nonempty and bounded in each positive finite dimension. Evolution is the actual matrix exponential of the matrix representing $tg$. Partial traces sum over the stated factor, and complete positivity means positivity on every finite ancillary extension.
--
--   This layer fixes the normalizations needed by all subsequent statements. The Choi–Frobenius identity is a mathematical consequence of these definitions, rather than an axiom or an alternative definition of the Frobenius norm.
-- source:
--   Jinge Bao, Yiyi Cai, Zhong-Xia Shang, Optimal Tolerant Testing of Lindbladian Dissipation, STOC 2027 submission #238 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/238.pdf, §§2.1–2.2, pp.9–11, PDF pp.9–11, Eqs.(7)–(17)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
open scoped BigOperators ComplexConjugate Matrix

namespace LindbladTolerant.Testing

/-- Finite matrices, with ordinary (unnormalized) trace. -/
abbrev Op (I : Type*) := Matrix I I ℂ
/-- Matrix of a complex-linear superoperator in matrix units; output pair first. -/
abbrev Super (I J : Type*) := Matrix (J × J) (I × I) ℂ

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

def applySuper (g : Super I J) (x : Op I) : Op J :=
  fun i j => ∑ r, ∑ s, g (i,j) (r,s) * x r s

def conjugation (l : Matrix J I ℂ) : Super I J :=
  fun ij rs => l ij.1 rs.1 * star (l ij.2 rs.2)

def leftRight (a b : Op I) : Super I I :=
  fun ij rs => a ij.1 rs.1 * b rs.2 ij.2

/-- The system is the first factor, and every off-diagonal memory block is retained. -/
def tensorId (g : Super I J) (x : Op (I × K)) : Op (J × K) :=
  fun i j => ∑ r, ∑ s, g (i.1,j.1) (r,s) * x (r,i.2) (s,j.2)

/-- Normalized Choi matrix, with system/output first. -/
def choi (g : Super I J) : Op (J × I) :=
  fun i j => g (i.1,j.1) (i.2,j.2) / (Fintype.card I : ℂ)

def inverseChoi (c : Op (J × I)) : Super I J :=
  fun ij rs => (Fintype.card I : ℂ) * c (ij.1,rs.1) (ij.2,rs.2)

def outer (v w : I → ℂ) : Op I := fun i j => v i * star (w j)

def ket (x : Op I) : (I × I) → ℂ :=
  fun i => x i.1 i.2 / (Real.sqrt (Fintype.card I : ℝ) : ℂ)

def phi : (I × I) → ℂ := ket (1 : Op I)
def phiProjector : Op (I × I) := outer phi phi
def orthogonalProjector : Op (I × I) := 1 - phiProjector

def traceSystem (x : Op (I × J)) : Op J := fun i j => ∑ a, x (a,i) (a,j)
def traceReference (x : Op (I × J)) : Op I := fun i j => ∑ a, x (i,a) (j,a)

def hsNorm (x : Op I) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j))
def frobenius (g : Super I I) : ℝ :=
  Real.sqrt ((∑ ij, ∑ rs, Complex.normSq (g ij rs)) / (Fintype.card I : ℝ)^2)
def frobeniusInner (g h : Super I I) : ℂ :=
  (∑ ij, ∑ rs, star (g ij rs) * h ij rs) / (Fintype.card I : ℂ)^2

/-- Eq.(17). Finite-dimensional linearity bounds this set; a nonzero matrix exists
on every nonempty index type. This is not a supremum of unrestricted response laws. -/
def diamond (g : Super I I) : ℝ :=
  sSup {r : ℝ | ∃ x : Op (I × I), x ≠ 0 ∧
    r = QAlgorithms.traceNorm (tensorId g x) / QAlgorithms.traceNorm x}

def IsDensity (x : Op I) : Prop := x.PosSemidef ∧ x.trace = 1

def evolution (g : Super I I) (t : ℝ) : Super I I :=
  NormedSpace.exp ((t : ℂ) • g)

/-- Complete positivity on every finite ancillary extension. -/
def IsCP (g : Super I J) : Prop :=
  ∀ (r : ℕ) (x : Op (I × Fin r)), x.PosSemidef → (tensorId g x).PosSemidef

end LindbladTolerant.Testing


