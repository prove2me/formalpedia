-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
-- name    : OAI_Combinatorics_GotsmanLinial_Walsh
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:43:59.465404+00:00
-- url     : https://prove2.me/theorems/743c511c-8995-435c-b73c-1b43aea27f21
-- title:
--   Walsh characters, the Walsh basis, and the Fourier degree filtration of the Boolean cube
-- statement:
--   Let $Q_n=\{-1,1\}^n$ be the Boolean cube, with coordinates $x_i\in\{-1,1\}$ indexed by the coordinate set $[n]$, and let $\mathbb{C}^{Q_n}$ be the $2^n$-dimensional space of complex functions on $Q_n$.
--
--   1. **Walsh characters.** For $S\subseteq[n]$, $\chi_S(x)=\prod_{i\in S}x_i$, regarded as a complex-valued function. Thus $\chi_\emptyset=1$ and $\chi_{\{i\}}(x)=x_i$; each $\chi_S$ is real-valued (equal to its complex conjugate), and $\chi_S\chi_T=\chi_{S\triangle T}$, in particular $\chi_S^2=1$.
--
--   2. **Orthogonality.** $\sum_{x\in Q_n}\chi_S(x)$ equals $2^n$ if $S=\emptyset$ and $0$ otherwise; consequently
--   $$
--   \sum_{x\in Q_n}\overline{\chi_S(x)}\,\chi_T(x)=\begin{cases}2^n, & S=T,\\ 0, & S\neq T.\end{cases}
--   $$
--
--   3. **Unnormalized Fourier coefficient.** For $S\subseteq[n]$, the linear functional $f\mapsto\sum_{x}\overline{\chi_S(x)}\,f(x)$ on $\mathbb{C}^{Q_n}$; it sends $\chi_T$ to $2^n$ if $T=S$ and to $0$ otherwise.
--
--   4. **Walsh basis.** The characters $(\chi_S)_{S\subseteq[n]}$ are linearly independent, and since there are $2^n$ of them they form a basis of $\mathbb{C}^{Q_n}$.
--
--   5. **Fourier degree spaces.** For $k\in\mathbb{N}$, $V_{\le k}=\operatorname{span}_{\mathbb{C}}\{\chi_S : |S|\le k\}$ is the space of functions of Fourier degree at most $k$; it is all of $\mathbb{C}^{Q_n}$ when $k\ge n$. The same subspace is also considered inside the Hilbert space $\ell^2(Q_n)$ with the counting inner product $\langle f,g\rangle=\sum_x\overline{f(x)}g(x)$.
--
--   6. **Shifted degree flag.** $F_0=\{0\}$ and $F_{k+1}=V_{\le k}$ for $k\ge0$, an increasing chain of subspaces of $\ell^2(Q_n)$ with $F_{n+1}=\ell^2(Q_n)$.
--
--   The Walsh characters are the Fourier basis of the cube, and the flag $(F_k)$ is the degree filtration that, after reweighting and orthogonalization, produces the degree grading used in the Gotsman–Linial argument.
--
--   **Formalization Note** The cube is `Cube n`, the Boolean functions on `Fin n`, read as signs via `cubeCoord`. The objects are `walshChar`, `walshCoefficientLinear`, `walshBasis` (built from linear independence and a cardinality count), `fourierSpace` (in the function space), `fourierEuclideanSpace` (its image in `EuclideanSpace`) and `fourierFlag`. A private copy of the core lemma `ite_eq_right` is included for compatibility.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Walsh.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Walsh.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Walsh characters of the Boolean cube

The characters are the real sign monomials, regarded as complex-valued
functions.  Counting orthogonality proves linear independence; the cardinality
comparison then gives a basis.  The degree filtration and its dimensions are
constructed from this concrete basis.
-/

noncomputable section

open scoped BigOperators symmDiff
open Finset Submodule Module

namespace LeanBlast.GotsmanLinial

/-- The complex-valued Walsh character associated to a subset of coordinates. -/
def walshChar {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℂ :=
  ∏ i ∈ S, (cubeCoord x i : ℂ)

@[simp] theorem walshChar_empty {n : ℕ} (x : Cube n) :
    walshChar ∅ x = 1 := by simp [walshChar]

@[simp] theorem walshChar_singleton {n : ℕ} (i : Fin n) (x : Cube n) :
    walshChar {i} x = (cubeCoord x i : ℂ) := by simp [walshChar]

theorem walshChar_eq_prod_univ {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar S x = ∏ i : Fin n, if i ∈ S then (cubeCoord x i : ℂ) else 1 := by
  exact (Fintype.prod_ite_mem S (fun i => (cubeCoord x i : ℂ))).symm

@[simp] theorem star_walshChar {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    star (walshChar S x) = walshChar S x := by
  simp [walshChar]

theorem walshChar_mul {n : ℕ} (S T : Finset (Fin n)) (x : Cube n) :
    walshChar S x * walshChar T x = walshChar (S ∆ T) x := by
  classical
  simp only [walshChar_eq_prod_univ, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    cases hx : x i <;> simp [Finset.mem_symmDiff, hS, hT, cubeCoord, hx]

@[simp] theorem walshChar_mul_self {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walshChar S x * walshChar S x = 1 := by
  simpa using walshChar_mul S S x

theorem sum_walshChar {n : ℕ} (S : Finset (Fin n)) :
    (∑ x : Cube n, walshChar S x) = if S = ∅ then (2 : ℂ) ^ n else 0 := by
  classical
  have hc (b : Bool) : ((if b then (1 : ℝ) else -1 : ℝ) : ℂ) =
      (if b then (1 : ℂ) else -1) := by cases b <;> simp
  simp_rw [walshChar_eq_prod_univ, cubeCoord, hc]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    if i ∈ S then (if b then (1 : ℂ) else -1) else 1)]
  by_cases hS : S = ∅
  · subst S
    simp
  · rw [ite_eq_right hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Orthogonality for the unnormalized counting inner product. -/
theorem walshChar_orthogonality {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Cube n, star (walshChar S x) * walshChar T x) =
      if S = T then (2 : ℂ) ^ n else 0 := by
  simp_rw [star_walshChar, walshChar_mul]
  rw [sum_walshChar]
  simp

/-- Unnormalized Fourier coefficient as a linear functional. -/
def walshCoefficientLinear {n : ℕ} (S : Finset (Fin n)) :
    (Cube n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, star (walshChar S x) * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem walshCoefficientLinear_char {n : ℕ} (S T : Finset (Fin n)) :
    walshCoefficientLinear S (walshChar T) = if S = T then (2 : ℂ) ^ n else 0 :=
  walshChar_orthogonality S T

theorem walshChar_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (walshChar (n := n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc S
  have h := congrArg (walshCoefficientLinear S) hc
  have h' : c S * (2 : ℂ) ^ n = 0 := by
    simpa only [map_sum, map_smul, walshCoefficientLinear_char, map_zero,
      smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h
  exact (mul_eq_zero.mp h').resolve_right (pow_ne_zero _ (by norm_num))

theorem walsh_index_card (n : ℕ) :
    Fintype.card (Finset (Fin n)) = Module.finrank ℂ (Cube n → ℂ) := by
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_finset, Cube]

/-- The concrete Walsh basis, indexed by coordinate subsets. -/
def walshBasis (n : ℕ) : Basis (Finset (Fin n)) ℂ (Cube n → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (walshChar_linearIndependent n) (walsh_index_card n)

@[simp] theorem walshBasis_apply {n : ℕ} (S : Finset (Fin n)) :
    walshBasis n S = walshChar S := by
  simp [walshBasis]

/-- Functions of Fourier degree at most `k`. -/
def fourierSpace (n k : ℕ) : Submodule ℂ (Cube n → ℂ) :=
  Submodule.span ℂ (walshChar '' {S : Finset (Fin n) | S.card ≤ k})

theorem fourierSpace_eq_top {n k : ℕ} (hk : n ≤ k) : fourierSpace n k = ⊤ := by
  apply top_unique
  rw [← (walshChar_linearIndependent n).span_eq_top_of_card_eq_finrank (walsh_index_card n)]
  apply Submodule.span_mono
  rintro f ⟨S, rfl⟩
  have hS : S.card ≤ n := by simpa using S.card_le_univ
  exact ⟨S, hS.trans hk, rfl⟩

/-- Fourier degree filtration in the Hilbert space with counting inner product. -/
def fourierEuclideanSpace (n k : ℕ) : Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  (fourierSpace n k).map
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.toLinearMap

@[simp] theorem mem_fourierEuclideanSpace {n k : ℕ}
    (f : EuclideanSpace ℂ (Cube n)) :
    f ∈ fourierEuclideanSpace n k ↔ (fun x => f x) ∈ fourierSpace n k := by
  change f ∈ (fourierSpace n k).map
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.toLinearMap ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

theorem fourierEuclideanSpace_eq_top {n k : ℕ} (hk : n ≤ k) :
    fourierEuclideanSpace n k = ⊤ := by
  unfold fourierEuclideanSpace
  rw [fourierSpace_eq_top hk, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr
    (WithLp.linearEquiv 2 ℂ (Cube n → ℂ)).symm.surjective

/-- Shift the degree filtration so that its zeroth member is bottom. -/
def fourierFlag (n : ℕ) : ℕ → Submodule ℂ (EuclideanSpace ℂ (Cube n))
  | 0 => ⊥
  | k + 1 => fourierEuclideanSpace n k

@[simp] theorem fourierFlag_zero (n : ℕ) : fourierFlag n 0 = ⊥ := rfl

@[simp] theorem fourierFlag_succ (n k : ℕ) :
    fourierFlag n (k + 1) = fourierEuclideanSpace n k := rfl

@[simp] theorem fourierFlag_top (n : ℕ) : fourierFlag n (n + 1) = ⊤ :=
  fourierEuclideanSpace_eq_top (le_refl n)

end LeanBlast.GotsmanLinial

end

end OAI


