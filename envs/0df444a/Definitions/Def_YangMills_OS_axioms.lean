-- Prove2me | Definitions.Def_YangMills_OS_axioms
-- name    : YangMills_OS_axioms
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T12:32:42.190426+00:00
-- url     : https://prove2.me/theorems/e0d29370-1097-4387-8dd9-984a0260428f
-- title:
--   Osterwalder–Schrader axioms and the mass gap on $\mathbb{R}^4$
-- statement:
--   This file fixes the continuum side of the Yang–Mills problem: what a Euclidean quantum field
--   theory on $\mathbb R^4$ is, and what it means for one to have a mass gap.
--
--   Space-time is $\mathbb R^4$, realised as the space of functions $\mathrm{Fin}\,4\to\mathbb R$,
--   with the coordinate $x^0$ playing the role of Euclidean time. Test functions are real-valued
--   Schwartz functions $f\in\mathcal S(\mathbb R^4;\mathbb R)$. Two elementary maps are fixed: the
--   time reflection $\theta(x^0,\vec x)=(-x^0,\vec x)$, and a Euclidean motion, given by an
--   orthogonal matrix $A$ (i.e. $A^{\mathsf T}A=I$) together with a translation vector $b$, acting by
--   $x\mapsto Ax+b$.
--
--   A **Euclidean (Osterwalder–Schrader) theory** is a family of Schwinger functions
--   $S_n\colon \mathcal S(\mathbb R^4;\mathbb R)^n\to\mathbb C$, $n\ge0$, subject to:
--
--   1. **Normalisation.** $S_0=1$.
--   2. **Temperedness (OS0).** Each $S_n$ is additive and real-homogeneous in every argument, and
--      continuous in every argument separately; that is, each $S_n$ is a separately continuous
--      multilinear form on test functions.
--   3. **Euclidean invariance (OS1).** If $f'_i=f_i\circ g$ for a Euclidean motion $g$, then
--      $S_n(f')=S_n(f)$.
--   4. **Permutation symmetry (OS3).** $S_n(f_{\sigma(0)},\dots,f_{\sigma(n-1)})=S_n(f_0,\dots,f_{n-1})$.
--   5. **Reflection positivity (OS2).** For finitely many finite families $F_j$ of test functions
--      supported in the open half-space $\{x^0>0\}$, their reflections $F_j\circ\theta$, and complex
--      coefficients $c_j$, the quadratic form
--      $$\sum_{j,l}\overline{c_j}\,c_l\,S_{k_j+k_l}\bigl(F_j\circ\theta,\;F_l\bigr)$$
--      is a non-negative real number, where $(F_j\circ\theta, F_l)$ denotes the concatenated family.
--
--   The **truncated two-point function** is $S^{\mathrm T}_2(f,g)=S_2(f,g)-S_1(f)S_1(g)$. The theory
--   is **non-trivial** when $S^{\mathrm T}_2(f,g)\neq0$ for at least one pair of test functions, and
--   it **has a mass gap of size at least $\Delta>0$** when for every pair $f,g$ there is a constant
--   $C\ge0$ with
--   $$\bigl|S^{\mathrm T}_2(f,g_t)\bigr|\le C e^{-\Delta t}\quad\text{for all }t\ge0,$$
--   where $g_t(x)=g(x-t e_0)$ is the translate of $g$ by $t$ units of Euclidean time.
--
--   This exponential-clustering formulation is the Euclidean counterpart of the statement that the
--   Hamiltonian obtained by Osterwalder–Schrader reconstruction has spectrum in
--   $\{0\}\cup[\Delta,\infty)$; it is the form in which the mass gap is stated in the Clay problem
--   description.
--
--   **Formalization Note.** The growth/analyticity refinements of OS0 and the ergodicity axiom OS4
--   are not imposed; clustering enters only through the mass-gap predicate. Reflection positivity is
--   stated for arbitrary finite collections of multi-point families, not only for the two-point
--   function.
-- source:
--   A. Jaffe and E. Witten, Quantum Yang-Mills Theory, Clay Mathematics Institute Millennium Prize Problem description (2000), pp. 1-6, https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf ; axioms OS0-OS3 as in K. Osterwalder and R. Schrader, Axioms for Euclidean Green's functions, Comm. Math. Phys. 31 (1973) 83-112, Section 2, and II, Comm. Math. Phys. 42 (1975) 281-305.

import Mathlib

/-!
# Euclidean (Osterwalder–Schrader) quantum field theories on `ℝ⁴` and the mass gap

This file sets up the continuum side of the Yang–Mills existence and mass gap problem:
Schwinger (Euclidean correlation) functions, the Osterwalder–Schrader axioms, non-triviality,
and the mass gap expressed as exponential clustering of the truncated two-point function.
-/

namespace YangMills

open MeasureTheory Filter Topology Finset

/-- Euclidean space-time `ℝ⁴`, realised as `Fin 4 → ℝ`; the coordinate `x 0` is Euclidean time. -/
abbrev Spacetime : Type := Fin 4 → ℝ

/-- Real-valued Schwartz test functions on `ℝ⁴`. -/
abbrev TestFn : Type := SchwartzMap Spacetime ℝ

/-- The unit vector in the Euclidean time direction. -/
noncomputable def timeDir : Spacetime := Pi.single 0 1

/-- Euclidean time reflection `θ (x⁰, x⃗) = (-x⁰, x⃗)`. -/
def timeReflect (x : Spacetime) : Spacetime := Function.update x 0 (-x 0)

/-- A Euclidean motion of `ℝ⁴`: an orthogonal matrix together with a translation vector. -/
structure EuclideanMotion where
  /-- The linear part, an orthogonal `4 × 4` matrix. -/
  matrix : Matrix (Fin 4) (Fin 4) ℝ
  /-- The translation part. -/
  vector : Spacetime
  /-- Orthogonality of the linear part. -/
  orthogonal : matrix.transpose * matrix = 1

/-- The action of a Euclidean motion on a point: `x ↦ A x + b`. -/
def EuclideanMotion.apply (g : EuclideanMotion) (x : Spacetime) : Spacetime :=
  g.matrix.mulVec x + g.vector

/-- A test function is *supported at positive time* if it vanishes off `{x : 0 < x⁰}`. -/
def PosTime (f : TestFn) : Prop := ∀ x : Spacetime, f x ≠ 0 → 0 < x 0

/-- A family of Schwinger functions on `ℝ⁴` satisfying the Osterwalder–Schrader axioms.

`S n (f₀, …, f_{n-1})` is the `n`-point Euclidean correlation function smeared against the test
functions `f i`. The fields record, in order: normalisation of the `0`-point function, additivity,
homogeneity and separate continuity in each slot (a separately-continuous multilinear, i.e.
tempered-distribution, form of OS0), Euclidean invariance (OS1), reflection positivity (OS2) and
permutation symmetry (OS3). -/
structure OSTheory where
  /-- The Schwinger functions. -/
  S : (n : ℕ) → (Fin n → TestFn) → ℂ
  /-- Normalisation: the `0`-point function is `1`. -/
  norm_one : ∀ f : Fin 0 → TestFn, S 0 f = 1
  /-- Additivity in each slot. -/
  add_slot : ∀ (n : ℕ) (f : Fin n → TestFn) (i : Fin n) (g h : TestFn),
    S n (Function.update f i (g + h))
      = S n (Function.update f i g) + S n (Function.update f i h)
  /-- Homogeneity in each slot. -/
  smul_slot : ∀ (n : ℕ) (f : Fin n → TestFn) (i : Fin n) (c : ℝ) (g : TestFn),
    S n (Function.update f i (c • g)) = (c : ℂ) * S n (Function.update f i g)
  /-- Separate continuity in each slot (temperedness). -/
  cont_slot : ∀ (n : ℕ) (f : Fin n → TestFn) (i : Fin n),
    Continuous fun g : TestFn => S n (Function.update f i g)
  /-- OS1, Euclidean invariance: precomposing every test function with a Euclidean motion
  leaves the Schwinger functions unchanged. -/
  euclid_inv : ∀ (n : ℕ) (g : EuclideanMotion) (f f' : Fin n → TestFn),
    (∀ (i : Fin n) (x : Spacetime), f' i x = f i (g.apply x)) → S n f' = S n f
  /-- OS3, permutation symmetry. -/
  perm_symm : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f : Fin n → TestFn), S n (f ∘ σ) = S n f
  /-- OS2, reflection positivity: for finitely many families `F j` of test functions supported at
  positive time, with time-reflected copies `Fθ j`, and complex coefficients `c j`, the quadratic
  form `∑_{j,l} conj (c j) * c l * S (Fθ j, F l)` is a non-negative real number. -/
  refl_pos : ∀ (m : ℕ) (k : Fin m → ℕ) (F Fθ : (j : Fin m) → Fin (k j) → TestFn)
      (c : Fin m → ℂ),
    (∀ (j : Fin m) (i : Fin (k j)), PosTime (F j i)) →
    (∀ (j : Fin m) (i : Fin (k j)) (x : Spacetime), Fθ j i x = F j i (timeReflect x)) →
    ∃ r : ℝ, 0 ≤ r ∧
      ∑ j : Fin m, ∑ l : Fin m,
        (starRingEnd ℂ) (c j) * c l * S (k j + k l) (Fin.append (Fθ j) (F l)) = (r : ℂ)

/-- The truncated (connected) two-point function of a Euclidean theory. -/
noncomputable def OSTheory.truncTwoPoint (Q : OSTheory) (f g : TestFn) : ℂ :=
  Q.S 2 ![f, g] - Q.S 1 ![f] * Q.S 1 ![g]

/-- A Euclidean theory is *non-trivial* if some truncated two-point function is non-zero, i.e.
the fields are genuinely correlated. -/
def OSTheory.IsNonTrivial (Q : OSTheory) : Prop :=
  ∃ f g : TestFn, Q.truncTwoPoint f g ≠ 0

/-- `Q` *has a mass gap of size at least* `Δ`: `Δ > 0` and, for all test functions `f` and `g`,
the truncated two-point function of `f` against the time translate of `g` by `t ≥ 0` decays
at least like `C e^{-Δ t}`.

This is the Euclidean (exponential clustering) formulation of the statement that the spectrum of
the Hamiltonian obtained by Osterwalder–Schrader reconstruction is contained in `{0} ∪ [Δ, ∞)`. -/
def OSTheory.HasMassGap (Q : OSTheory) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ f g : TestFn, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : ℝ) (gt : TestFn), 0 ≤ t → (∀ x : Spacetime, gt x = g (x - t • timeDir)) →
      ‖Q.truncTwoPoint f gt‖ ≤ C * Real.exp (-Δ * t)

end YangMills


