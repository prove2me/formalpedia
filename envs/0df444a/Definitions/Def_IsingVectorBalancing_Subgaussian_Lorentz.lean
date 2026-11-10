-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz
-- name    : IsingVectorBalancing_Subgaussian_Lorentz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:33:19.394196+00:00
-- url     : https://prove2.me/theorems/df8e9a11-d852-420a-9d8b-c3db4da7d85c
-- title:
--   Spectral Lorentzian matrices and the selection polynomial
-- statement:
--   For a finite coordinate set $C$, a real matrix $A\in\mathbb R^{C\times C}$ is Lorentzian when it is symmetric, entrywise nonnegative, and has at most one strictly positive eigenvalue counted with multiplicity. The zero matrix and singular matrices are allowed. The Lorentz matrix of a family $u_c\in\mathbb R^d$ is $A(c,c')=1-\langle u_c,u_{c'}\rangle$, including diagonal entries.
--
--   For selections $x_1,\ldots,x_k\in\mathbb R^C$, define
--   $$V_A(x_1,\ldots,x_k)=\sum_{c:[k]\to C}\left(\prod_i x_i(c(i))\right)\left(\prod_{i<j}A(c(i),c(j))\right).$$
--   The sum ranges over all assignments, with repetitions allowed, and has no factorial normalization. A constructor places two selections before an arbitrary remaining list. These are the spectral and polynomial objects of the discrete Alexandrov–Fenchel statement.
--
--   **Formalization Note** Symmetry is real Hermitian symmetry; Mathlib's full eigenvalue list counts multiplicity. The polynomial is defined for every finite arity, including empty products, and its theorem uses $k=m+2$ for arbitrary $m\ge0$.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, p. 5 (PDF 6), §5, Eq. (3), definitions before Theorem 5 and Lemma 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Geometry

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

/-- Section 5 spectral definition. The eigenvalue index counts multiplicity. -/
noncomputable def IsLorentzian {C : Type*} [Fintype C] [DecidableEq C]
    (A : Matrix C C ℝ) : Prop :=
  (∀ c c', 0 ≤ A c c') ∧
    ∃ hA : A.IsHermitian, (Finset.univ.filter (fun c => 0 < hA.eigenvalues c)).card ≤ 1

noncomputable def lorentzMatrix {C : Type*} {d : ℕ} (u : C → Vec d) : Matrix C C ℝ :=
  fun c c' => 1 - inner ℝ (u c) (u c')

/-- Equation (3): all assignments, including repeated coordinates; no normalization. -/
noncomputable def selectionPolynomial {C : Type*} [Fintype C] {k : ℕ}
    (A : Matrix C C ℝ) (x : Fin k → C → ℝ) : ℝ :=
  ∑ c : Fin k → C, (∏ i, x i (c i)) *
    (∏ i : Fin k, ∏ j ∈ Finset.univ.filter (fun j : Fin k => i < j), A (c i) (c j))

/-- The first two selections followed by an arbitrary remaining list. -/
def selections {C : Type*} {m : ℕ} (x₁ x₂ : C → ℝ) (tail : Fin m → C → ℝ) :
    Fin (m + 2) → C → ℝ :=
  Fin.cons x₁ (Fin.cons x₂ tail)

end IsingVectorBalancing.Subgaussian


