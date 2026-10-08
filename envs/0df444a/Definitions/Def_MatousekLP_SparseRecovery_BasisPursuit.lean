-- Prove2me | Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit
-- name    : MatousekLP_SparseRecovery_BasisPursuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T13:24:45.071989+00:00
-- url     : https://prove2.me/theorems/3aaed8a0-03c1-4d04-b9cd-11f34475cec7
-- title:
--   Sparse solutions, basis pursuit (BP) and (BP′), BP-exactness, and the crosspolytope
-- statement:
--   Let $A$ be a real $m\times n$ matrix and $b\in\mathbb{R}^m$. Section 8.5 of Matoušek & Gärtner studies sparse solutions of the linear system $Ax=b$ and their recovery by linear programming. This module fixes the vocabulary.
--
--   1. The **support** of $x\in\mathbb{R}^n$ is $\operatorname{supp}(x)=\{i : x_i\neq 0\}$. For an integer $r\ge 0$, a **sparse solution** of $Ax=b$ is an $x$ with $Ax=b$ and $|\operatorname{supp}(x)|\le r$ (the book's (8.10)).
--   2. The **$\ell_1$-norm** is $\|x\|_1=|x_1|+|x_2|+\dots+|x_n|$.
--   3. **Basis pursuit** is the problem
--   $$\text{(BP)}\qquad \text{minimize } \|x\|_1 \ \text{ subject to } x\in\mathbb{R}^n,\ Ax=b .$$
--   An **optimal solution** of (BP) is an $x$ with $Ax=b$ and $\|x\|_1\le\|x'\|_1$ for every $x'$ with $Ax'=b$; it is the **unique optimal solution** if moreover every optimal solution equals it.
--   4. The linear program
--   $$\text{(BP}'\text{)}\qquad \text{minimize } u_1+\dots+u_n \ \text{ subject to } Ax=b,\ -u\le x\le u,\ x,u\in\mathbb{R}^n,\ u\ge 0,$$
--   with feasible and optimal solutions $(x,u)$ in the usual sense (optimal: feasible, with objective at most that of every feasible pair).
--   5. $A$ is **BP-exact for $r$** if for every $b\in\mathbb{R}^m$: whenever $Ax=b$ has a solution $\tilde x$ with at most $r$ nonzero components, $\tilde x$ is the unique optimal solution of (BP).
--   6. The **crosspolytope** is the unit ball of the $\ell_1$-norm, $B^n_1=\{x\in\mathbb{R}^n:\|x\|_1\le 1\}$.
--   7. The **kernel** of $A$ is $L=\{x\in\mathbb{R}^n: Ax=0\}$, and for $z\in\mathbb{R}^n$ its **translate** is $L+z=\{\ell+z:\ell\in L\}$.
--   8. For $z\in\mathbb{R}^n$, the **cone at $z$** is $C_z=\{t(x-z): t\ge 0,\ x\in B^n_1\}$, and a set $L$ is **good for $z$** if $(L+z)\cap B^n_1=\{z\}$.
--
--   These notions are the language of Observation 8.5.1, Theorem 8.5.2 and Lemma 8.5.4.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so the book's indices $1,\dots,n$ are $0,\dots,n-1$. The $\ell_1$-norm is written out as a sum of absolute values (Mathlib's norm on `Fin n → ℝ` is the sup norm). The support is a `Finset` of indices; optimality is stated against every feasible point, with no infimum taken. The translate and the cone are defined for an arbitrary set $L$; the theorems use $L$ = the kernel of $A$.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, §8.5: p. 168 (supp, (8.10) sparse solution), p. 169 ((BP), ℓ1-norm), p. 170 ((BP′), BP-exact), p. 172 (crosspolytope B^n_1, kernel L, L + z), p. 174 (cone C_z, L good for z)

import Mathlib

namespace MatousekLP.SparseRecovery

/-!
# Sparse solutions, basis pursuit and BP-exactness (§8.5)

Matoušek & Gärtner, *Understanding and Using Linear Programming*, Springer 2007, §8.5,
pp. 167–174.  For a real `m × n` matrix `A` and `b ∈ ℝ^m`:

* `supp(x) = {i : xᵢ ≠ 0}` (p. 168), and a *sparse solution* of `Ax = b` is an `x` with
  `Ax = b` and `|supp(x)| ≤ r`, (8.10) (p. 168);
* `‖x‖₁ = |x₁| + ⋯ + |xₙ|` (p. 169);
* (BP) minimize `‖x‖₁` subject to `x ∈ ℝⁿ` and `Ax = b` (p. 169);
* (BP′) minimize `u₁ + ⋯ + uₙ` subject to `Ax = b`, `−u ≤ x ≤ u`, `x, u ∈ ℝⁿ`, `u ≥ 0` (p. 170);
* `A` is *BP-exact for `r`* if whenever `Ax = b` has a solution `x̃` with at most `r` nonzero
  components, `x̃` is the unique optimal solution of (BP) (p. 170);
* the crosspolytope `B₁ⁿ = {x : ‖x‖₁ ≤ 1}` (p. 172);
* the kernel `L = {x : Ax = 0}` and its translates `L + z` (p. 172);
* the cone `C_z = {t(x − z) : t ≥ 0, x ∈ B₁ⁿ}` and "`L` is good for `z`", i.e.
  `(L + z) ∩ B₁ⁿ = {z}` (p. 174).

The book's indices `1, …, n` are `0, …, n-1` here.  `‖·‖₁` is written out as a sum of absolute
values (Mathlib's norm on `Fin n → ℝ` is the sup norm).
-/

open Matrix

variable {m n : ℕ}

/-- The ℓ₁-norm `‖x‖₁ = ∑ᵢ |xᵢ|`. -/
def l1Norm (x : Fin n → ℝ) : ℝ := ∑ i, |x i|

/-- The support `supp(x) = {i : xᵢ ≠ 0}`, as a finset of indices. -/
noncomputable def supp (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

/-- `x` is a sparse solution of `Ax = b` (for the sparsity bound `r`): `Ax = b` and
`|supp(x)| ≤ r`, the book's (8.10). -/
def IsSparseSolution (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (r : ℕ)
    (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ (supp x).card ≤ r

/-- `x` is an optimal solution of (BP): `Ax = b`, and `‖x‖₁ ≤ ‖x'‖₁` for every `x'` with
`Ax' = b`. -/
def IsBPOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ ∀ x' : Fin n → ℝ, A *ᵥ x' = b → l1Norm x ≤ l1Norm x'

/-- `x` is the unique optimal solution of (BP): it is optimal, and every optimal solution
equals `x`. -/
def IsUniqueBPOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  IsBPOptimal A b x ∧ ∀ x' : Fin n → ℝ, IsBPOptimal A b x' → x' = x

/-- `(x, u)` is a feasible solution of (BP′): `Ax = b`, `−u ≤ x ≤ u` and `u ≥ 0`
(componentwise). -/
def IsBPPrimeFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x u : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧ -u ≤ x ∧ x ≤ u ∧ 0 ≤ u

/-- `(x, u)` is an optimal solution of (BP′): it is feasible and
`u₁ + ⋯ + uₙ ≤ u'₁ + ⋯ + u'ₙ` for every feasible `(x', u')`. -/
def IsBPPrimeOptimal (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x u : Fin n → ℝ) : Prop :=
  IsBPPrimeFeasible A b x u ∧
    ∀ x' u' : Fin n → ℝ, IsBPPrimeFeasible A b x' u' → ∑ i, u i ≤ ∑ i, u' i

/-- `A` is BP-exact for `r` (p. 170): for every `b ∈ ℝ^m`, if `Ax = b` has a solution `x̃`
with at most `r` nonzero components, then `x̃` is the unique optimal solution of (BP). -/
def IsBPExact (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ) : Prop :=
  ∀ (b : Fin m → ℝ) (xt : Fin n → ℝ), A *ᵥ xt = b → (supp xt).card ≤ r →
    IsUniqueBPOptimal A b xt

/-- The `n`-dimensional crosspolytope `B₁ⁿ = {x ∈ ℝⁿ : ‖x‖₁ ≤ 1}`. -/
def crosspolytope (n : ℕ) : Set (Fin n → ℝ) := {x | l1Norm x ≤ 1}

/-- The kernel (null space) `L = {x ∈ ℝⁿ : Ax = 0}` of `A`. -/
def kernel (A : Matrix (Fin m) (Fin n) ℝ) : Set (Fin n → ℝ) := {x | A *ᵥ x = 0}

/-- The translate `L + z = {l + z : l ∈ L}` of a set `L ⊆ ℝⁿ` by `z`. -/
def translate (L : Set (Fin n → ℝ)) (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ l ∈ L, x = l + z}

/-- The cone `C_z = {t(x − z) : t ≥ 0, x ∈ B₁ⁿ}` at `z` (p. 174). -/
def coneAt (z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ crosspolytope n, v = t • (x - z)}

/-- `L` is good for `z` (p. 174): `(L + z) ∩ B₁ⁿ = {z}`. -/
def IsGoodFor (L : Set (Fin n → ℝ)) (z : Fin n → ℝ) : Prop :=
  translate L z ∩ crosspolytope n = {z}

end MatousekLP.SparseRecovery


