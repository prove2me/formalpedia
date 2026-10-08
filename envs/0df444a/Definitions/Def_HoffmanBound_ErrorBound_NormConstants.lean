-- Prove2me | Definitions.Def_HoffmanBound_ErrorBound_NormConstants
-- name    : HoffmanBound_ErrorBound_NormConstants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:21:00.616567+00:00
-- url     : https://prove2.me/theorems/863b80cc-dd80-4b31-99b6-4643f0d96ba4
-- title:
--   Max and sum norms of §3, Gram matrix g_ij = A_i·A_j, a_S (6), game value v_S (7), and the constants of (8)–(10)
-- statement:
--   These are the explicit quantities of Sections 3–5 of Hoffman's paper. Let $A=(a_{ij})$ be a real $m\times n$ matrix with rows $A_1,\dots,A_m$.
--
--   1. **Norms (§3).** $|x|$ is the maximum of the absolute values of the coordinates of $x$, and $\|x\|$ is the sum of the absolute values of the coordinates of $x$.
--   2. **Gram matrix.** $g_{ij}=A_i\cdot A_j$.
--   3. **(6).** For a set $S$ of rows, $a_S$ is the largest absolute value of the coordinates of the rows $A_i$, $i\in S$.
--   4. **(7).** For a nonempty set $S$ of rows,
--   $$
--   v_S=\min_{\lambda}\max_{i\in S}\sum_{j\in S}g_{ij}\lambda_j,
--   $$
--   the minimum over $\lambda_j\ge 0$ ($j\in S$) with $\sum_{j\in S}\lambda_j=1$; it is the value of the zero-sum two-person game with matrix $(g_{ij})_{i,j\in S}$.
--   5. **(8).** $c=\max_{v_S>0}a_S/v_S$, over the nonempty sets $S$ of rows with $v_S>0$.
--   6. **(9).** $v=\min_{i,j}A_i\cdot A_j$ and $a=\max_{i,j}|a_{ij}|$.
--   7. **(10).** $w=\min_i\bigl(g_{ii}+\sum_{j:\,g_{ij}<0}g_{ij}\bigr)$, with $g$ the Gram matrix of all the rows of $A$.
--
--   These constants make the error bound of the main theorem explicit for the max norm (Case II) and for the max norm against the sum norm (Case III).
--
--   **Formalization Note** Minima and maxima are `⨅`/`⨆` in `ℝ` over finite index types (or, for $v_S$, over the simplex, which is nonempty and compact when $S\neq\emptyset$), so they are the attained min/max whenever the index set is nonempty; on an empty index set they take the value $0$ ($|x|=0$ for $n=0$; $v=a=w=0$ for $m=0$; $c=0$ when no $S$ has $v_S>0$, which happens only if every row is $0$). In $w$ the page prints the summation range "$j=1,\dots,n$"; since $g$ is indexed by rows, $j$ is read as ranging over the $m$ rows.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), pp. 264–265 (PDF pp. 2–3): §3 norms, (6), (7), (8), (9), (10)

import Mathlib

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 264, §3: `|x|`, the maximum of the absolute values of the coordinates of
`x` (the value is `0` on the zero-dimensional space). -/
noncomputable def maxNorm {k : ℕ} (x : Fin k → ℝ) : ℝ := ⨆ i, |x i|

/-- Hoffman 1952, p. 264, §3: `‖x‖`, the sum of the absolute values of the coordinates of `x`. -/
def sumNorm {k : ℕ} (x : Fin k → ℝ) : ℝ := ∑ i, |x i|

/-- The Gram matrix `g_ij = A_i · A_j` of the rows of `A` (pp. 265). -/
def gram {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => A i ⬝ᵥ A j

/-- (6), p. 264: `a_S`, the largest absolute value of the coordinates of the rows `A_i`,
`i ∈ S`. -/
noncomputable def aS {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) : ℝ :=
  ⨆ i : S, ⨆ j, |A i j|

/-- The probability simplex on the index set `S`: weights `λ_j ≥ 0`, zero off `S`, with
`∑_{j ∈ S} λ_j = 1`. -/
def simplexOn {m : ℕ} (S : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {l | (∀ j, 0 ≤ l j) ∧ (∀ j, j ∉ S → l j = 0) ∧ ∑ j ∈ S, l j = 1}

/-- (7), p. 265: `v_S = min_λ max_{i ∈ S} ∑_{j ∈ S} g_ij λ_j`, the minimum over the simplex on
`S` (the value of the zero-sum game with matrix `g_ij`, `i, j ∈ S`). Used for nonempty `S`. -/
noncomputable def vS {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m)) : ℝ :=
  ⨅ l : simplexOn S, ⨆ i : S, ∑ j ∈ S, gram A i j * (l : Fin m → ℝ) j

/-- (8), p. 265: `c = max_{v_S > 0} a_S / v_S`, the maximum over the nonempty subsets `S` of the
rows with `v_S > 0` (`0` if there is none, which happens only when every row is `0`). -/
noncomputable def constC8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨆ S : {S : Finset (Fin m) // S.Nonempty ∧ 0 < vS A S}, aS A S.1 / vS A S.1

/-- (9), p. 265: `v = min_{i,j} A_i · A_j`. -/
noncomputable def vMin {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ⨅ i, ⨅ j, gram A i j

/-- (9), p. 265: `a = max_{i,j} |a_ij|`. -/
noncomputable def aMax {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ⨆ i, ⨆ j, |A i j|

/-- (10), p. 265: `w = min_i (g_ii + ∑_{j, g_ij < 0} g_ij)`, with `g` the Gram matrix of all the
rows of `A` and `j` ranging over the rows. -/
noncomputable def wConst {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ⨅ i, (gram A i i + ∑ j ∈ Finset.univ.filter (fun j => gram A i j < 0), gram A i j)

end HoffmanBound.ErrorBound


