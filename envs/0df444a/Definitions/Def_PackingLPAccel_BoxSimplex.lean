-- Prove2me | Definitions.Def_PackingLPAccel_BoxSimplex
-- name    : PackingLPAccel_BoxSimplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:30.179954+00:00
-- url     : https://prove2.me/theorems/ecb1990d-4d99-4209-8fbb-df2423414b95
-- title:
--   The doubly entropic regularizer and the approximate composite best response oracle
-- statement:
--   For $A\in\mathbb R^{m\times n}$, $\alpha\ge0$ and $\xi>0$, the doubly entropic regularizer is
--
--   $$r_{\alpha,\xi}(u,v)=\sum_{i,j}(v_i+\xi)|A_{ij}|(u_j+\xi)\log(u_j+\xi)+\alpha\sum_iv_i\log v_i.$$
--
--   A $\delta$-approximate composite best response oracle with respect to $(U,\psi,r)$ takes $v\in\Delta^m$ and $h_U\in\mathbb R^n$, and returns $\hat u\in U$ with
--
--   1. $\langle h_U+\nabla_Ur(\hat u,v),\hat u-u\rangle\le\psi(u)-\psi(\hat u)+\delta$ for all $u\in U$, and
--   2. $\|\nabla_Vr(u^\star,v)-\nabla_Vr(\hat u,v)\|_\infty\le\delta/2$, where $u^\star$ minimizes $\langle h_U,u\rangle+r(u,v)+\psi(u)$ over $U$.
--
--   The module fixes the parameters of Theorem 5.5, $\xi=\min(1/m,\rho/(mn\|A\|_\infty))$, $\alpha=16\rho B$ and $B=1+\log\max(1/\xi,R_U+\xi)$, and defines the oracle's query class and the program's input layout.
--
--   **Formalization Note** The gradients are written out. The constant $c$ of Definition 5.3 is $1$, the paper's convention. The minimizer $u^\star$ ranges over all minimizers, which agree on $\nabla_Vr$. $\|A\|_\infty$ is the largest absolute entry, and the diameter is Euclidean.
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), display (10), p.19 (pdf 20); Definitions 5.3, 5.4 and Theorem 5.5, p.20 (pdf 21); notation, p.7 (pdf 8)

import Mathlib
import Definitions.Def_PackingLPAccel_Layout

namespace PackingLPAccel

/-!
# Box-simplex games, the doubly entropic regularizer and the best response oracle

Chen, Chen, Graur, Sidford, *Accelerated Parallel Algorithms for Packing Linear Programming*,
STOC 2027 submission (manuscript sha256 1dac7711…), display (10), Definitions 5.3, 5.4, and Theorem 5.5
(pp.19–20).

**Formalization Note.**
* The gradients of `r_{α,ξ}` are written out, not left to `fderiv`.
* The constant `c` of Definition 5.3 is `1`, the paper's convention (p.20).
* The `u⋆` of Definition 5.3.2 ranges over all minimizers. They all give the same `∇_V r`, since `r`
  is strictly convex in the coordinates with nonzero columns.
* `∥A∥_∞` is the largest absolute entry (p.7), and `Diam` the Euclidean diameter (p.7).
* Theorem 5.5's input layout: `I 0 = m`, `I 1 = n`, `I 2 = N`, then positions; `M 0 = ε`, `M 1 = ρ`,
  `M 2 = R_U`, then values; output `û` from `M (3 + N)` and `v̂` from `M (3 + N + n)`. Oracle block:
  `v` from cell `0`, `h_U` from cell `m`, the answer from cell `m + n`.
-/

variable {m n : ℕ}

/-- `∥A∥_∞`, the largest absolute entry. -/
noncomputable def entryNorm (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ⨆ ij : Fin m × Fin n, |A ij.1 ij.2|

/-- The Euclidean diameter `Diam(S) = max_{a,b ∈ S} ∥a - b∥₂`. -/
noncomputable def euclDiam (S : Set (Fin n → ℝ)) : ℝ :=
  sSup {d | ∃ a ∈ S, ∃ b ∈ S, d = Real.sqrt (∑ j, (a j - b j) ^ 2)}

/-- The doubly entropic regularizer `r_{α,ξ}(u, v)` of Definition 5.4. -/
noncomputable def doublyEntropic (A : Matrix (Fin m) (Fin n) ℝ) (α ξ : ℝ) (u : Fin n → ℝ)
    (v : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, (v i + ξ) * |A i j| * ((u j + ξ) * Real.log (u j + ξ)) + α * ∑ i, v i * Real.log (v i)

/-- `∇_U r_{α,ξ}(u, v)`. -/
noncomputable def gradUEntropic (A : Matrix (Fin m) (Fin n) ℝ) (ξ : ℝ) (u : Fin n → ℝ)
    (v : Fin m → ℝ) (j : Fin n) : ℝ :=
  ∑ i, (v i + ξ) * |A i j| * (Real.log (u j + ξ) + 1)

/-- `∇_V r_{α,ξ}(u, v)`. -/
noncomputable def gradVEntropic (A : Matrix (Fin m) (Fin n) ℝ) (α ξ : ℝ) (u : Fin n → ℝ)
    (v : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j, |A i j| * ((u j + ξ) * Real.log (u j + ξ)) + α * (Real.log (v i) + 1)

/-- `ξ = min(1/m, ρ/(mn∥A∥_∞))` of Theorem 5.5. -/
noncomputable def bsXi (A : Matrix (Fin m) (Fin n) ℝ) (ρ : ℝ) : ℝ :=
  min (1 / (m : ℝ)) (ρ / (m * n * entryNorm A))

/-- `B = 1 + log(max(1/ξ, R_U + ξ))` of Theorem 5.5. -/
noncomputable def bsB (A : Matrix (Fin m) (Fin n) ℝ) (ρ RU : ℝ) : ℝ :=
  1 + Real.log (max (1 / bsXi A ρ) (RU + bsXi A ρ))

/-- `û` answers the query `(v, h)` of a `δ`-ABRO with respect to `(U, ψ, r_{α,ξ})`, with `c = 1`
(Definition 5.3). -/
def IsABROAnswer (A : Matrix (Fin m) (Fin n) ℝ) (U : Set (Fin n → ℝ)) (ψ : (Fin n → ℝ) → ℝ)
    (α ξ δ : ℝ) (v : Fin m → ℝ) (h uhat : Fin n → ℝ) : Prop :=
  uhat ∈ U ∧
  (∀ u ∈ U, ∑ j, (h j + gradUEntropic A ξ uhat v j) * (uhat j - u j) ≤ ψ u - ψ uhat + δ) ∧
  ∀ ustar ∈ U,
    (∀ u ∈ U, ∑ j, h j * ustar j + doublyEntropic A α ξ ustar v + ψ ustar ≤
      ∑ j, h j * u j + doublyEntropic A α ξ u v + ψ u) →
    ‖fun i => gradVEntropic A α ξ ustar v i - gradVEntropic A α ξ uhat v i‖ ≤ δ / 2

/-- The oracle of Theorem 5.5: on queries with `v ∈ ∆^m` and `∥h_U∥_∞ ≤ 3nB∥A∥_∞` it writes an ABRO
answer; every other query has no answer. -/
def IsABROOracle (A : Matrix (Fin m) (Fin n) ℝ) (U : Set (Fin n → ℝ)) (ψ : (Fin n → ℝ) → ℝ)
    (ρ RU δBR : ℝ) (O : OracleModel) : Prop :=
  ∀ st : State,
    let v : Fin m → ℝ := readBlock st.M 0
    let h : Fin n → ℝ := readBlock st.M m
    (v ∈ stdSimplex ℝ (Fin m) ∧ ‖h‖ ≤ 3 * n * bsB A ρ RU * entryNorm A →
      ∃ uhat, IsABROAnswer A U ψ (16 * ρ * bsB A ρ RU) (bsXi A ρ) δBR v h uhat ∧
        O.answer st =
          some (writeBlock st.M (m + n) n (fun k => if hk : k < n then uhat ⟨k, hk⟩ else 0), st.I)) ∧
    (¬ (v ∈ stdSimplex ℝ (Fin m) ∧ ‖h‖ ≤ 3 * n * bsB A ρ RU * entryNorm A) → O.answer st = none)

/-- The initial state of Theorem 5.5. -/
noncomputable def boxSimplexInit {N : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ε ρ RU : ℝ)
    (e : Fin N → Fin m × Fin n) : State :=
  initState ([ε, ρ, RU] ++ sparseVals A e) ([(m : ℤ), (n : ℤ), (N : ℤ)] ++ sparseIdx e)

end PackingLPAccel


