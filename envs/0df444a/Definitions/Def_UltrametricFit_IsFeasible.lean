-- Prove2me | Definitions.Def_UltrametricFit_IsFeasible
-- name    : UltrametricFit_IsFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:32.898438+00:00
-- url     : https://prove2.me/theorems/e684fb2a-f34c-4bf5-9e64-c696a3ba4ba2
-- title:
--   The standard layered LP (ℓp-ultrametric-LP): cost, feasibility, optimality, integer points
-- statement:
--   The relaxation has a variable $x_\ell(i,j)$ for each layer $\ell\in[L]$ and each pair, with the convention $x_0(i,j)=1$ on pairs and $x_\ell(i,i)=0$. A point is **feasible** when
--
--   1. $x_\ell(i,j)\le x_\ell(i,k)+x_\ell(k,j)$ for all $\ell\in[L]$ and $i,j,k\in[n]$ (2);
--   2. $x_L(i,j)=0$ for all $i,j\in[n]$ (3);
--   3. $x_\ell(i,j)\ge x_{\ell+1}(i,j)$ for all $\ell\in[L-1]$ and $i,j\in[n]$ (4);
--   4. $x_\ell(i,j)\in[0,1]$ for all $\ell\in[L]$ and $i,j\in[n]$ (5).
--
--   The **LP cost** of a pair and of a solution are
--   $$\mathrm{lp\text{-}cost}_p(x,i,j)=\sum_{\ell=1}^{L}|D_\ell-X(i,j)|^p\,\bigl(x_{\ell-1}(i,j)-x_\ell(i,j)\bigr),\qquad \mathrm{lp\text{-}cost}_p(x)=\sum_{i<j}\mathrm{lp\text{-}cost}_p(x,i,j),$$
--   and an **optimal** solution is a feasible point of least cost.
--
--   The **integer point** of an ultrametric $U$ has $x_\ell(i,j)=1$ exactly when $U(i,j)>D_\ell$. It is what makes the program a relaxation of the fitting problem.
--
--   **Formalization Note** Variables are `x : ℕ → Fin n → Fin n → ℝ`, with `x ℓ` the paper's $x_\ell$; layers beyond $L$ are not constrained or read. Symmetry of each layer is a constraint, because the paper's variables live on unordered pairs. Optimality is stated without a real infimum.
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §2, pp.6–7, constraints (2)–(5), and footnote 4, p.8

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_layerValue

namespace UltrametricFit

/-- **LP cost of a pair**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), §2,
p.7: `lp-cost_p(x, i, j) = Σ_{ℓ=1}^{L} |D_ℓ − X(i, j)|^p · (x_{ℓ−1}(i, j) − x_ℓ(i, j))`.

**Formalization Note.** The variables are `x : ℕ → Fin n → Fin n → ℝ`, with `x ℓ` the paper's
`x_ℓ`; only layers `0, …, L` are ever read. `ℓ - 1` is natural-number subtraction at `ℓ ≥ 1`. -/
noncomputable def lpCostPair {n : ℕ} (X : Fin n → Fin n → ℝ) (p : ℝ)
    (x : ℕ → Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 (numLayers X),
    |layerValue X ℓ - X i j| ^ p * (x (ℓ - 1) i j - x ℓ i j)

/-- **LP objective** `lp-cost_p(x) := Σ_{i,j ∈ ([n] choose 2)} lp-cost_p(x, i, j)`, Charikar, Gao,
STOC 2027 submission (manuscript sha256 87af12a2…), §2, p.7. It is the `p`-th power of the
`ℓ_p`-distance, not its root. -/
noncomputable def lpCost {n : ℕ} (X : Fin n → Fin n → ℝ) (p : ℝ)
    (x : ℕ → Fin n → Fin n → ℝ) : ℝ :=
  ∑ q ∈ pairs n, lpCostPair X p x q.1 q.2

/-- **Feasible points of (ℓp-ultrametric-LP)**, Charikar, Gao, STOC 2027 submission (manuscript
sha256 87af12a2…), §2, pp.6–7 and footnote 4, p.8: constraints (2)–(5), `x_0(i, j) = 1` on pairs,
and `x_ℓ(i, i) = 0`.

**Formalization Note.** The paper's variables live on unordered pairs, so symmetry of each layer
is a constraint here. Layers `ℓ > L` are not constrained and not read. At `L = 0` (that is,
`n ≤ 1`) there is no pair, and the clauses reduce to `x 0 i i = 0`, which is harmless because
nothing reads it. -/
structure IsFeasible {n : ℕ} (X : Fin n → Fin n → ℝ) (x : ℕ → Fin n → Fin n → ℝ) : Prop where
  /-- `x` lives on unordered pairs -/
  symm : ∀ ℓ, ℓ ≤ numLayers X → ∀ i j, x ℓ i j = x ℓ j i
  /-- footnote 4, p.8 -/
  diag : ∀ ℓ ∈ Finset.Icc 1 (numLayers X), ∀ i, x ℓ i i = 0
  /-- `x_0(i, j) = 1` for all pairs, p.6 -/
  layer_zero : ∀ i j, i ≠ j → x 0 i j = 1
  /-- constraint (2) -/
  triangle : ∀ ℓ ∈ Finset.Icc 1 (numLayers X), ∀ i j k, x ℓ i j ≤ x ℓ i k + x ℓ k j
  /-- constraint (3) -/
  last_layer : ∀ i j, x (numLayers X) i j = 0
  /-- constraint (4) -/
  antitone : ∀ ℓ ∈ Finset.Icc 1 (numLayers X - 1), ∀ i j, x (ℓ + 1) i j ≤ x ℓ i j
  /-- constraint (5) -/
  mem_unit : ∀ ℓ ∈ Finset.Icc 1 (numLayers X), ∀ i j, x ℓ i j ∈ Set.Icc (0 : ℝ) 1

/-- **Optimal solution of (ℓp-ultrametric-LP)**, Charikar, Gao, STOC 2027 submission (manuscript
sha256 87af12a2…), §2, p.7 and §3, p.8: a feasible point whose LP objective is at most that of every
feasible point. No real infimum is used. -/
def IsOptimal {n : ℕ} (X : Fin n → Fin n → ℝ) (p : ℝ) (x : ℕ → Fin n → Fin n → ℝ) : Prop :=
  IsFeasible X x ∧ ∀ x', IsFeasible X x' → lpCost X p x ≤ lpCost X p x'

/-- **The integer point of an ultrametric**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), §2, p.6: `x_ℓ(i, j)` "indicates whether the distance between species i and j is strictly
greater than D_ℓ". With `x_0 = 1` on pairs, and `0` on the diagonal. -/
noncomputable def integerPoint {n : ℕ} (X U : Fin n → Fin n → ℝ) :
    ℕ → Fin n → Fin n → ℝ :=
  fun ℓ i j => if i ≠ j ∧ (ℓ = 0 ∨ layerValue X ℓ < U i j) then 1 else 0

end UltrametricFit


