-- Prove2me | Definitions.Def_WalledBrauer_Center_Setting
-- name    : WalledBrauer_Center_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:17.411713+00:00
-- url     : https://prove2.me/theorems/d5773bd6-188a-4d4c-88ad-b08774397f8d
-- title:
--   Definitions 2.1, 2.8, p. 12, (3.1) — Jucys–Murphy elements $L_k$, supersymmetric polynomials, evaluation at the $L_k$, content vectors $c(\lambda,i)$, $\tau_t$
-- statement:
--   Let $r,s\ge 0$ be integers, $\delta\in\mathbb C$, and let $B_{r,s}(\delta)$ be the walled Brauer algebra over $\mathbb C$ with basis the $(r,s)$-walled Brauer diagrams on the vertices $1,\dots,r+s$ (wall between $r$ and $r+1$). This file introduces the objects of Jung–Kim's description of the center of $B_{r,s}(\delta)$.
--
--   1. **Transpositions and arcs** (p. 5). For $a\ne b$ on the same side of the wall, $(a,b)$ is the permutation diagram of the transposition of $a$ and $b$. For $1\le j\le r<k\le r+s$, $e_{j,k}$ is the diagram with a top arc and a bottom arc joining $j$ and $k$, all other vertices joined straight down.
--   2. **Jucys–Murphy elements** (Definition 2.1, p. 7). For $1\le k\le r+s$,
--   $$
--   L_k=\begin{cases}\displaystyle\sum_{j=1}^{k-1}(j,k) & 1\le k\le r,\\[2mm] \displaystyle -\sum_{j=1}^{r}e_{j,k}+\sum_{j=r+1}^{k-1}(j,k)+\delta & r+1\le k\le r+s.\end{cases}
--   $$
--   In particular $L_1=0$. The element $L_1^k+\dots+L_r^k+(-1)^{k+1}(L_{r+1}^k+\dots+L_{r+s}^k)$ of Proposition 2.7 is also defined here.
--   3. **Supersymmetric polynomials** (Definition 2.8, p. 11). A polynomial $p\in\mathbb C[x_1,\dots,x_r,y_1,\dots,y_s]$ is supersymmetric if it is symmetric in $x_1,\dots,x_r$ and in $y_1,\dots,y_s$ separately, and the substitution $x_r=-y_1=t$ yields a polynomial in the remaining variables that does not depend on $t$. The power sums are $p_k=x_1^k+\dots+x_r^k+(-1)^{k+1}(y_1^k+\dots+y_s^k)$ (p. 11).
--   4. **Evaluation** $p\mapsto p(L_1,\dots,L_{r+s})$, sending $x_i\mapsto L_i$ and $y_j\mapsto L_{r+j}$.
--   5. **Contents** (p. 12). $\operatorname{cont}(\mu,i)$ is the content $b-a$ of the box at position $(a,b)$ carrying entry $i$ in the tableau $\mathfrak t^\mu$ that numbers the boxes $1,\dots,|\mu|$ along successive rows. For $\lambda=(\lambda^L,\lambda^R)\in\Lambda^t_{r,s}$,
--   $$
--   c(\lambda,i)=\begin{cases}\operatorname{cont}(\lambda^L,i) & 1\le i\le r-t,\\ 0 & r-t+1\le i\le r+t,\\ \operatorname{cont}(\lambda^R,i-r-t)+\delta & r+t+1\le i\le r+s.\end{cases}
--   $$
--   6. **The element** $\tau_t=e_{r,r+1}e_{r-1,r+2}\cdots e_{r-t+1,r+t}$ of (3.1), p. 14, for $t\le\min(r,s)$.
--
--   These are the objects in which Jung and Kim state that, when $B_{r,s}(\delta)$ is semisimple, the supersymmetric polynomials in $L_1,\dots,L_{r+s}$ generate its center.
--
--   **Formalization Note** The algebra, its diagrams, the cell-module index set $\Lambda_{r,s}$ (`CellIndex`) and contents are the published `WalledBrauer.Blocks` definitions. Vertices are 0-based: the paper's vertex $k$ is `Fin (r + s)` value $k-1$, so `jm δ k` is $L_{k+1}$, and `tr`, `eArc` take 0-based vertices. Polynomials live in `MvPolynomial (Fin r ⊕ Fin s) ℂ` with $x_i$ = `X (Sum.inl (i-1))` and $y_j$ = `X (Sum.inr (j-1))`. The cancellation property substitutes `X none` for $t$ in a polynomial ring over `Option (Fin r ⊕ Fin s)` and asks that `none` not occur among the variables; it is vacuous when $r=0$ or $s=0$, where the substitution cannot be made. Since $B_{r,s}(\delta)$ is not commutative, `evalJM` evaluates monomial by monomial with factors in increasing vertex order; this is the paper's $p(L_1,\dots,L_{r+s})$ because the $L_k$ commute (Proposition 2.6), which the definition does not assume. `cVec δ λ` is the point $(c(\lambda,1),\dots,c(\lambda,r+s))$, indexed like the variables. The platform's product puts the left factor on top, the opposite of the paper's (p. 4); the elements defined here are fixed by the up–down flip, so they are the same elements in either convention. `tau` is $1$ outside $t\le\min(r,s)$, a case never used.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, pp. 4–7, 11–12, 14, Definition 2.1, Definition 2.8, (3.1)

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Algebra
import Definitions.Def_WalledBrauer_Blocks_Partitions
import Definitions.Def_WalledBrauer_Blocks_CellModules

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

/-- The walled Brauer algebra `B_{r,s}(δ)` over `ℂ` (Jung–Kim p. 4), the published algebra on the
walled diagram basis. Its product stacks the left factor on top, so it is Jung–Kim's algebra with
the opposite multiplication on the same basis. -/
abbrev B (r s : ℕ) (δ : ℂ) := WalledBrauerAlgebra ℂ r s δ

variable {r s : ℕ}

/-- The transposition `(a, b)` of `B_{r,s}(δ)` (p. 5), with 0-based vertices `a, b : Fin (r + s)`
on the same side of the wall: the permutation diagram of the transposition of `a` and `b`. -/
noncomputable def tr (δ : ℂ) (a b : Fin (r + s)) : B r s δ :=
  diag (WalledDiagram.perm (Equiv.swap a b))

/-- The element `e_{j+1,k+1}` of `B_{r,s}(δ)` (p. 5), for 0-based vertices `j < r ≤ k`: the
diagram with a top arc and a bottom arc joining `j` and `k`, every other vertex joined straight
down. -/
noncomputable def eArc (δ : ℂ) (j k : Fin (r + s)) : B r s δ :=
  diag (WalledDiagram.E j k)

/-- The Jucys–Murphy elements, Definition 2.1 (p. 7), with 0-based vertices: `jm δ k` is the
paper's `L_{k+1}`. For `k < r` it is the sum of the transpositions `(j, k)`, `j < k`; for
`r ≤ k` it is `-∑_{j < r} e_{j,k} + ∑_{r ≤ j < k} (j, k) + δ·1`. -/
noncomputable def jm (δ : ℂ) (k : Fin (r + s)) : B r s δ :=
  if k.val < r then ∑ j ∈ Finset.univ.filter (fun j : Fin (r + s) => j < k), tr δ j k
  else -(∑ j ∈ Finset.univ.filter (fun j : Fin (r + s) => j.val < r), eArc δ j k)
       + ∑ j ∈ Finset.univ.filter (fun j : Fin (r + s) => r ≤ j.val ∧ j < k), tr δ j k
       + algebraMap ℂ (B r s δ) δ

/-- The power-sum element `L_1^k + ⋯ + L_r^k + (-1)^{k+1}(L_{r+1}^k + ⋯ + L_{r+s}^k)` of
Proposition 2.7 (p. 10). -/
noncomputable def jmPowerSum (δ : ℂ) (k : ℕ) : B r s δ :=
  (∑ i ∈ Finset.univ.filter (fun i : Fin (r + s) => i.val < r), jm δ i ^ k)
    + ((-1 : ℂ) ^ (k + 1)) • ∑ i ∈ Finset.univ.filter (fun i : Fin (r + s) => r ≤ i.val), jm δ i ^ k

/-- The substitution of the cancellation property (Definition 2.8 (2)): `x_r ↦ t`,
`y_1 ↦ -t` (with `t = X none`), every other variable `v ↦ X (some v)`. Used only when
`0 < r` and `0 < s`. -/
noncomputable def cancelSubst (hr : 0 < r) (hs : 0 < s) :
    Fin r ⊕ Fin s → MvPolynomial (Option (Fin r ⊕ Fin s)) ℂ := fun v =>
  if v = Sum.inl ⟨r - 1, by omega⟩ then X none
  else if v = Sum.inr ⟨0, hs⟩ then -X none else X (some v)

/-- Supersymmetric polynomials, Definition 2.8 (p. 11): `p ∈ ℂ[x_1, …, x_r, y_1, …, y_s]`
(`x_i = X (Sum.inl i)`, `y_j = X (Sum.inr j)`) is (1) symmetric in the `x`'s and in the `y`'s
separately, and (2) after the substitution `x_r = -y_1 = t` it does not involve `t`. When
`r = 0` or `s = 0` the substitution cannot be made and (2) is vacuous. -/
def IsSupersymmetric (p : MvPolynomial (Fin r ⊕ Fin s) ℂ) : Prop :=
  (∀ (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)), rename (Sum.map σ τ) p = p) ∧
  ∀ (hr : 0 < r) (hs : 0 < s), none ∉ (bind₁ (cancelSubst hr hs) p).vars

/-- The `k`-th power sum supersymmetric polynomial (p. 11):
`p_k = x_1^k + ⋯ + x_r^k + (-1)^{k+1}(y_1^k + ⋯ + y_s^k)`. -/
noncomputable def powerSum (k : ℕ) : MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  ∑ i : Fin r, X (Sum.inl i) ^ k + (-1) ^ (k + 1) * ∑ j : Fin s, X (Sum.inr j) ^ k

/-- `p(L_1, …, L_{r+s})`: the evaluation `x_i ↦ L_i`, `y_j ↦ L_{r+j}`, defined monomial by
monomial with the factors in increasing vertex order. `B_{r,s}(δ)` is not commutative; the
ordering is immaterial because the `L_k` commute (Proposition 2.6), which this definition does
not assume. -/
noncomputable def evalJM (δ : ℂ) (p : MvPolynomial (Fin r ⊕ Fin s) ℂ) : B r s δ :=
  ∑ m ∈ p.support,
    coeff m p • (List.ofFn fun i : Fin (r + s) => jm δ i ^ m (finSumFinEquiv.symm i)).prod

/-- `cont(μ, a + 1)` (p. 12): the content (column minus row) of the box with entry `a + 1` in the
row-reading standard tableau `t^μ` (0-based `a`). -/
def cont (μ : YoungDiagram) (a : ℕ) : ℤ := content (rowOfIndex μ a, colOfIndex μ a)

/-- The content vector `(c(λ, i))_{1 ≤ i ≤ r+s}` of `λ ∈ Λ^t_{r,s}` (p. 12), indexed like the
variables: `x_{i+1} ↦ cont(λ^L, i+1)` if `i < r - t`, else `0`; `y_{j+1}` (vertex `r + j + 1`)
`↦ 0` if `j < t`, else `cont(λ^R, j + 1 - t) + δ`. -/
noncomputable def cVec (δ : ℂ) (x : CellIndex r s) : Fin r ⊕ Fin s → ℂ
  | Sum.inl i => if i.val < r - x.t then ((cont x.L i.val : ℤ) : ℂ) else 0
  | Sum.inr j => if j.val < x.t then 0 else ((cont x.R (j.val - x.t) : ℤ) : ℂ) + δ

/-- `τ_t = e_{r,r+1} e_{r-1,r+2} ⋯ e_{r-t+1,r+t}` of (3.1) (p. 14), for `t ≤ min(r, s)`; with
0-based vertices the `u`-th factor (`u < t`) is the arc element joining `r - 1 - u` and `r + u`.
Outside `t ≤ min(r, s)` (never used) it is `1`. -/
noncomputable def tau (δ : ℂ) (t : ℕ) : B r s δ :=
  if h : t ≤ r ∧ t ≤ s then
    (List.ofFn fun u : Fin t =>
      eArc δ (⟨r - 1 - u.val, by omega⟩ : Fin (r + s)) (⟨r + u.val, by omega⟩ : Fin (r + s))).prod
  else 1

end WalledBrauer.Center


