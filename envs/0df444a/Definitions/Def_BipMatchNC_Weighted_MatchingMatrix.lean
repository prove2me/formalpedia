-- Prove2me | Definitions.Def_BipMatchNC_Weighted_MatchingMatrix
-- name    : BipMatchNC_Weighted_MatchingMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:13:24.567674+00:00
-- url     : https://prove2.me/theorems/fd18fdc8-08ad-45ba-a944-cbf0420acd4b
-- title:
--   The extension matrix Â, the matching matrix M(G), the weighted matching matrix M(G, w), D_w(t) and block polynomials (§3.1, §3.3)
-- statement:
--   Let $G$ be a balanced bipartite graph with bi-adjacency matrix $A$. The **extension matrix** is the $n\times n^2$ matrix $\hat A=(A\ A_0)$, where row $i$ of the $n\times n(n-1)$ matrix $A_0$ has ones exactly in its own block of $n-1$ columns: $\hat A_{i,j}=1$ for $n+(i-1)(n-1)<j\le n+i(n-1)$.
--
--   Fix $\gamma\in F$, $\alpha_1,\dots,\alpha_{n^2}\in F$ and $D,r$. The **matching matrix** $M(G)$ is the $nD\times n^2r$ matrix obtained from $\hat A$ by replacing every $1$ in column $j$ by the $D\times r$ folded Vandermonde matrix $V(\alpha_j)$ and every $0$ by a $D\times r$ zero block. The **weighted matching matrix** $M(G,w)$ over $F[t]$ has $(i,j)$ block
--   $$\begin{cases}t^{w(i,j)}V(\alpha_j)&j\le n,\ (i,j)\in E,\\ V(\alpha_j)& n+(n-1)(i-1)<j\le n+(n-1)i,\\ 0&\text{otherwise,}\end{cases}$$
--   and $\mathcal D_w(t)=\det\big(M(G,w)M(G,w)^T\big)$. For $p\in F^{nD}$ split into blocks $p=(p_1,\dots,p_n)$, $p_i\in F^D$, the **block polynomial** $p_i(x)=\sum_{k=0}^{D-1}p_{i,k}x^k$.
--
--   **Formalization Note.** Indices are 0-based. Rows of `matchingMatrix γ α r D G` are `(i, p) : Fin n × Fin D` (row `p` of block `i`), columns `(j, q) : Fin (n * n) × Fin r` (column `q` of block `j`); `extAdj G i j` is $\hat A_{i,j}$, with the 0-based condition $n+i(n-1)\le j<n+(i+1)(n-1)$ for $j\ge n$. `weightedMatchingMatrix` uses `X` for $t$; `detPoly` is $\mathcal D_w(t)$; `blockPoly p i` is $p_i(x)$. The parameters $\gamma,\alpha,r,D$ are arguments; the theorems impose the paper's conditions.
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), pp. 9–10 (PDF 10–11), §3.1, and pp. 13–14 (PDF 14–15), §3.3

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Folded
import Definitions.Def_BipMatchNC_Weighted_Graph

namespace BipMatchNC.Weighted

open Polynomial Matrix

/-- The entries of the `n × n²` **extension matrix** `Â = (A A₀)` (§3.1, p. 9): column block `j < n`
is column `j` of the bi-adjacency matrix `A`; row `i` of `A₀` has ones exactly in its own block of
`n - 1` columns, i.e. (1-based, as on p. 13) `Â_{i,j} = 1` for `n + (i-1)(n-1) < j ≤ n + i(n-1)`.

**Formalization Note.** Indices are 0-based: row `i : Fin n`, column `j : Fin (n * n)`; the 1-based
condition becomes `n + i (n - 1) ≤ j < n + (i + 1)(n - 1)`. -/
def extAdj {n : ℕ} (G : BipGraph n) (i : Fin n) (j : Fin (n * n)) : Bool :=
  if h : (j : ℕ) < n then G.adj i ⟨j, h⟩
  else decide (n + (i : ℕ) * (n - 1) ≤ (j : ℕ) ∧ (j : ℕ) < n + ((i : ℕ) + 1) * (n - 1))

/-- The **matching matrix** `M(G)` (§3.1, p. 9): the `nD × n²r` matrix obtained from `Â` by replacing
every `1` in column `j` by the `D × r` `γ`-folded Vandermonde matrix `V(α_j)` and every `0` by the
`D × r` zero matrix.

**Formalization Note.** Row `(i, p)` is row `p` of row block `i`; column `(j, q)` is column `q` of
column block `j` (all 0-based). The parameters `γ`, `α = (α_j)_{j < n²}`, `r` and `D` are
arguments; the theorems impose the paper's conditions on them. -/
def matchingMatrix {F : Type*} [Field F] (γ : F) {n : ℕ} (α : Fin (n * n) → F) (r D : ℕ)
    (G : BipGraph n) : Matrix (Fin n × Fin D) (Fin (n * n) × Fin r) F :=
  fun a b => if extAdj G a.1 b.1 then foldedVandermonde γ (α b.1) D r a.2 b.2 else 0

/-- The **weighted matching matrix** `M(G, w)` (§3.3, p. 13), over `F[t]` (`t = X`): block `(i, j)`
is `t^{w(i,j)} V(α_j)` if `j ≤ n` and `(i, j) ∈ E`, `V(α_j)` if `n + (n-1)(i-1) < j ≤ n + (n-1)i`,
and `0` otherwise (1-based; the code is 0-based as in `matchingMatrix`). -/
noncomputable def weightedMatchingMatrix {F : Type*} [Field F] (γ : F) {n : ℕ}
    (α : Fin (n * n) → F) (r D : ℕ) (G : BipGraph n) (w : Fin n → Fin n → ℕ) :
    Matrix (Fin n × Fin D) (Fin (n * n) × Fin r) F[X] :=
  fun a b =>
    if h : (b.1 : ℕ) < n then
      (if G.adj a.1 ⟨b.1, h⟩ then
        X ^ (w a.1 ⟨b.1, h⟩) * C (foldedVandermonde γ (α b.1) D r a.2 b.2) else 0)
    else if extAdj G a.1 b.1 then C (foldedVandermonde γ (α b.1) D r a.2 b.2) else 0

/-- `D_w(t) = det(M(G, w) M(G, w)^T)` (§3.3, p. 14), a polynomial in `t`. -/
noncomputable def detPoly {F : Type*} [Field F] (γ : F) {n : ℕ} (α : Fin (n * n) → F) (r D : ℕ)
    (G : BipGraph n) (w : Fin n → Fin n → ℕ) : F[X] :=
  (weightedMatchingMatrix γ α r D G w * (weightedMatchingMatrix γ α r D G w)ᵀ).det

/-- The polynomial `p_i(x)` of block `i` of a vector `p ∈ F^{nD}` (proof of Theorem 3.1, p. 10): "We
view each `p_i` as the coefficient vector of a polynomial `p_i(x)`" of degree at most `D - 1`, the
entry `p_{(i,k)}` being the coefficient of `x^k`. Then `p^T V(α) = 0` says that `α` is an `r`-folded
root of `p_i(x)`. -/
noncomputable def blockPoly {F : Type*} [Field F] {n D : ℕ} (p : Fin n × Fin D → F) (i : Fin n) :
    F[X] :=
  ∑ k : Fin D, monomial (k : ℕ) (p (i, k))

end BipMatchNC.Weighted


