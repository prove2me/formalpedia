-- Prove2me | Definitions.Def_BipMatchNC_Weighted_BlowUp
-- name    : BipMatchNC_Weighted_BlowUp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:14:33.590712+00:00
-- url     : https://prove2.me/theorems/24052e25-bcb8-4db4-b576-726436809aaa
-- title:
--   The blow-up graph G^{r,δ}, its weights ŵ, the subgraphs G^{r,δ}[S], ŵ_S, column submatrices M[S] and the lifted dual (ŷ, ẑ) (Definition 3.6, §3.3)
-- statement:
--   The **blow-up graph** $G^{r,\delta}$ of a balanced bipartite graph $G$ (with $D=n(r-\delta)$) has left vertices $u_{i,p}$ ($i\in[n]$, $p\in[D]$) and right vertices $v_{j,q}$ ($j\in[n]$, $q\in[r]$) and $a_{i,q}$ ($i\in[n]$, $q\in[(n-1)r]$); its edges are $(u_{i,p},v_{j,q})$ for $(u_i,v_j)\in E$, with weight $\hat w=w(u_i,v_j)$, and $(u_{i,p},a_{i,q})$ with weight $0$. Its bi-adjacency matrix is the support pattern of $M(G)$, so its right vertex set $\hat R$ indexes the columns of $M(G)$ and $M(G,w)$.
--
--   For $S\subseteq\hat R$ with $|S|=nD$, $G^{r,\delta}[S]$ deletes the right vertices outside $S$, $M[S]$ keeps the columns in $S$, and
--   $$\hat w_S=\max\{\hat w(T): T\text{ a perfect matching of }G^{r,\delta}[S]\}.$$
--   For a dual solution $(y,z)$ of $G$, the **lifted dual** $(\hat y,\hat z)$ gives every copy $u_{i,p}$ the value $y_{u_i}$, every copy $v_{j,q}$ the value $z_{v_j}$, and $a_{i,q}$ the value $-y_{u_i}$.
--
--   **Formalization Note.** Left vertices are rows `(i, p) : Fin n × Fin D`, right vertices are columns `(j, q) : Fin (n * n) × Fin r` of $M(G)$: `(j, q)` with `j < n` is $v_{j+1,q+1}$, and `(n + i (n-1) + b, q)` with `b < n - 1` is $a_{i+1,br+q+1}$. Then `blowUpAdj G r D (i, p) (j, q) = extAdj G i j`. `blowUpWeight`, `blowUpAdjOn`/`blowUpWeightOn` (on `↥S`), `blowUpPMWeight` ($\hat w_S$, $0$ if $G^{r,\delta}[S]$ has no perfect matching), `colSubmatrix M S e` (columns of $S$ in the order of a bijection `e : Fin n × Fin D ≃ S`; another order changes every determinant only by the same sign), `liftY`, `liftZ`. Definition 3.6 prints the weight of $(u_{i,p},v_{i,q})$; the intended $v_{j,q}$ is used.
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 14 (PDF 15), Definition 3.6, and pp. 16–17 (PDF 17–18), §3.3

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_Bipartite
import Definitions.Def_BipMatchNC_Weighted_Graph
import Definitions.Def_BipMatchNC_Weighted_MatchingMatrix

namespace BipMatchNC.Weighted

/-! The **blow-up graph** `G^{r,δ}` (Definition 3.6, p. 14), its induced weights `ŵ`, the column
submatrices `M[S]`, the subgraphs `G^{r,δ}[S]` and the lifted dual solution `(ŷ, ẑ)` (§3.3,
pp. 16–17).

**Formalization Note (vertex indexing).** The left vertex `u_{i,p}` (`i ∈ [n]`, `p ∈ [D]`) is the
row index `(i - 1, p - 1) : Fin n × Fin D` of `M(G)`. The right vertex set `R̂` is the column index
set `Fin (n * n) × Fin r` of `M(G)`, in the natural order: column `(j, q)` with `j < n` is
`v_{j+1, q+1}`, and column `(n + i (n - 1) + b, q)` with `b < n - 1` is `a_{i+1, b r + q + 1}`.
With this indexing the bi-adjacency matrix of `G^{r,δ}` is the support pattern of `M(G)`
(`(A^{r,δ})_{i,j} = 1` iff `M(G)_{i,j} ≠ 0`, p. 14, when all `α_j ≠ 0`). -/

variable {n : ℕ}

/-- The edges of `G^{r,δ}`: `(u_{i,p}, v_{j,q})` for every edge `(u_i, v_j)` of `G`, and
`(u_{i,p}, a_{i,q})` for all `p, q`. Equivalently, `(i, p) ~ (j, q)` iff `Â_{i,j} = 1`. -/
def blowUpAdj (G : BipGraph n) (r D : ℕ) (a : Fin n × Fin D) (b : Fin (n * n) × Fin r) : Bool :=
  extAdj G a.1 b.1

/-- The induced weight `ŵ` (Definition 3.6, p. 14): `ŵ(u_{i,p}, v_{j,q}) = w(u_i, v_j)`, and the
edges `(u_{i,p}, a_{i,q})` to the additional vertices have weight `0`. -/
def blowUpWeight (w : Fin n → Fin n → ℕ) (r D : ℕ) (a : Fin n × Fin D)
    (b : Fin (n * n) × Fin r) : ℕ :=
  if h : (b.1 : ℕ) < n then w a.1 ⟨b.1, h⟩ else 0

/-- The edges of `G^{r,δ}[S]`, the graph obtained from `G^{r,δ}` by deleting all right vertices
outside `S` (§3.3, p. 16). -/
def blowUpAdjOn (G : BipGraph n) (r D : ℕ) (S : Finset (Fin (n * n) × Fin r))
    (a : Fin n × Fin D) (b : ↥S) : Bool :=
  blowUpAdj G r D a b.1

/-- The weights `ŵ` on `G^{r,δ}[S]`. -/
def blowUpWeightOn (w : Fin n → Fin n → ℕ) (r D : ℕ) (S : Finset (Fin (n * n) × Fin r))
    (a : Fin n × Fin D) (b : ↥S) : ℕ :=
  blowUpWeight w r D a b.1

/-- `ŵ_S = max { ŵ(T) | T is a perfect matching in G^{r,δ}[S] }` (§3.3, p. 17); `0` if there is
none. -/
def blowUpPMWeight (G : BipGraph n) (w : Fin n → Fin n → ℕ) (r D : ℕ)
    (S : Finset (Fin (n * n) × Fin r)) : ℕ :=
  maxPerfectMatchingWeight (blowUpAdjOn G r D S) (blowUpWeightOn w r D S)

/-- The column submatrix `M[S]` (§3.3, p. 16) for a set `S` of `nD` columns, with the columns of `S`
listed in the order given by the bijection `e : Fin n × Fin D ≃ S`. A different order changes
`det M[S]` only by a sign, the same for every matrix of this shape. -/
def colSubmatrix {K : Type*} {D r : ℕ} (M : Matrix (Fin n × Fin D) (Fin (n * n) × Fin r) K)
    (S : Finset (Fin (n * n) × Fin r)) (e : Fin n × Fin D ≃ ↥S) :
    Matrix (Fin n × Fin D) (Fin n × Fin D) K :=
  M.submatrix id fun a => (e a).1

/-- The lifted dual values of the left vertices (proof of Claim 3.10, p. 16): every copy `u_{i,p}`
gets the value `y_{u_i}`. -/
def liftY (D : ℕ) (y : Fin n → ℝ) (a : Fin n × Fin D) : ℝ :=
  y a.1

/-- The lifted dual values of the right vertices (proof of Claim 3.10, p. 16): every copy `v_{j,q}`
gets `z_{v_j}`, and the additional vertex `a_{i,q}` gets `-y_{u_i}`. For a column block
`j ≥ n` exactly one row `i` has `Â_{i,j} = 1`, so the sum below is `-y_i` for that `i`. -/
def liftZ (G : BipGraph n) (r : ℕ) (y z : Fin n → ℝ) (b : Fin (n * n) × Fin r) : ℝ :=
  if h : (b.1 : ℕ) < n then z ⟨b.1, h⟩
  else -∑ i, if extAdj G i b.1 then y i else 0

end BipMatchNC.Weighted


