-- Prove2me | Definitions.Def_MMSDelta2_KPW
-- name    : MMSDelta2_KPW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:58.960517+00:00
-- url     : https://prove2.me/theorems/e518f452-e3fe-462b-aaa7-a7800b8996b3
-- title:
--   The KPW core: matrices $S$, $T$, $M=S+T$ and $A=2^{750}M$
-- statement:
--   Let $\varepsilon=2^{-125}$ and, for $i\in[3]$, $r_i=\varepsilon^{8-2i}$ and $c_i=\varepsilon^{7-2i}$, so $r_1<c_1<r_2<c_2<r_3<c_3=\varepsilon$. Put $u_1=c_1$, $v_1=r_1$, $u_2=c_2-r_1$, $v_2=r_2-c_1$, $u_3=c_1+c_3-r_2$, $v_3=r_1+r_3-c_2$, $x=v_3$, $y=u_3$, $z=r_1+c_1+r_3+c_3$, and
--
--   $$S=\begin{pmatrix}\tfrac{15}{16}&0&0&0&\tfrac1{16}\\0&\tfrac78&0&0&\tfrac18\\0&0&\tfrac34&0&\tfrac14\\0&0&0&\tfrac12&\tfrac12\\\tfrac1{16}&\tfrac18&\tfrac14&\tfrac12&\tfrac1{16}\end{pmatrix},\qquad T=\begin{pmatrix}0&v_1&0&0&-r_1\\u_1&0&v_2&0&-r_2\\0&u_2&0&v_3&-r_3\\0&0&u_3&0&-y\\-c_1&-c_2&-c_3&-x&z\end{pmatrix}.$$
--
--   Let $M=S+T$, $M^+=\{(i,j):M_{i,j}>0\}$ and $M(X)=\sum_{(i,j)\in X}M_{i,j}$ for $X\subseteq M^+$. With $\alpha=2^{750}$, the integer matrix is $A_{i,j}=\alpha M_{i,j}$ and $A^+=\{(i,j):A_{i,j}>0\}$. For a set $Y$ of positions, $R_i$ and $C_j$ are its positions in row $i$ and column $j$. A partition $(X_1,\dots,X_5)$ of $Y$ is the **row partition up to relabeling** if $\{X_1,\dots,X_5\}=\{R_1,\dots,R_5\}$ as indexed by a permutation, and the **column partition up to relabeling** likewise with $C_1,\dots,C_5$.
--
--   These are the objects of Lemmas 5.1, 5.2 and Proposition 5.3, and $A$ is the core of the §7 reduction.
--
--   **Formalization Note** Rows and columns are indexed $0,\dots,4$ (the paper's $1,\dots,5$), and $r_i,c_i,u_i,v_i$ are indexed by $i-1\in\{0,1,2\}$. $A_{i,j}$ is defined as $\lfloor\alpha M_{i,j}\rfloor$ as a natural number; $\alpha M_{i,j}$ is a nonnegative integer for every entry. A partition is an indexed family of five pairwise disjoint, possibly empty sets with union $Y$.
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), §5.1, pp.13–14 and p.20 (PDF pp.15–16, 22); Definition 2.1, p.5 (PDF p.7)

import Mathlib

namespace MMSDelta2

/-!
# The KPW core for five agents: the matrices `S`, `T`, `M = S + T` and `A = 2^750·M`

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…), §5.1, pp.13–14 and 20 (PDF pp.15–16, 22):
`K = 125`, `ε = 2^{−K}`, `r_i = ε^{8−2i}`, `c_i = ε^{7−2i}` (`i ∈ [3]`), `u_1 = c_1`, `v_1 = r_1`,
`u_2 = c_2 − r_1`, `v_2 = r_2 − c_1`, `u_3 = c_1 + c_3 − r_2`, `v_3 = r_1 + r_3 − c_2`, `x = v_3`,
`y = u_3`, `z = r_1 + c_1 + r_3 + c_3`, the matrices `S` and `T` as printed, `M = S + T`,
`M⁺ = {(i,j) : M_{i,j} > 0}`, `M(X) = Σ_{(i,j)∈X} M_{i,j}`, `α = 2^750`, `A_{i,j} = α M_{i,j}`,
`A⁺ = {(i,j) : A_{i,j} > 0}`; `R_i`, `C_j` are the positive entries of row `i` and column `j`
(Definition 2.1, p.5: row partition and column partition).

**Formalization Note.**
* Indices are 0-based: row/column `0, …, 4` are the paper's `1, …, 5`; `kpwR i`, `kpwC i`,
  `kpwU i`, `kpwV i` for `i : Fin 3` are `r_{i+1}`, `c_{i+1}`, `u_{i+1}`, `v_{i+1}`.
* `kpwA i j` is `⌊α M_{i,j}⌋` as a natural number; `α M_{i,j}` is a nonnegative integer for every
  entry, so this is `α M_{i,j}`.
* A partition of a set `Y` of positions into five bundles is an indexed family `X : Fin 5 → Finset`
  of pairwise disjoint sets with union `Y` (bundles may be empty). "The row partition, up to
  relabeling" means `X t = R_{π t}` for a permutation `π`; likewise for columns.
-/

/-- `ε = 2^{−125}`. -/
def kpwEps : ℚ := 1 / 2 ^ 125

/-- `r_i = ε^{8−2i}` (`i ∈ [3]`, here `i = k + 1`). -/
def kpwR (k : Fin 3) : ℚ := kpwEps ^ (8 - 2 * (k.val + 1))

/-- `c_i = ε^{7−2i}` (`i ∈ [3]`, here `i = k + 1`). -/
def kpwC (k : Fin 3) : ℚ := kpwEps ^ (7 - 2 * (k.val + 1))

/-- `u_1 = c_1`, `u_2 = c_2 − r_1`, `u_3 = c_1 + c_3 − r_2`. -/
def kpwU : Fin 3 → ℚ := ![kpwC 0, kpwC 1 - kpwR 0, kpwC 0 + kpwC 2 - kpwR 1]

/-- `v_1 = r_1`, `v_2 = r_2 − c_1`, `v_3 = r_1 + r_3 − c_2`. -/
def kpwV : Fin 3 → ℚ := ![kpwR 0, kpwR 1 - kpwC 0, kpwR 0 + kpwR 2 - kpwC 1]

/-- `x = v_3`. -/
def kpwX : ℚ := kpwV 2

/-- `y = u_3`. -/
def kpwY : ℚ := kpwU 2

/-- `z = r_1 + c_1 + r_3 + c_3`. -/
def kpwZ : ℚ := kpwR 0 + kpwC 0 + kpwR 2 + kpwC 2

/-- The matrix `S` (p.13). -/
def kpwS : Matrix (Fin 5) (Fin 5) ℚ :=
  !![15/16, 0, 0, 0, 1/16;
     0, 7/8, 0, 0, 1/8;
     0, 0, 3/4, 0, 1/4;
     0, 0, 0, 1/2, 1/2;
     1/16, 1/8, 1/4, 1/2, 1/16]

/-- The adjustment matrix `T` (p.14). -/
def kpwT : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0, kpwV 0, 0, 0, -kpwR 0;
     kpwU 0, 0, kpwV 1, 0, -kpwR 1;
     0, kpwU 1, 0, kpwV 2, -kpwR 2;
     0, 0, kpwU 2, 0, -kpwY;
     -kpwC 0, -kpwC 1, -kpwC 2, -kpwX, kpwZ]

/-- `M = S + T`. -/
def kpwM : Matrix (Fin 5) (Fin 5) ℚ := kpwS + kpwT

/-- `M⁺`, the positions of the positive entries of `M`. -/
def kpwMplus : Finset (Fin 5 × Fin 5) := Finset.univ.filter fun p => 0 < kpwM p.1 p.2

/-- `M(X) = Σ_{(i,j) ∈ X} M_{i,j}`. -/
def kpwMsum (X : Finset (Fin 5 × Fin 5)) : ℚ := ∑ p ∈ X, kpwM p.1 p.2

/-- `α = 2^750`. -/
def kpwAlpha : ℕ := 2 ^ 750

/-- The KPW integer matrix `A_{i,j} = α M_{i,j}` (p.20). -/
def kpwA (i j : Fin 5) : ℕ := (⌊(kpwAlpha : ℚ) * kpwM i j⌋).toNat

/-- `A⁺`, the positions of the positive entries of `A`. -/
def kpwAplus : Finset (Fin 5 × Fin 5) := Finset.univ.filter fun p => 0 < kpwA p.1 p.2

/-- `R_i ∩ Y`: the positions of `Y` in row `i`. -/
def rowSet (Y : Finset (Fin 5 × Fin 5)) (i : Fin 5) : Finset (Fin 5 × Fin 5) :=
  Y.filter fun p => p.1 = i

/-- `C_j ∩ Y`: the positions of `Y` in column `j`. -/
def colSet (Y : Finset (Fin 5 × Fin 5)) (j : Fin 5) : Finset (Fin 5 × Fin 5) :=
  Y.filter fun p => p.2 = j

/-- `(X_1, …, X_5)` is a partition of `Y`: pairwise disjoint with union `Y`. -/
def IsPartitionOf (Y : Finset (Fin 5 × Fin 5)) (X : Fin 5 → Finset (Fin 5 × Fin 5)) : Prop :=
  Pairwise (fun s t => Disjoint (X s) (X t)) ∧ Finset.univ.biUnion X = Y

/-- `(X_1, …, X_5)` is the row partition or the column partition of `Y`, up to relabeling. -/
def IsRowOrColPartition (Y : Finset (Fin 5 × Fin 5)) (X : Fin 5 → Finset (Fin 5 × Fin 5)) :
    Prop :=
  (∃ π : Equiv.Perm (Fin 5), ∀ t, X t = rowSet Y (π t)) ∨
    (∃ π : Equiv.Perm (Fin 5), ∀ t, X t = colSet Y (π t))

end MMSDelta2


