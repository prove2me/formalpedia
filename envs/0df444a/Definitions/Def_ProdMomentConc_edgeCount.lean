-- Prove2me | Definitions.Def_ProdMomentConc_edgeCount
-- name    : ProdMomentConc_edgeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:12:13.570994+00:00
-- url     : https://prove2.me/theorems/038b4fd4-9328-4875-9153-7ae817eaf1a1
-- title:
--   Edges and average degrees $d_L$, $d_R$ of the dependency graph
-- statement:
--   Let $X_1,\dots,X_m$ be the underlying variables and $Y_1,\dots,Y_n$ the outputs, where output $i$ reads the variables indexed by a set $P_i \subseteq [m]$. The **bipartite dependency graph** has the underlying variables as left vertices, the outputs as right vertices, and an edge between $j$ and $i$ exactly when $j \in P_i$. Its number of edges is
--
--   $$
--   E := \sum_{i=1}^n |P_i|,
--   $$
--
--   and the **average left and right degrees** are
--
--   $$
--   d_L := \frac{E}{m}, \qquad d_R := \frac{E}{n},
--   $$
--
--   so that $d_L m = d_R n = E$.
--
--   These quantities enter the conditions (8) and (9) of the main theorem and the expectation bound $\mathbb E L_k \le d_R k$.
--
--   **Formalization Note** $P$ is a function from `Fin n` to finite subsets of `Fin m`. $d_L$ and $d_R$ are real numbers; for $m = 0$ (resp. $n = 0$) Lean's division gives $0$, a case the main statements exclude through $1 \le r \le m$.
-- source:
--   Saks, Srinivasan, Valieva, Concentration from Product Moments via an Additional Element of Randomness, arXiv:2608.04125 (held version, sha256 5218e9d0405f975413d3e2dd2c4c9d6b43c772029e645965afee1cd619ae38aa), §3.2, p.15 (PDF p.15), "Let dL and dR denote the average left and right degrees, so that dLm = dRn"; dependency graph, §1.2, p.4

import Mathlib

namespace ProdMomentConc

/-- **Number of edges of the dependency graph.**
Saks, Srinivasan, Valieva, arXiv:2608.04125 (held version, sha256 5218e9d0…), §3.2, p.15. The
bipartite dependency graph has left vertices the underlying variables `j ∈ [m]` and right vertices
the outputs `i ∈ [n]`, with an edge `(j, i)` iff `Yᵢ` reads `Xⱼ`, i.e. `j ∈ P i`. Its number of
edges is `∑ᵢ |Pᵢ|`.

**Formalization Note.** `P : Fin n → Finset (Fin m)` lists, for each output, the underlying
variables it reads. -/
def edgeCount {m n : ℕ} (P : Fin n → Finset (Fin m)) : ℕ :=
  ∑ i, (P i).card

/-- **Average left degree** `d_L` (p.15: "Let dL and dR denote the average left and right degrees,
so that dLm = dRn"): the number of edges divided by the number `m` of underlying variables.

**Formalization Note.** Real division; for `m = 0` Lean's convention gives `0`, a case excluded in
this mission's main statements by `1 ≤ r ≤ m`. -/
noncomputable def dL {m n : ℕ} (P : Fin n → Finset (Fin m)) : ℝ :=
  (edgeCount P : ℝ) / m

/-- **Average right degree** `d_R` (p.15): the number of edges divided by the number `n` of
outputs.

**Formalization Note.** Real division; for `n = 0` Lean's convention gives `0`. -/
noncomputable def dR {m n : ℕ} (P : Fin n → Finset (Fin m)) : ℝ :=
  (edgeCount P : ℝ) / n

end ProdMomentConc


