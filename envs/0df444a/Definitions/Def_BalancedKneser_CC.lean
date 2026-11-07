-- Prove2me | Definitions.Def_BalancedKneser_CC
-- name    : BalancedKneser_CC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:52.561518+00:00
-- url     : https://prove2.me/theorems/09690e50-f8b7-41b3-a464-6f5f5d23c377
-- title:
--   Johnson-center complex $C_c(N,k)$: families with a common center at Johnson distance $\le c$
-- statement:
--   For $k$-subsets $A,Z$ of $[N]$, the **Johnson distance** is $d_J(A,Z)=k-|A\cap Z|$, the number of replacements needed to turn $A$ into $Z$. For an integer $c\ge 0$, the complex $C_c(N,k)$ has the $k$-subsets of $[N]$ as vertices (called labels), and its nonempty faces are the families $\sigma$ with a **common center at distance at most $c$**:
--   $$
--   \sigma\in C_c(N,k)\iff \sigma\ne\emptyset\ \text{and}\ \exists Z\subseteq[N],\ |Z|=k,\ d_J(A,Z)\le c\ \text{for all } A\in\sigma .
--   $$
--   For $n>c$, complementation turns a common neighbor in $G_{n,c+1}$ into a center, so $N(G_{n,c+1})=C_c(2n,n)$; the source uses $C_1(2n,n)$, $C_2(2n,n)$, $C_2(9,3)$ and $C_2(8,4)$.
--
--   **Formalization Note** $d_J(A,Z)\le c$ is written $k\le|A\cap Z|+c$, avoiding truncated subtraction; $[N]$ is $\mathrm{Fin}\,N$.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.2, p.6 (PDF p.8): Johnson distance, C₁(N, k); §4.1, p.8 (PDF p.10): C₂(N, k); §9.2, p.18 (PDF p.20): C_c(N, k)

import Mathlib
import Definitions.Def_BalancedKneser_KG

namespace BalancedKneser

/-- **The Johnson-center complex** `C_c(N, k)` (Alipour–Jafari, *Balanced Fair Division and
Generalized Kneser Graphs*, arXiv:2611.04486v1, §3.2, p.6 (PDF p.8); §4.1, p.8 (PDF p.10);
§9.2, p.18 (PDF p.20)). For `k`-subsets `A, Z` of `[N]` the Johnson distance is
`d_J(A, Z) = k − |A ∩ Z|`. The vertices of `C_c(N, k)` are the `k`-subsets of `[N]` (the
"labels"), and its nonempty faces are the families with a common center at Johnson distance at
most `c`: a `k`-set `Z` with `d_J(A, Z) ≤ c` for every member `A`.

Formalization Note: `d_J(A, Z) ≤ c` is written `k ≤ |A ∩ Z| + c`, avoiding truncated
subtraction; `[N]` is `Fin N`. -/
def CC (c N k : ℕ) : Set (Finset (KSet N k)) :=
  {σ | σ.Nonempty ∧ ∃ Z : Finset (Fin N), Z.card = k ∧ ∀ A ∈ σ, k ≤ (A.1 ∩ Z).card + c}

end BalancedKneser


