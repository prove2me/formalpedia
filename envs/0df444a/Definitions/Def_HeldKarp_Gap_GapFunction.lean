-- Prove2me | Definitions.Def_HeldKarp_Gap_GapFunction
-- name    : HeldKarp_Gap_GapFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:31.21916+00:00
-- url     : https://prove2.me/theorems/0843bafe-31a6-4759-b34f-0e9abbd40ba9
-- title:
--   The transformed weights $c_{ij}+\pi_i+\pi_j$, the minimum tour and 1-tree weights, and the gap $f(\pi)$ (§1, pp. 1140–1141)
-- statement:
--   Let $K_n$ be the complete undirected graph on the vertex set $\{1,2,\dots,n\}$, with a real weight $c_{ij}$ on each edge $\{i,j\}$ (no sign, metric or integrality condition). The weight of a subgraph is the sum of the weights of its edges. A **tour** is a cycle passing through each vertex exactly once, and a **1-tree** is a tree on the vertex set $\{2,3,\dots,n\}$ together with two distinct edges at vertex $1$. This item defines, for a real $n$-vector $\pi=(\pi_1,\dots,\pi_n)$:
--
--   1. the **transformed weights** $c_{ij}+\pi_i+\pi_j$ on every edge $\{i,j\}$;
--   2. the **minimum tour weight** $W(c)=\min\{c(H) : H \text{ a tour of } K_n\}$;
--   3. the **minimum 1-tree weight** $\min\{c(T) : T \text{ a 1-tree of } K_n\}$;
--   4. the **gap function** of Held and Karp, the amount by which the weight of a minimum tour exceeds the weight of a minimum 1-tree, both with respect to the transformed weights:
--
--   $$
--   f(\pi)=\min_{H\ \mathrm{tour}}\ \sum_{\{i,j\}\in H}(c_{ij}+\pi_i+\pi_j)\;-\;\min_{T\ \text{1-tree}}\ \sum_{\{i,j\}\in T}(c_{ij}+\pi_i+\pi_j).
--   $$
--
--   Every tour is a 1-tree, so $f(\pi)\ge 0$. The paper studies the minimization of $f$ over all $\pi\in\mathbb R^n$; its main corollary characterizes when $f$ attains the value $0$.
--
--   **Formalization Note** Vertices are `Fin n`; the paper's vertex $1$ is `0 : Fin n`. Weights are a function on unordered pairs `Sym2 (Fin n)` (symmetry built in; the diagonal is never used). Tours and 1-trees are the published predicates `HeldKarp.Ascent.IsTour` (connected and every vertex of degree $2$) and `HeldKarp.Ascent.IsOneTree` (the induced graph on the vertices other than vertex $1$ is a tree, and vertex $1$ has degree $2$), and the weight is the published `HeldKarp.Ascent.weight`. The minima are infima (`sInf`) of the finite sets of tour and 1-tree weights; for $n\ge 3$ these sets are nonempty, so the infima are attained minima. For $n\le 2$ there is neither a tour nor a 1-tree and the infima are the junk value $0$, which is why every theorem using these objects assumes $3\le n$. The gap is defined from the transformed weights as printed, not as $W-w(\pi)$; that identity is a separate theorem.
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, pp. 1139–1141, §1 (definitions of 1-tree, tour, weight; the transformation c_ij → c_ij + π_i + π_j and the gap function f(π), p. 1140; W, p. 1141)

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound

open Classical

namespace HeldKarp.Gap

open HeldKarp.Ascent

/-- **Transformed edge weights** `c_ij + π_i + π_j` (Held & Karp, *The Traveling-Salesman Problem
and Minimum Spanning Trees*, Operations Research 18(6) 1970, §1, p. 1140). The weight of the
unordered pair `{i, j}` is `c {i, j} + π i + π j`; the sum `π i + π j` is symmetric, so this is a
function on `Sym2 (Fin n)`. -/
noncomputable def shift {n : ℕ} (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) : Sym2 (Fin n) → ℝ :=
  fun e => c e + Sym2.lift ⟨fun i j => π i + π j, fun i j => add_comm (π i) (π j)⟩ e

/-- **The weight of a minimum tour** (§1, p. 1141, "W is the weight of a minimum tour with respect
to the weights c_ij"): the least weight `weight c H` over all tours `H` of `K_n`. For `n ≥ 3` the
set is finite and nonempty, so this `sInf` is an attained minimum; for `n ≤ 2` there is no tour
and the value is the junk value `0`. -/
noncomputable def tourMin {n : ℕ} (c : Sym2 (Fin n) → ℝ) : ℝ :=
  sInf {t : ℝ | ∃ H : SimpleGraph (Fin n), IsTour H ∧ t = weight c H}

/-- **The weight of a minimum 1-tree** (§1, pp. 1139–1140): the least weight `weight c G` over all
1-trees `G` of `K_n`. For `n ≥ 3` this `sInf` is an attained minimum over a finite nonempty set;
for `n ≤ 2` there is no 1-tree and the value is the junk value `0`. -/
noncomputable def oneTreeMin {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) : ℝ :=
  sInf {t : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧ t = weight c G}

/-- **The gap function** `f(π)` (§1, p. 1140): "a 'gap' function f(π) equal to the amount by which
the cost of a minimum tour with respect to the weights c_ij+π_i+π_j exceeds the cost of a minimum
1-tree with respect to the same weights." Defined for every real `n`-vector `π`. -/
noncomputable def gap {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) : ℝ :=
  tourMin (shift c π) - oneTreeMin (shift c π)

end HeldKarp.Gap


