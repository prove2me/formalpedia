-- Prove2me | Definitions.Def_ProcNetStab_Supplement_WeightedNet
-- name    : ProcNetStab_Supplement_WeightedNet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:54:41.507547+00:00
-- url     : https://prove2.me/theorems/6d9c55fa-3a60-57f9-ad51-e43288cd1d70
-- title:
--   Weighted networks $g=(N,W)$, the update $(x,g_{-ij})$ and the unweighted network $B(g)$
-- statement:
--   Let $V$ be a set of agents. A **weighted network** on $V$ is a matrix $W = (W_{ij})_{i,j \in V}$ of link weights such that
--   $$
--   W_{ij} = W_{ji}, \qquad 0 \le W_{ij} \le 1 \quad\text{for all } i, j, \qquad W_{ii} = 0 .
--   $$
--   $W_{ij}$ is the weight of the link between $i$ and $j$; weight $0$ means there is no link.
--
--   For a weighted network $g$, nodes $i, j$ and a weight $x \in [0,1]$, the network $(x, g_{-ij})$ is obtained from $g$ by setting the weight between $i$ and $j$ (both $W_{ij}$ and $W_{ji}$) to $x$ and keeping every other weight. Thus $g = (W_{ij}, g_{-ij})$.
--
--   The **unweighted network** $B(g)$ of $g$ is the (simple, undirected) network on $V$ in which $i$ and $j$ are linked if and only if $i \ne j$ and $W_{ij} = W_{ji} > 0$.
--
--   These are the objects of §5 of the paper: utilities are defined on weighted networks, and the $k$-neighborhoods and $k$-isomorphisms of a weighted network are those of $B(g)$.
--
--   **Formalization Note** Nodes form an arbitrary type $V$ (the paper's $N=\{1,\dots,n\}$ is a special case). The diagonal is fixed at $0$, so weighted networks correspond exactly to symmetric $[0,1]$-weights on pairs of distinct nodes. The update writes the weight $\max(0,\min(x,1))$, which is $x$ for every $x \in [0,1]$ (the only weights the mission uses); for $i = j$ it changes nothing.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), §5, p.18 (weighted networks, the notation (x, g−ij)) and §5.1, p.19 (the unweighted network B(g))

import Mathlib

namespace ProcNetStab.Supplement

/-- A **weighted network** on the node set `V` (Chiong, Qi, *Stability of Procurement Networks*
(authors' manuscript, 2025), §5, p.18, following Bich and Morhaim 2020): a matrix `W` of link
weights, symmetric, with every weight in `[0, 1]`.

**Formalization Note** Nodes form an arbitrary type `V` (the paper's `N = {1, …, n}`). The
diagonal is fixed at `0`: an undirected network has no self-links, and fixing the diagonal makes
weighted networks correspond exactly to symmetric `[0,1]`-weights on pairs of distinct nodes. -/
structure WeightedNet (V : Type*) where
  /-- The weight `W i j` of the link between `i` and `j`. -/
  W : V → V → ℝ
  symm : ∀ i j, W i j = W j i
  diag : ∀ i, W i i = 0
  nonneg : ∀ i j, 0 ≤ W i j
  le_one : ∀ i j, W i j ≤ 1

/-- The weight `x` clipped to `[0, 1]`; it is `x` itself for every weight `x ∈ [0, 1]`. -/
noncomputable def clipWeight (x : ℝ) : ℝ := max 0 (min x 1)

open Classical in
/-- The weighted network `(x, g_{-ij})` (Chiong, Qi, *Stability of Procurement Networks* (authors'
manuscript, 2025), §5, p.18): `g` with the weight between `i` and `j` (both `W i j` and `W j i`)
set to `x`, all other weights unchanged.

**Formalization Note** Every use in the mission has `x ∈ [0, 1]`; the weight written is
`clipWeight x`, which equals `x` there and keeps the result a weighted network for every real `x`.
For `i = j` nothing changes (the diagonal stays `0`). -/
noncomputable def setWeight {V : Type*} (g : WeightedNet V) (i j : V) (x : ℝ) : WeightedNet V where
  W a b := if a ≠ b ∧ s(a, b) = s(i, j) then clipWeight x else g.W a b
  symm a b := by
    by_cases h : a ≠ b ∧ s(a, b) = s(i, j)
    · have h' : b ≠ a ∧ s(b, a) = s(i, j) := ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
      rw [if_pos h, if_pos h']
    · have h' : ¬ (b ≠ a ∧ s(b, a) = s(i, j)) := by
        rintro ⟨h1, h2⟩; exact h ⟨h1.symm, by rw [Sym2.eq_swap]; exact h2⟩
      rw [if_neg h, if_neg h', g.symm]
  diag a := by simp [g.diag]
  nonneg a b := by
    split_ifs
    · exact le_max_left _ _
    · exact g.nonneg a b
  le_one a b := by
    split_ifs
    · exact max_le zero_le_one (min_le_right _ _)
    · exact g.le_one a b

/-- The **unweighted network** `B(g)` of a weighted network `g` (Chiong, Qi, *Stability of
Procurement Networks* (authors' manuscript, 2025), §5.1, p.19): there is a link between `i` and `j`
if and only if `W i j = W j i > 0`.

**Formalization Note** `B(g)` is a `SimpleGraph V`, the network type of the base mission; a link
needs distinct nodes `i ≠ j` (with the diagonal fixed at `0` this is automatic). -/
def support {V : Type*} (g : WeightedNet V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ 0 < g.W i j
  symm := ⟨fun i j h => ⟨h.1.symm, g.symm i j ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end ProcNetStab.Supplement


