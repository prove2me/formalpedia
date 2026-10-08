-- Prove2me | Definitions.Def_DistVerif_Simulation_Network
-- name    : DistVerif_Simulation_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:14.814977+00:00
-- url     : https://prove2.me/theorems/9eabdd76-bca4-465e-9306-63e629ecdfe0
-- title:
--   The network $G(\Gamma,d,p)$, its special nodes $s,r$ and the sets $L_i$, $R_i$ (§3.1–3.2, pp. 1247–1248)
-- statement:
--   Fix integers $\Gamma, d, p \ge 0$. The network $G(\Gamma,d,p)$ is the undirected graph built from two kinds of pieces.
--
--   1. **Paths.** There are $\Gamma$ paths $\mathcal P^1,\dots,\mathcal P^\Gamma$, each with $d^p$ nodes: $V(\mathcal P^\ell)=\{v^\ell_0,\dots,v^\ell_{d^p-1}\}$ and $E(\mathcal P^\ell)=\{(v^\ell_i,v^\ell_{i+1}) : 0\le i<d^p-1\}$.
--   2. **Tree.** There is a tree $\mathcal T$ of depth $p$ in which every nonleaf node has $d$ children. Its nodes at level $\ell\in\{0,\dots,p\}$ are $u^\ell_0,\dots,u^\ell_{d^\ell-1}$ from left to right, so $u^0_0$ is the root and $u^p_0,\dots,u^p_{d^p-1}$ are the $d^p$ leaves. The children of $u^\ell_i$ are $u^{\ell+1}_{di},\dots,u^{\ell+1}_{di+d-1}$.
--   3. **Spokes.** For every path $\ell$ and every $j$, the leaf $u^p_j$ is joined to the path node $v^\ell_j$.
--
--   The two special nodes are $s=u^p_0$ (the leftmost leaf, which will receive Alice's input $x$) and $r=u^p_{d^p-1}$ (the rightmost leaf, which will receive Bob's input $y$).
--
--   For $i\ge1$, the **$i$-left** and **$i$-right** sets are
--   $$L_i=\bigcup_\ell L_i(\mathcal P^\ell)\cup L_i(\mathcal T),\qquad R_i=\bigcup_\ell R_i(\mathcal P^\ell)\cup R_i(\mathcal T),$$
--   where $L_i(\mathcal P^\ell)=\{v^\ell_j : j\le d^p-1-i\}$, $R_i(\mathcal P^\ell)=\{v^\ell_j : j\ge i\}$, $L_i(\mathcal T)$ is the set of leaves $u^p_j$ with $j\le d^p-1-i$ together with all their ancestors, and $R_i(\mathcal T)$ is the set of leaves $u^p_j$ with $j\ge i$ together with all their ancestors. For $i=0$ the definition is modified: $L_0=V\setminus\{r\}$ and $R_0=V\setminus\{s\}$.
--
--   The sets $R_0\supseteq R_1\supseteq\cdots$ shrink towards $r$ by one path position per step, and $L_0\supseteq L_1\supseteq\cdots$ towards $s$; they are the bookkeeping device of the Simulation Theorem, where Bob tracks the states of $R_t$ and Alice those of $L_t$.
--
--   **Formalization Note** Paths are numbered $0,\dots,\Gamma-1$ (the paper uses $1,\dots,\Gamma$): `Sum.inl (ℓ, j)` is $v^{\ell+1}_j$ and `Sum.inr ⟨ℓ, i⟩` is $u^\ell_i$. The graph is `SimpleGraph.fromRel` of the path, tree and spoke relations, which symmetrizes it and removes loops. The ancestor of leaf $u^p_j$ at level $\ell$ is $u^\ell_{\lfloor j/d^{p-\ell}\rfloor}$, and the condition $j\le d^p-1-i$ is written $j+i<d^p$ to avoid natural-number subtraction. $L_i$ and $R_i$ are defined for every $i\in\mathbb N$; the paper defines them only for $0\le i\le\lfloor(d^p-1)/2\rfloor$, and every statement of the mission uses them only in that range. The nodes $s$ and $r$ take a proof of $0<d^p$, needed to name a leaf.
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), pp. 1247–1248, §3.1 (description of G(Γ,d,p)) and §3.2 (i-left and i-right sets, L_0 and R_0)

import Mathlib

namespace DistVerif.Simulation

/-- Vertices of `G(Γ, d, p)` (§3.1, p. 1247). `Sum.inl (ℓ, j)` is the path node `v^{ℓ+1}_j`
(paths are numbered `0, …, Γ - 1` here, `1, …, Γ` in the paper); `Sum.inr ⟨ℓ, i⟩` is the tree
node `u^ℓ_i` at level `ℓ ∈ {0, …, p}`, numbered `0, …, d^ℓ - 1` from left to right. -/
abbrev Vtx (Γ d p : ℕ) : Type :=
  (Fin Γ × Fin (d ^ p)) ⊕ (Σ ℓ : Fin (p + 1), Fin (d ^ (ℓ : ℕ)))

/-- The (non-symmetrized) edge relation of `G(Γ, d, p)`:
* path edges `v^ℓ_j — v^ℓ_{j+1}`;
* tree edges `u^ℓ_i — u^{ℓ+1}_j` with `j / d = i`, so the children of `u^ℓ_i` are
  `u^{ℓ+1}_{d·i+k}`, `0 ≤ k < d` (the left-to-right numbering);
* spoke edges `u^p_j — v^ℓ_j` for every path `ℓ` and every `j`. -/
def baseRel (Γ d p : ℕ) : Vtx Γ d p → Vtx Γ d p → Prop
  | Sum.inl (a, j), Sum.inl (a', j') => a = a' ∧ (j : ℕ) + 1 = j'
  | Sum.inr ⟨ℓ, i⟩, Sum.inr ⟨ℓ', j⟩ => (ℓ : ℕ) + 1 = ℓ' ∧ (j : ℕ) / d = i
  | Sum.inr ⟨ℓ, k⟩, Sum.inl (_, j) => (ℓ : ℕ) = p ∧ (k : ℕ) = j
  | Sum.inl _, Sum.inr _ => False

instance (Γ d p : ℕ) : DecidableRel (baseRel Γ d p) := fun v w => by
  rcases v with ⟨a, j⟩ | ⟨ℓ, i⟩ <;> rcases w with ⟨a', j'⟩ | ⟨ℓ', j'⟩ <;>
    unfold baseRel <;> infer_instance

/-- The network `G(Γ, d, p)` of §3.1 (p. 1247): `Γ` paths with `d^p` nodes each, a complete
`d`-ary tree of depth `p`, and a spoke from the `j`-th leaf to the `j`-th node of every path. -/
def graph (Γ d p : ℕ) : SimpleGraph (Vtx Γ d p) :=
  SimpleGraph.fromRel (baseRel Γ d p)

instance (Γ d p : ℕ) : DecidableRel (graph Γ d p).Adj := fun v w =>
  decidable_of_iff (v ≠ w ∧ (baseRel Γ d p v w ∨ baseRel Γ d p w v))
    (SimpleGraph.fromRel_adj (baseRel Γ d p) v w).symm

/-- The special node `s = u^p_0` (the leftmost leaf), which receives Alice's input `x`. -/
def sNode (Γ d p : ℕ) (hdp : 0 < d ^ p) : Vtx Γ d p :=
  Sum.inr ⟨Fin.last p, ⟨0, hdp⟩⟩

/-- The special node `r = u^p_{d^p - 1}` (the rightmost leaf), which receives Bob's input `y`. -/
def rNode (Γ d p : ℕ) (hdp : 0 < d ^ p) : Vtx Γ d p :=
  Sum.inr ⟨Fin.last p, ⟨d ^ p - 1, Nat.sub_lt hdp Nat.one_pos⟩⟩

/-- Membership in the `i`-left set `L_i` (§3.2, pp. 1247–1248).
For `i ≥ 1`: a path node `v^ℓ_j` lies in `L_i` iff `j ≤ d^p - 1 - i` (written `j + i < d^p`),
and a tree node `u^ℓ_k` lies in `L_i(T)` iff it is a leaf `u^p_j` with `j ≤ d^p - 1 - i` or an
ancestor of one; the ancestor of leaf `j` at level `ℓ` is `u^ℓ_{⌊j / d^{p-ℓ}⌋}`.
For `i = 0`: `L_0 = V \ {r}`, i.e. every vertex except the leaf `u^p_{d^p-1}`. -/
def InLeft (Γ d p i : ℕ) : Vtx Γ d p → Prop
  | Sum.inl (_, j) => i = 0 ∨ (j : ℕ) + i < d ^ p
  | Sum.inr ⟨ℓ, k⟩ =>
      if i = 0 then ¬ ((ℓ : ℕ) = p ∧ (k : ℕ) = d ^ p - 1)
      else ∃ j : Fin (d ^ p), (j : ℕ) + i < d ^ p ∧ (j : ℕ) / d ^ (p - ℓ) = k

/-- Membership in the `i`-right set `R_i` (§3.2, pp. 1247–1248).
For `i ≥ 1`: a path node `v^ℓ_j` lies in `R_i` iff `j ≥ i`, and a tree node lies in `R_i(T)`
iff it is a leaf `u^p_j` with `j ≥ i` or an ancestor of one.
For `i = 0`: `R_0 = V \ {s}`, i.e. every vertex except the leaf `u^p_0`. -/
def InRight (Γ d p i : ℕ) : Vtx Γ d p → Prop
  | Sum.inl (_, j) => i ≤ (j : ℕ)
  | Sum.inr ⟨ℓ, k⟩ =>
      if i = 0 then ¬ ((ℓ : ℕ) = p ∧ (k : ℕ) = 0)
      else ∃ j : Fin (d ^ p), i ≤ (j : ℕ) ∧ (j : ℕ) / d ^ (p - ℓ) = k

instance (Γ d p i : ℕ) : DecidablePred (InLeft Γ d p i) := fun v => by
  rcases v with ⟨a, j⟩ | ⟨ℓ, k⟩ <;> unfold InLeft <;> infer_instance

instance (Γ d p i : ℕ) : DecidablePred (InRight Γ d p i) := fun v => by
  rcases v with ⟨a, j⟩ | ⟨ℓ, k⟩ <;> unfold InRight <;> infer_instance

/-- The `i`-left set `L_i = ⋃_ℓ L_i(P^ℓ) ∪ L_i(T)` of `G(Γ, d, p)`, with `L_0 = V \ {r}`. -/
def L (Γ d p i : ℕ) : Finset (Vtx Γ d p) :=
  Finset.univ.filter (InLeft Γ d p i)

/-- The `i`-right set `R_i = ⋃_ℓ R_i(P^ℓ) ∪ R_i(T)` of `G(Γ, d, p)`, with `R_0 = V \ {s}`. -/
def R (Γ d p i : ℕ) : Finset (Vtx Γ d p) :=
  Finset.univ.filter (InRight Γ d p i)

end DistVerif.Simulation


