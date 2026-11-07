-- Prove2me | Definitions.Def_MonoTestDAG_bipDAG
-- name    : MonoTestDAG_bipDAG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:41.731204+00:00
-- url     : https://prove2.me/theorems/82c56bc5-7d6c-4803-b6e5-e062380f0831
-- title:
--   The bipartite DAG $P(U)$ and positive matchings
-- statement:
--   For an undirected bipartite graph $U=(L,R;E)$, $P(U)$ is the DAG on $L\sqcup R$ obtained by orienting every edge from $L$ to $R$. A matching $M\subseteq E$ is **positive** if some weight function $w:L\sqcup R\to\mathbb R$ satisfies, for every edge $e=\{\ell,r\}\in E$,
--   $$
--   w(\ell)+w(r)>0\iff e\in M.
--   $$
--
--   **Formalization Note.** Definition 2.1 is stated for any undirected graph; every use in this mission is for a bipartite $U$, which is the case encoded. Matchings are the published `OAI.SeymourSecondNeighborhood.Bipartite.IsMatching`. The module also defines `IsPosWeight` and `IsPositiveMatching`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §4.1, p.16 and Definition 2.1, p.10

import Mathlib
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching

namespace MonoTestDAG

/-- The bipartite DAG `G = P(U)` of an undirected bipartite graph `U = (L, R; E)`: vertex set
`L ⊔ R`, and every edge `(ℓ, r) ∈ E` oriented from `ℓ ∈ L` to `r ∈ R`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §4.1, p.16.

**Formalization Note.** `E` is a finite set of pairs `(ℓ, r) ∈ L × R`. -/
def bipDAG {L R : Type} (EU : Finset (L × R)) : L ⊕ R → L ⊕ R → Prop
  | .inl l, .inr r => (l, r) ∈ EU
  | _, _ => False

/-- `w : L ⊔ R → ℝ` certifies positivity of `M` in `U`: for every edge `e = {ℓ, r}` of `U`,
`w(ℓ) + w(r) > 0 ⟺ e ∈ M`. -/
def IsPosWeight {L R : Type} (EU M : Finset (L × R)) (w : L ⊕ R → ℝ) : Prop :=
  ∀ e ∈ EU, (0 < w (.inl e.1) + w (.inr e.2) ↔ e ∈ M)

/-- **Definition 2.1 (positive matching [18]),** for the bipartite graph `Γ = U = (L, R; E)`:
a matching `M ⊆ E` is positive if some weight function `w : L ⊔ R → ℝ` satisfies, for every edge
`e = {u, v} ∈ E`, `w(u) + w(v) > 0 ⟺ e ∈ M`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Definition 2.1, p.10.

**Formalization Note.** The paper states Definition 2.1 for any undirected graph `Γ`; every use in
the paper is for a bipartite `U`, which is the case encoded here. "Matching in `E`" is the
published `OAI.SeymourSecondNeighborhood.Bipartite.IsMatching`: a finite set of edges of `E` no
two of which share a left or a right endpoint. -/
def IsPositiveMatching {L R : Type} (EU M : Finset (L × R)) : Prop :=
  OAI.SeymourSecondNeighborhood.Bipartite.IsMatching (fun l r => (l, r) ∈ EU) M ∧
    ∃ w : L ⊕ R → ℝ, IsPosWeight EU M w

end MonoTestDAG


