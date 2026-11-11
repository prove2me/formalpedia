-- Prove2me | Definitions.Def_SnarlSPQR_Snarls_GoodVertex
-- name    : SnarlSPQR_Snarls_GoodVertex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:29:58.804132+00:00
-- url     : https://prove2.me/theorems/a40fd974-00f1-40d7-82da-1efcde784f48
-- title:
--   Cyclic labellings of S-node skeletons, good vertices, and the slot sets E^α_u of P-nodes
-- statement:
--   Let $H$ be a block of the bidirected graph $G$, let $T$ be an SPQR tree of $U(H)$ (Q-nodes omitted) and let $\mu$ be an S-node of $T$.
--
--   A **cyclic labelling** of $\mathrm{skeleton}(\mu)$ lists its vertices $v_0,\dots,v_{k-1}$ and its edges $e_0,\dots,e_{k-1}$, each exactly once, so that $e_i$ has endpoints $v_i$ and $v_{(i+1)\bmod k}$.
--
--   With respect to such a labelling, $v_i$ is **good** when three conditions hold:
--   - the vertex-sides at $v_i$ in the expansion of the edge to its left, $e_{(i-1)\bmod k}$, all have one sign $\hat\alpha_i$;
--   - the vertex-sides at $v_i$ in the expansion of the edge to its right, $e_i$, all have the opposite sign $\alpha_i$;
--   - $v_i$ has no dangling block with respect to $H$.
--
--   For a node $\mu$ and a vertex $u$, the set $E^\gamma_u$ consists of the skeleton edges $e_i$ of $\mu$ with $N^\gamma_{\mathrm{expansion}(e_i)}(u)\ne\emptyset$ (Proposition 10).
--
--   **Formalization Note.** A labelling is given by $k$, a vertex map $v:\mathbb N\to V$ and a slot map $\sigma:\mathbb N\to\mathbb N$ (indices $<k$), with $\sigma$ a bijection onto the slots of $\mu$. `GoodWith … i α` records the right-hand sign $\alpha=\alpha_i$. `slotsWithSide H e T μ u γ` is $E^\gamma_u$ as a set of slot indices.
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 35, §5.4 (good vertices; Proposition 9) and p. 36 (the sets E^α_u of Proposition 10)

import Mathlib
import Definitions.Def_SnarlSPQR_Snarls_SPQRTree
import Definitions.Def_SnarlSPQR_Snarls_SignCut

open Classical

namespace SnarlSPQR.Snarls

/-!
# Cyclic labellings of S-node skeletons and good vertices (§5.4, p. 35)

Sena et al., arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), §5.4, p. 35 (the paragraph
"S-, P-, and R-nodes" and the statement of Proposition 9).

Let `H` be a block of the bidirected graph `G`, `T` an SPQR tree of `U(H)` with reference edge `e`
(Q-nodes omitted, `Def_SnarlSPQR_Snarls_SPQRTree`), and `μ` an S-node of `T`. A **cyclic
labelling** of `skeleton(μ)` lists its vertices `v₀, …, v_{k−1}` (each once, all of them) and its
edges `e₀, …, e_{k−1}` (each slot of `μ` once) so that the endpoints of `e_i` are `v_i` and
`v_{(i+1) mod k}`; here `v i` is a vertex and `σ i` the slot index of `e_i`, for `i < k`.

With respect to such a labelling, `v_i` is **good** if the vertex-sides at `v_i` in the expansion
of the edge to its left, `e_{(i−1) mod k}`, all have one sign `α̂`, those in the expansion of the
edge to its right, `e_i`, all have the opposite sign `α`, and `v_i` has no dangling block with
respect to `H` (in `G`). `GoodWith … i α` records the sign `α` of the right-hand edge, which is
the paper's `α_i` (and `α̂_i` the sign on the left), as in Proposition 9.
-/

namespace BiGraph

variable {V : Type*}

/-- A cyclic labelling of the skeleton of the node `μ`: vertices `v 0, …, v (k−1)` (injective, all
skeleton vertices) and slots `σ 0, …, σ (k−1)` (a bijection onto the slot indices of `μ`) with
the endpoints of slot `σ i` equal to `{v i, v ((i + 1) % k)}`. -/
def IsCycleLabel {E : Type*} (μ : Tree V E) (k : ℕ) (v : ℕ → V) (σ : ℕ → ℕ) : Prop :=
  (∀ i < k, ∀ j < k, v i = v j → i = j) ∧ (∀ x, x ∈ μ.skelVerts ↔ ∃ i < k, v i = x) ∧
    (∀ i < k, ∀ j < k, σ i = σ j → i = j) ∧
    (∀ m, m < μ.slots.length ↔ ∃ i < k, σ i = m) ∧
    ∀ i < k, μ.slots[σ i]? = some s(v i, v ((i + 1) % k))

/-- With respect to the cyclic labelling `(k, v, σ)` of the skeleton of the S-node `μ` of the
SPQR tree `T` (reference edge `e`) of the block `H` of `G`, the vertex `v i` is good with sign
`α`: all vertex-sides at `v i` in the expansion of `e_{(i−1) mod k}` have sign `α̂`, all those in
the expansion of `e_i` have sign `α`, and `v i` has no dangling block with respect to `H`. -/
def GoodWith (G H : BiGraph V) (e : Sym2 (V × Sign)) (T μ : Tree V (Sym2 (V × Sign)))
    (k : ℕ) (v : ℕ → V) (σ : ℕ → ℕ) (i : ℕ) (α : Sign) : Prop :=
  (edgeInduced (Tree.slotExp H.edges e T μ (σ ((i + k - 1) % k)))).AllSidesAt (v i) α.opp ∧
    (edgeInduced (Tree.slotExp H.edges e T μ (σ i))).AllSidesAt (v i) α ∧
    ¬ G.HasDangling H (v i)

/-- `v i` is a good vertex of the S-node `μ` (for the labelling `(k, v, σ)`). -/
def IsGood (G H : BiGraph V) (e : Sym2 (V × Sign)) (T μ : Tree V (Sym2 (V × Sign)))
    (k : ℕ) (v : ℕ → V) (σ : ℕ → ℕ) (i : ℕ) : Prop :=
  i < k ∧ ∃ α, G.GoodWith H e T μ k v σ i α

/-- For the node `μ` of the SPQR tree `T` (reference edge `e`) of `H`, the set of slots `i` of
`skeleton(μ)` with `N^γ_{expansion(e_i)}(u) ≠ ∅` (the sets `E^α_u` of Proposition 10, p. 36). -/
noncomputable def slotsWithSide (H : BiGraph V) (e : Sym2 (V × Sign))
    (T μ : Tree V (Sym2 (V × Sign))) (u : V) (γ : Sign) : Finset ℕ :=
  (Finset.range μ.slots.length).filter fun i =>
    ((edgeInduced (Tree.slotExp H.edges e T μ i)).nbr γ u).Nonempty

end BiGraph

end SnarlSPQR.Snarls


