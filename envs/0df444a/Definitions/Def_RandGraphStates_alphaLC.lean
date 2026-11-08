-- Prove2me | Definitions.Def_RandGraphStates_alphaLC
-- name    : RandGraphStates_alphaLC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:35.657037+00:00
-- url     : https://prove2.me/theorems/8086bdf4-ee7f-48ec-ae90-5fff4f979c0f
-- title:
--   Local complementation $G\star v$, LC-equivalence, and $\alpha_{\mathrm{LC}}(G)$
-- statement:
--   For a graph $G$ and a vertex $v$, the **local complementation** $G\star v$ is obtained from $G$ by complementing the subgraph induced on the neighbourhood $N(v)$: a pair $\{a,b\}$ with $a\neq b$ changes its adjacency exactly when $a,b\in N(v)$, and every other pair is unchanged. Two graphs on the same vertex set are **LC-equivalent**, $G\equiv_{\mathrm{LC}}H$, if there is a sequence of vertices $v_1,\dots,v_t$ with
--   $$
--   H=G\star v_1\star\cdots\star v_t .
--   $$
--   The independence number up to local complementation is
--   $$
--   \alpha_{\mathrm{LC}}(G):=\max\{\alpha(H):H\equiv_{\mathrm{LC}}G\}.
--   $$
--   This is the graph parameter the mission bounds for random graphs; for a graph state, $n-\alpha_{\mathrm{LC}}(G)$ is the Pauli persistency.
--
--   **Formalization Note** The sequence is a list and the composite is its left fold; the empty list is allowed. The maximum is a supremum in $\mathbb N$; on a finite vertex set the family is nonempty and bounded by the number of vertices, so the supremum is attained.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §2.1, p.4, and §2.2, p.5

import Mathlib

set_option autoImplicit false

namespace RandGraphStates

variable {V : Type*}

/-- Local complementation `G ⋆ v`: the graph obtained from `G` by complementing the induced
subgraph on `N(v)`. A pair `{a, b}`, `a ≠ b`, flips exactly when `a, b ∈ N(v)`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), §2.1, p.4. -/
def localComplement (G : SimpleGraph V) (v : V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ Xor (G.Adj a b) (G.Adj v a ∧ G.Adj v b)
  symm := ⟨fun a b h => by
    refine ⟨h.1.symm, ?_⟩
    rw [G.adj_comm b a, and_comm (a := G.Adj v b)]
    exact h.2⟩
  loopless := ⟨fun a h => h.1 rfl⟩

/-- `G ≡LC H`: there is a sequence of vertices `v₁, …, v_t` with `H = G ⋆ v₁ ⋆ ⋯ ⋆ v_t`.

Source: ibid., §2.1, p.4.

**Formalization Note.** The left fold is the sequence of local complementations, in order; the
empty sequence is allowed, and it adds nothing on a nonempty vertex set since `G ⋆ v ⋆ v = G`. -/
def LCEquiv (G H : SimpleGraph V) : Prop :=
  ∃ vs : List V, H = vs.foldl localComplement G

/-- `αLC(G) := max{α(H) : H is LC-equivalent to G}`, the independence number up to local
complementation.

Source: ibid., §2.2, p.5.

**Formalization Note.** A supremum in `ℕ`. On a finite vertex set the family is nonempty (it
contains `α(G)`) and bounded by the number of vertices, so the supremum is the printed maximum;
`Solutions/verification/RandGraphStates_Sanity.lean` proves it. -/
noncomputable def alphaLC (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ H : SimpleGraph V, LCEquiv G H ∧ k = H.indepNum}

end RandGraphStates


