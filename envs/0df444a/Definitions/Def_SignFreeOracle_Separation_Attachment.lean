-- Prove2me | Definitions.Def_SignFreeOracle_Separation_Attachment
-- name    : SignFreeOracle_Separation_Attachment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:41.242493+00:00
-- url     : https://prove2.me/theorems/7466e427-c24a-4d51-9125-27cbbb170e6d
-- title:
--   The full boundary-preserving attachment graph
-- statement:
--   For a closed base set $S$, the attachment graph has its original induced base edges, $K$ copies of $\widehat T_{n,k}$ per vertex for $1\le k<K$, and one copy of $\widehat T_{n,K}$ for every base edge leaving $S$. Copies use dependent disjoint unions of their actual finite vertex sets, and each receives one edge from its root to its owning base vertex. Its distinguished boundary consists exactly of the 0-level leaves in the depth-$K$ copies:
--   $$\partial_{\rm att}S=\bigcup_{\substack{u\in S,\ v\notin S\\uv\in E(B)}}\{\text{0-level leaves of the copy indexed by }(u,v)\}.$$
--   This supplies a concrete isomorphism target for all of Proposition 4.1, including disjoint branches and the boundary bijection. No isomorphism, forest property or spectral bound is assumed in the construction.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Proposition 4.1 and its proof, p. 13 (PDF p. 13)

import Definitions.Def_SignFreeOracle_Separation_Family

set_option autoImplicit false

namespace SignFreeOracle.Separation

/-- Fresh branch indices: smaller decorations, and one depth-K branch for each base edge
leaving the closure. This dependent disjoint union keeps every copy disjoint. -/
def ClosureBranch (n NB : ℕ) (B : SimpleGraph (Fin NB))
    (S : Set (Fin NB)) (u : S) : Type :=
  (Fin (Nat.sqrt n - 1) × Fin (Nat.sqrt n)) ⊕ {v : Fin NB // B.Adj u.val v ∧ v ∉ S}

noncomputable def branchShape (n NB : ℕ) (B : SimpleGraph (Fin NB))
    (S : Set (Fin NB)) (u : S) : ClosureBranch n NB B S u → TreeShape
  | .inl kc => selfSimilar n (kc.1.val + 1)
  | .inr _ => selfSimilar n (Nat.sqrt n)

/-- The graph obtained by the actual attachments asserted in Proposition 4.1. -/
def AttachedVertex (n NB : ℕ) (B : SimpleGraph (Fin NB)) (S : Set (Fin NB)) : Type :=
  S ⊕ (Σ u : S, Σ b : ClosureBranch n NB B S u, Fin (branchShape n NB B S u b).size)

noncomputable def attachmentEdge (n NB : ℕ) (B : SimpleGraph (Fin NB)) (S : Set (Fin NB))
    (x y : AttachedVertex n NB B S) : Prop :=
  (∃ u v : S, x = .inl u ∧ y = .inl v ∧ B.Adj u.val v.val) ∨
  (∃ (u : S) (b : ClosureBranch n NB B S u) (i : Fin (branchShape n NB B S u b).size),
    x = .inl u ∧ y = .inr ⟨u, b, i⟩ ∧ i.val = 0) ∨
  (∃ (u : S) (b : ClosureBranch n NB B S u)
      (i j : Fin (branchShape n NB B S u b).size),
    x = .inr ⟨u, b, i⟩ ∧ y = .inr ⟨u, b, j⟩ ∧ (treeGraph (branchShape n NB B S u b)).Adj i j)

noncomputable def attachedGraph (n NB : ℕ) (B : SimpleGraph (Fin NB)) (S : Set (Fin NB)) :
    SimpleGraph (AttachedVertex n NB B S) where
  Adj x y := x ≠ y ∧ (attachmentEdge n NB B S x y ∨ attachmentEdge n NB B S y x)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

noncomputable def AttachedBoundary (n NB : ℕ) (B : SimpleGraph (Fin NB)) (S : Set (Fin NB))
    (x : AttachedVertex n NB B S) : Prop :=
  ∃ (u : S) (v : {v : Fin NB // B.Adj u.val v ∧ v ∉ S})
    (i : Fin (branchShape n NB B S u (.inr v)).size),
    x = .inr ⟨u, .inr v, i⟩ ∧ i.val ∈ (selfSimilar n (Nat.sqrt n)).marked

end SignFreeOracle.Separation


