-- Prove2me | Definitions.Def_HypRecov_auxGraph
-- name    : HypRecov_auxGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:11.3156+00:00
-- url     : https://prove2.me/theorems/c27f3ee7-217f-4181-98e2-16a85b88c621
-- title:
--   The proof-only graph $A_Q$ of Lemma 6.1
-- statement:
--   For a component $L$ of $G-R$ and $Q=L\cup R$, the graph $A_Q$ on $Q$ joins two distinct vertices of $Q$ if
--
--   1. they lie in the same current block, or
--   2. at least one of them lies in $L$ and their residual codegree is at least $M$.
--
--   The item is a graph on all of $V$ with no edge leaving $Q$; Lemma 6.1 concerns its subgraph induced on $Q$.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 6.1, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_HypRecov_envelope

namespace HypRecov

/-- **The proof-only graph `A_Q`.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection
Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 6.1, p.13 (PDF p.14): "Set
Q = L ∪ R. On Q, define the proof-only graph A_Q by including: 1. all current-block clique edges
restricted to Q. 2. every pair with at least one endpoint in L whose true residual codegree is at
least M."

`auxGraph J P M L Q` is a graph on `Fin n` with no edge leaving `Q`; Lemma 6.1 concerns its induced
subgraph on `Q`. -/
def auxGraph {n : ℕ} (J : Finset (Finset (Fin n))) (P : Fin n → Fin n) (M : ℕ)
    (L Q : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u ∈ Q ∧ v ∈ Q ∧ (P u = P v ∨ ((u ∈ L ∨ v ∈ L) ∧ M ≤ codeg J u v))
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.elim (fun h' => Or.inl h'.symm)
    (fun h' => Or.inr ⟨h'.1.symm, by unfold codeg at h' ⊢; simpa only [and_comm] using h'.2⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end HypRecov


