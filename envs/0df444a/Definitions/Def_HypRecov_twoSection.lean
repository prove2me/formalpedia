-- Prove2me | Definitions.Def_HypRecov_twoSection
-- name    : HypRecov_twoSection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:48.245187+00:00
-- url     : https://prove2.me/theorems/4d416581-a973-46e7-be78-fb76525c87d9
-- title:
--   The two-section $G(J)$ of a hypergraph
-- statement:
--   For a hypergraph $J$ on $V$, its **two-section** $G(J)$ is the simple graph on $V$ in which two distinct vertices are adjacent exactly when some edge of $J$ contains both. Thus $G(H)$ is the support graph of the counted pair projection. The mission also uses it to express connectivity of a hypergraph: two vertices lie in the same connected component of $J$ exactly when they are joined by a path in $G(J)$.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §2, p.5 (PDF p.6)

import Mathlib

namespace HypRecov

/-- **The two-section `G(J)`.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection
Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), §2, p.5 (PDF p.6): "For a hypergraph J,
its two-section G(J) is the simple graph on V(J) in which two distinct vertices are adjacent exactly
when some hyperedge contains both."

**Formalization Note.** Vertices are `Fin n`; edges of `J` of size below two add no adjacency. -/
def twoSection {n : ℕ} (J : Finset (Finset (Fin n))) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ e ∈ J, u ∈ e ∧ v ∈ e
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim fun e he => ⟨e, he.1, he.2.2, he.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n : ℕ} (J : Finset (Finset (Fin n))) : DecidableRel (twoSection J).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ ∃ e ∈ J, u ∈ e ∧ v ∈ e))

end HypRecov


