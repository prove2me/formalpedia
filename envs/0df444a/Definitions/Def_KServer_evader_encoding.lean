-- Prove2me | Definitions.Def_KServer_evader_encoding
-- name    : KServer_evader_encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T08:40:15.44205+00:00
-- url     : https://prove2.me/theorems/1a819ed4-5b27-40ab-ac59-a7502412a8c3
-- title:
--   The k-server encoding of evader request sequences
-- statement:
--   The **k-server encoding** of an evader (metrical service systems) request sequence on a finite space $M$: a set request $S \subseteq M$ becomes $R$ consecutive *passes*, each pass requesting every point of $M \setminus S$ once (in a fixed ambient enumeration order); a sequence of set requests is encoded block by block (`encSeq`).
--
--   On a space with $k+1$ points, a lazy simple $k$-server algorithm leaves exactly one point — the *hole* — uncovered. During a pass, requests away from the hole are free no-ops, while requesting the hole forces it to move; if after a block of $R$ passes the hole has still not entered $S$, the algorithm has been hit at least once per pass and has paid at least $R$ times the minimum distance. Choosing $R$ of the order of (diameter / minimum distance) therefore forces the hole into $S$ or makes the block pay for a full teleport. This is the mechanism of the folklore reduction $C^{\mathrm{kSRV}}(\mathcal{M}) \ge C^{\mathrm{MSS}}(\mathcal{M})$ for $|\mathcal M| = k+1$ used by Bubeck–Coester–Rabani (STOC 2023, Proposition 2.6).
--
--   Accompanying lemmas: membership in a pass is exactly non-membership in the request (`mem_encBlock`), and the encoding is a monoid homomorphism on sequences (`encSeq_nil`, `encSeq_append`, `encSeq_singleton`).
--
--   ## Formalization note
--
--   `encBlock` uses the classical decidability of set membership and a `Finset.filter`; the pass order is the ambient `Finset.toList` enumeration, which is irrelevant to the bounds.
-- source:
--   Folklore; as in S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Proposition 2.6.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader

namespace KServer

/-- One **pass** of the k-server encoding of an evader (MSS) request: the list of
all points outside the requested set, in the ambient enumeration order. -/
noncomputable def encBlock (M : Type*) [Fintype M] (S : Set M) : List M :=
  letI := Classical.decPred (· ∈ S)
  (Finset.univ.filter (· ∉ S)).toList

/-- The k-server encoding of an evader request sequence: each set request becomes
`R` consecutive passes through the complement of the set. -/
noncomputable def encSeq (M : Type*) [Fintype M] (R : ℕ) (σ : List (Set M)) : List M :=
  σ.flatMap fun S => (List.replicate R (encBlock M S)).flatten

theorem mem_encBlock {M : Type*} [Fintype M] (S : Set M) (r : M) :
    r ∈ encBlock M S ↔ r ∉ S := by
  classical
  unfold encBlock
  rw [Finset.mem_toList]
  simp

theorem encSeq_nil (M : Type*) [Fintype M] (R : ℕ) : encSeq M R [] = [] := rfl

theorem encSeq_append (M : Type*) [Fintype M] (R : ℕ) (σ τ : List (Set M)) :
    encSeq M R (σ ++ τ) = encSeq M R σ ++ encSeq M R τ := by
  unfold encSeq
  rw [List.flatMap_append]

theorem encSeq_singleton (M : Type*) [Fintype M] (R : ℕ) (S : Set M) :
    encSeq M R [S] = (List.replicate R (encBlock M S)).flatten := by
  unfold encSeq
  simp

end KServer


