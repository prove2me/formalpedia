-- Prove2me | Definitions.Def_MonDepMW_IsPredampingSet
-- name    : MonDepMW_IsPredampingSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:23.464486+00:00
-- url     : https://prove2.me/theorems/7afa4212-643e-4931-8a0a-6368b451bdd3
-- title:
--   Assertions (A1)–(A3) of the Predamping Lemma
-- statement:
--   A set $S$ satisfies the predamping assertions for $\mathcal P,A,q,\alpha,\beta,\gamma$ if:
--
--   1. (A1) $|S|\leqslant|A|/q$;
--   2. (A2) for every $u$ there is $s_u\in S$ with $\mathrm{ham}_{\mathcal P(G,A\cup S)}(u,s_u)\leqslant15(q+1)\beta\gamma$;
--   3. (A3) any two vertices $u,v$ of the same 1-type over $S$ have $\mathrm{ham}_{\mathcal P(G,A\cup S)}(u,v)\leqslant44(q+1)\alpha\gamma$.
--
--   It is the conclusion of Lemma 6.1, stated once for its existence and algorithmic clauses.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §6, p.23, Lemma 6.1

import Mathlib
import Definitions.Def_MonDepMW_oneType
import Definitions.Def_MonDepMW_closedSymmDiff
import Definitions.Def_MonDepMW_PartitionSelector

set_option autoImplicit false

namespace MonDepMW

/-- **Assertions (A1)–(A3) of the Predamping Lemma.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 6.1, p.23: "(A1) |S| ⩽ |A|/q; (A2) for every u ∈ V (G)
there exists s_u ∈ S such that ham_{𝒫(G,A∪S)}(u, s_u) ⩽ 15(q + 1) · βγ; and (A3) for any two vertices u, v ∈ V (G)
belonging to the same 1-type over S, we have ham_{𝒫(G,A∪S)}(u, v) ⩽ 44(q + 1) · αγ."

**Formalization Note.** Every use carries `1 ≤ q`, so the division is genuine. -/
structure IsPredampingSet (𝔓 : PartitionSelector) {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (q α β γ : ℕ) (S : Finset (Fin n)) : Prop where
  A1 : (S.card : ℝ) ≤ (A.card : ℝ) / (q : ℝ)
  A2 : ∀ u, ∃ s ∈ S, ham G (𝔓 n G (A ∪ S)) u s ≤ 15 * (q + 1) * (β * γ)
  A3 : ∀ u v, (oneType G S).r u v → ham G (𝔓 n G (A ∪ S)) u v ≤ 44 * (q + 1) * (α * γ)

end MonDepMW


