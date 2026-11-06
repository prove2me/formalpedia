-- Prove2me | Definitions.Def_AuctionMatroidInt_Loopless
-- name    : AuctionMatroidInt_Loopless
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:17.803392+00:00
-- url     : https://prove2.me/theorems/ae23d1b9-3816-4057-bd9b-911a8c29722e
-- title:
--   Matroid without loops
-- statement:
--   For a matroid $M=(E,\mathcal I)$, an element $e\in E$ is a **loop** if $\{e\}\notin\mathcal I$. The matroid is **loopless** if it has no loop, that is, $\{e\}\in\mathcal I$ for every $e\in E$.
--
--   Throughout the paper both matroids are assumed loopless without loss of generality (loops can be removed). Looplessness guarantees that the fundamental circuit $C_2(X\mid e)$ contains an element other than $e$, so that the minimum in the price definition (1) is over a nonempty set.
--
--   **Formalization Note** The ground set is the whole type `α`.
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), §2.1, p.10 (PDF p.12)

import Mathlib

namespace AuctionMatroidInt

/-- **Matroid without loops.**
Huang, Kobayashi, Terao (manuscript, sha256 2e12cb4a…), §2.1, p.10: "An element e ∈ E is called
a loop if {e} ∉ I." `Loopless I` says that no element of the ground set `α` is a loop.

**Formalization Note.** The ground set is the whole type `α`; the family of independent sets is
the predicate `I : Finset α → Prop`. -/
def Loopless {α : Type*} (I : Finset α → Prop) : Prop :=
  ∀ e : α, I {e}

end AuctionMatroidInt


