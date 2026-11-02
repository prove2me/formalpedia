-- Prove2me | Definitions.Def_OpenSearchLivenessAbstract
-- name    : OpenSearchLivenessAbstract
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-01T18:51:43.192203+00:00
-- url     : https://prove2.me/theorems/a7c4dc2e-f14c-4edc-8dc8-007be6eb0844
-- title:
--   Generalized election-timer round: fire times and uncontested rounds for arbitrary delays
-- statement:
--   For a round of an election-timer competition, each candidate $i$ has an integer offset and a delay function over all $2^{64}$ draws. The fire time of candidate $i$ on draw $x$ is its offset plus its delay for $x_i$. A round is uncontested with margin $\delta$ when some candidate fires at least $\delta$ before every other candidate.
-- source:
--   OpenSearch cluster coordination, pinned revision b2a54ba5c0defba3d1d20423e911d4bf920bab19 (org.opensearch.cluster.coordination); liveness/timer gap-closure analysis, new theorems mechanized from the branch's OpenSearchCoordination/OpenSearchPreVote/OpenSearchSafety/OpenSearchProgress missions.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

namespace OpenSearchLivenessAbstract

/-- Fire time of candidate `i`: its offset plus its delay for draw `x i`. -/
def fireTime {n : Nat} (offset : Fin n → Int) (delay : Fin n → Fin (2 ^ 64) → Int)
    (x : Fin n → Fin (2 ^ 64)) (i : Fin n) : Int :=
  offset i + delay i (x i)

/-- A round is uncontested with margin `δ`: some candidate fires at least `δ`
before every other candidate. -/
def Uncontested {n : Nat} (offset : Fin n → Int) (delay : Fin n → Fin (2 ^ 64) → Int)
    (δ : Nat) (x : Fin n → Fin (2 ^ 64)) : Prop :=
  ∃ i, ∀ j, j ≠ i → fireTime offset delay x i + δ ≤ fireTime offset delay x j

instance {n : Nat} (offset : Fin n → Int) (delay : Fin n → Fin (2 ^ 64) → Int)
    (δ : Nat) : DecidablePred (Uncontested offset delay δ) := fun x => by
  unfold Uncontested; infer_instance

end OpenSearchLivenessAbstract


