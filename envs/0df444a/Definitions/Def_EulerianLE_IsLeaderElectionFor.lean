-- Prove2me | Definitions.Def_EulerianLE_IsLeaderElectionFor
-- name    : EulerianLE_IsLeaderElectionFor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:45.568211+00:00
-- url     : https://prove2.me/theorems/977cd1a3-feef-4bef-ab0e-9ab4b2807b04
-- title:
--   Quiescent leader election with the leader terminating last
-- statement:
--   Programs $P$ (one per node, with output Leader or Non-Leader) **solve leader election on $G$** in the sense of Theorem 1 when:
--
--   1. a standalone execution (fair run) exists;
--   2. in every fair run there is a node $\ell$ such that every node completes, $\ell$ with output Leader and every other node with output Non-Leader;
--   3. the run is quiescent: every pulse sent to a node is consumed before that node completes;
--   4. every node other than $\ell$ completes strictly before $\ell$.
--
--   These are the conclusions of Theorem 1 other than the pulse count, which the theorem states separately.
--
--   **Formalization Note** Clause 1 prevents a vacuous "for every fair run".
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §1.1, pp.1–2 (PDF pp.3–4), Theorem 1 and footnote 1

import Mathlib
import Definitions.Def_EulerianLE_program1

namespace EulerianLE

/-- The programs `P` solve leader election on `G` in the sense of Theorem 1 (Frei, Gelles, Ghazy,
Nolin, STOC 2027 submission (manuscript sha256 90954a93…), pp.1–2), except for the pulse count,
which Theorem 1 states separately:

1. a standalone execution exists (some fair run);
2. in every standalone execution (fair run) there is a node `ℓ` such that every node completes,
   `ℓ` with output `leader` and every other node with output `nonLeader` ("elects a unique leader");
3. the execution is quiescent: every pulse sent to a node is consumed before that node completes
   ("The algorithm quiescently terminates", footnote 1, p.2);
4. every other node completes strictly before `ℓ` ("the elected leader is the last node to
   terminate").

**Formalization Note.** Clause 1 rules out a vacuous "for every fair run": gated scheduler events
could otherwise be blocked forever by a node that computes forever. -/
def IsLeaderElectionFor (G : Network) (P : ∀ v, NodeProg (G.deg v) Outcome) : Prop :=
  (∃ ρ : Run P (stdTag P), IsFair ρ) ∧
  ∀ ρ : Run P (stdTag P), IsFair ρ → ∃ ℓ : G.V,
    (∀ v, ρ.CompletesWith v (if v = ℓ then .leader else .nonLeader)) ∧
    ρ.Quiescent ∧
    ∀ w, w ≠ ℓ → ∀ tw tℓ, ρ.CompletesAt w tw → ρ.CompletesAt ℓ tℓ → tw < tℓ

end EulerianLE


