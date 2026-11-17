-- Prove2me | Definitions.Def_EulerianLE_Supplement_IsLEAlgorithm
-- name    : EulerianLE_Supplement_IsLEAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:00.09882+00:00
-- url     : https://prove2.me/theorems/392d27f8-7b4f-4a58-80d4-ba250ac3f1fa
-- title:
--   Content-oblivious leader-election algorithms for identifiers in $[K]$
-- statement:
--   A deterministic content-oblivious algorithm is a family $A$ of node programs: $A(\mathrm{id},d)$ is the program run by a node with identifier $\mathrm{id}$ and degree $d$, and a program sees the network only through the outcomes of queue tests on its ports (pulses carry no content).
--
--   $A$ is a **leader-election algorithm for identifiers in $[K]=\{1,\dots,K\}$** when, for every simple 2-edge-connected network $H$ and every assignment of distinct identifiers from $[K]$ to the nodes of $H$,
--
--   1. some standalone execution (fair run) of $A$ on $H$ exists, and
--   2. in every standalone execution, every node completes; exactly one node $\ell$ outputs `leader` and every other node outputs `nonLeader`.
--
--   This is the class of algorithms the lower bound (Theorem 18) speaks about. Since the identifiers are distinct and lie in $[K]$, such networks have at most $K$ nodes, so the class contains the non-uniform algorithms of Chalopin, Chang, Chen, Di Luna and Zhou (2025) run with the node bound $N=K$; uniform algorithms are the families that do not depend on $K$.
--
--   **Formalization Note** Quiescence and the leader terminating last are not required. Executions, fairness and completion are the mission's published model (`Run`, `IsFair`, `CompletesWith`); outputs are the published `Outcome`.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §2, p.7 (PDF p.9); §6, pp.26–28 (PDF pp.28–30), proof of Lemma 17

import Mathlib
import Definitions.Def_EulerianLE_Supplement_IsTwoEdgeConnected
import Definitions.Def_EulerianLE_Run
import Definitions.Def_EulerianLE_program1

namespace EulerianLE.Supplement

/-- A content-oblivious **leader-election algorithm for identifiers in `[K]`** on 2-edge-connected
networks (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*,
STOC 2027 submission (manuscript sha256 90954a93…), §2, p.7, PDF p.9 and §6, pp.26–28, PDF pp.28–30).

`A id d` is the program that a node with identifier `id` and degree `d` runs ("initial states depend
only on a node's identifier and degree", proof of Lemma 17, p.28). `A` is a leader-election algorithm
for identifiers in `[K] = {1, …, K}` when, on every simple 2-edge-connected network `H` and for every
assignment of distinct identifiers from `[K]` to its nodes,

1. some standalone execution (fair run) exists, and
2. in every standalone execution every node completes, one node `ℓ` with output `leader` and every
   other node with output `nonLeader`.

**Formalization Note.** Quiescence and the leader terminating last are not required: they are
properties of the paper's own algorithm, not of the algorithms the lower bound speaks about. Clause 1
rules out a vacuous clause 2. Since the identifiers are distinct and lie in `[K]`, every such network
has at most `K` nodes. -/
def IsLEAlgorithm (K : ℕ) (A : ℕ → (d : ℕ) → NodeProg d Outcome) : Prop :=
  ∀ H : Network, IsSimpleNet H → IsTwoEdgeConnected H →
    ∀ ids : H.V → ℕ, Function.Injective ids → (∀ v, ids v ∈ Finset.Icc 1 K) →
      (∃ ρ : Run (fun v => A (ids v) (H.deg v)) (stdTag _), IsFair ρ) ∧
      ∀ ρ : Run (fun v => A (ids v) (H.deg v)) (stdTag _), IsFair ρ →
        ∃ ℓ : H.V, ∀ v, ρ.CompletesWith v (if v = ℓ then .leader else .nonLeader)

end EulerianLE.Supplement


