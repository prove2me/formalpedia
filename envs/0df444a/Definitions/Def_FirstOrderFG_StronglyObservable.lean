-- Prove2me | Definitions.Def_FirstOrderFG_StronglyObservable
-- name    : FirstOrderFG_StronglyObservable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:18.148217+00:00
-- url     : https://prove2.me/theorems/65ecc37c-b027-4d07-aadb-831ce7e6610d
-- title:
--   Strongly observable feedback graph
-- statement:
--   Throughout, $G=(V,E)$ is a directed graph on the arms $V=[K]$; the edge $i\to j$ means that playing arm $i$ reveals the loss of arm $j$.
--
--   The graph $G$ is **strongly observable** if every vertex either has a self-loop or is observed by every other vertex:
--   $$
--   \forall i\in V:\qquad i\to i\quad\text{or}\quad j\to i\ \text{ for every } j\neq i .
--   $$
--
--   This is the standing assumption of the paper; it covers prediction with expert advice (the complete graph with self-loops) and multi-armed bandits (self-loops only).
--
--   **Formalization Note** The graph is a relation `E : Fin K → Fin K → Prop`, with `E i j` the edge $i\to j$; arms are indexed $0,\dots,K-1$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3

import Mathlib

namespace FirstOrderFG

/-- **Strong observability.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3: "We assume that `G` is strongly observable in the
sense of [ACBDK15]: for every `i ∈ V`, either `i → i`, or `j → i` for every `j ≠ i`."

The graph is the edge relation `E : Fin K → Fin K → Prop` on the arms `V = [K]`.

**Formalization Note.** `E i j` is the edge `i → j`: playing arm `i` reveals the loss of arm `j`.
Arms are indexed `0, …, K-1` (`Fin K`) instead of `1, …, K`. -/
def StronglyObservable {K : ℕ} (E : Fin K → Fin K → Prop) : Prop :=
  ∀ i, E i i ∨ ∀ j, j ≠ i → E j i

end FirstOrderFG


