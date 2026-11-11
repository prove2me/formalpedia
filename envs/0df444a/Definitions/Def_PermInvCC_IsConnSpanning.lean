-- Prove2me | Definitions.Def_PermInvCC_IsConnSpanning
-- name    : PermInvCC_IsConnSpanning
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:17.922198+00:00
-- url     : https://prove2.me/theorems/de6a5787-e6a3-4884-8db3-e126e6f93e9b
-- title:
--   Connected spanning subgraphs on the active symbols
-- statement:
--   A row or column symbol is **active** if its margin is positive. A set $G$ of cells is a **connected spanning bipartite subgraph on the active symbols** of margins $\rho,\sigma$ if each cell of $G$ joins an active row symbol to an active column symbol and the graph with edges $G$ on the active symbols is connected.
--
--   It is the hypothesis of Lemmas 4.3 and B.2: only these cells need large counts.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), p.15 and Lemmas 4.3, B.2

import Mathlib
import Definitions.Def_PermInvCC_symbolGraph

namespace PermInvCC

/-- `G` is a **connected spanning bipartite subgraph on the active symbols** of the margins
`ρ, σ` (Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, p.15: "A row or
column symbol is active if its corresponding margin is positive"; Lemmas 4.3 and B.2): every cell
of `G` joins an active row symbol to an active column symbol, and the graph with edges `G`,
restricted to the active symbols, is connected (so every active symbol is covered when there are
active symbols on both sides). -/
def IsConnSpanning {q : ℕ} (ρ σ : Fin q → ℕ) (G : Finset (Fin q × Fin q)) : Prop :=
  (∀ e ∈ G, 0 < ρ e.1 ∧ 0 < σ e.2) ∧
    ((symbolGraph G).induce {u | Sum.elim (fun a => 0 < ρ a) (fun b => 0 < σ b) u}).Connected

end PermInvCC


