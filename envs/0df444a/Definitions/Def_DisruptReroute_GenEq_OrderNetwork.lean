-- Prove2me | Definitions.Def_DisruptReroute_GenEq_OrderNetwork
-- name    : DisruptReroute_GenEq_OrderNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:04.759948+00:00
-- url     : https://prove2.me/theorems/483c9085-69df-49ca-87fc-b95e67e7a420
-- title:
--   §2, pp. 8–9 — finite multi-good order network
-- statement:
--   A finite **order network** has a set of firms and a set of goods. For each good $m$ and pair of firms $i,j$, the real number $o^m_{ij}$ is the quantity that firm $i$ commits to deliver to firm $j$.
--
--   This order array is the shared network skeleton on which the paper's prices, stocks, costs, market functions, and default dynamics are built.
--
--   **Formalization Note** Firms and goods are indexed by `Fin N` and `Fin M`, starting at zero; the paper indexes them from one. Nonnegativity and nonempty index sets are imposed by `Standing` in the model definition.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), pp. 8–9, supply chain network definition

import Mathlib

namespace DisruptReroute.GenEq

/-- A finite directed multi-good order network. `o m i j` is the amount
    that firm `i` promises to deliver to firm `j`. -/
structure OrderNetwork (N M : ℕ) where
  o : Fin M → Fin N → Fin N → ℝ

end DisruptReroute.GenEq


