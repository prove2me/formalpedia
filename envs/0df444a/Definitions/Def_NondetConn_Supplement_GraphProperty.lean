-- Prove2me | Definitions.Def_NondetConn_Supplement_GraphProperty
-- name    : NondetConn_Supplement_GraphProperty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:09:27.427291+00:00
-- url     : https://prove2.me/theorems/ca23f87f-9139-45e6-a2d0-c2000cba0a39
-- title:
--   The five graph properties of Theorem 6.2
-- statement:
--   Theorem 6.2 treats five graph-decision properties in one result: **bipartite**, **cycle-free**, **Eulerian**, **Hamiltonian**, and **planar**.
--
--   This finite type indexes those five clauses without dropping or splitting any of them.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), Theorem 6.2, p.21 (PDF p.23)

import Mathlib

set_option autoImplicit false

namespace NondetConn.Supplement

/-- The five graph properties in Zhang's Theorem 6.2. -/
inductive GraphProperty where
  | bipartite
  | cycleFree
  | eulerian
  | hamiltonian
  | planar
  deriving DecidableEq

end NondetConn.Supplement


