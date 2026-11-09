-- Prove2me | Definitions.Def_AgnosticTNS_TTN
-- name    : AgnosticTNS_TTN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:14.491327+00:00
-- url     : https://prove2.me/theorems/add90a0e-3dc2-4613-a2c8-59fe35b0ef81
-- title:
--   Tree tensor network description
-- statement:
--   A tree tensor network description on node set $[m]$ for $n$ qudits of dimension $d$ consists of a parent map (with the root having no parent), an assignment of each physical qudit to a node, a bond dimension for the edge joining each node to its parent, and at each node $k$ a tensor with one index per physical qudit at $k$, one index for its own bond and one index for the bond of each child. Proposition 3.8 represents the output of Algorithm 1 in this form.
--
--   **Formalization Note** That the parent map forms a given tree is imposed where it is needed (`TTN.IsOn`, Proposition 3.8). The root's own bond index is summed over in the contraction.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.8, pp.24–25; Theorem 1.1, p.3

import Mathlib

namespace AgnosticTNS

/-- **A tree tensor network description**, Proposition 3.8, p.24, and the outputs of Theorem 1.1,
Corollaries 5.1–5.2 (pp.3, 39–40) (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Nodes are `Fin m`; node `k` has a parent `parent k`
(`none` at the root), the physical qudits `v` with `site v = k`, a bond of dimension `bond k` joining
it to its parent, and a tensor with one index per physical qudit at `k`, one index for its own bond
and one index for the bond of each child `c` (`parent c = some k`).

**Formalization Note** The contraction is `TTN.state`; that the parent relation is a given tree is
imposed where needed (`TTN.IsOn`, Proposition 3.8). The root's own bond index is summed over, so a
root bond larger than one only adds the root tensor's slices. -/
structure TTN (m n d : ℕ) where
  /-- the parent of each node (`none` at the root) -/
  parent : Fin m → Option (Fin m)
  /-- the node carrying each physical qudit -/
  site : Fin n → Fin m
  /-- the dimension of the bond joining a node to its parent -/
  bond : Fin m → ℕ
  /-- the tensor at a node: physical labels, own bond index, children's bond indices -/
  tensor : (k : Fin m) → ({v // site v = k} → Fin d) → Fin (bond k) →
    ((c : {c // parent c = some k}) → Fin (bond c.1)) → ℂ

end AgnosticTNS


