-- Prove2me | Definitions.Def_SparseHistComm_IsHomogeneous
-- name    : SparseHistComm_IsHomogeneous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:26.07298+00:00
-- url     : https://prove2.me/theorems/b404fd35-6298-4d9b-91bb-8c337c59079a
-- title:
--   Homogeneous protocol: one common channel $Q_r$
-- statement:
--   A protocol is **homogeneous** if all users use the same channel after fixing the public randomness: $Q_{i,r} = Q_r$ for every user $i$ and every $r$, so that
--   $$
--   P(M_1 = m_1,\dots,M_n = m_n \mid x_1,\dots,x_n, R = r) = \prod_{i=1}^n Q_r(m_i \mid x_i).
--   $$
--   Different users may still send different messages, since their inputs and their private randomness differ.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (5), p.3

import Mathlib
import Definitions.Def_SparseHistComm_Protocol

namespace SparseHistComm

/-- A protocol is **homogeneous** if all users use the same channel after fixing the public
randomness: `Q_{i,r} = Q_r` for every user `i` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Eq. (5), p.3). -/
def IsHomogeneous {n d : ℕ} (P : Protocol n d) : Prop :=
  ∀ i j, P.enc i = P.enc j

end SparseHistComm


