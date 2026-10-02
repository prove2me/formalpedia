-- Prove2me | Definitions.Def_ProcessingNetworks_GlobalStability_UnidirectionalRing
-- name    : ProcessingNetworks_GlobalStability_UnidirectionalRing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T18:09:54.343366+00:00
-- url     : https://prove2.me/theorems/b6331d61-7d5d-4658-8bca-ad5171db2c2a
-- title:
--   The unidirectional ring network (Theorem 8.24's setting)
-- statement:
--   A **unidirectional ring network** with $L$ customer types and $K$ single-server stations: a
--   type-$\ell$ customer enters at some station $k$ and visits $k, k+1, \dots, k+n_\ell$ (indices
--   mod $K$); all classes served at station $k$ share mean service time $\beta_k$.
--
--   A **unidirectional ring network** with $L$ customer types and $K$ single-server stations: a
--   type-$\ell$ customer enters at some station $k$ and visits $k, k+1, \dots, k+n_\ell$ (indices
--   mod $K$); all classes served at station $k$ share mean service time $\beta_k$.
--
--   **Formalization note.** Rather than re-introducing per-type route lengths $n_\ell$ and
--   two-level class indices $(\ell,j)$, this mission characterizes the ring structure directly as
--   a property of an ordinary (flat-indexed) `QueueingNetworkData`: a partial successor function
--   `succ` encodes the deterministic routes (`succ i = some j` iff class `i` routes to class `j`
--   with probability `1`, matching the routing matrix `P`), the "next station" requirement is
--   `(p i + 1) mod K = p j`, the routes are disjoint paths (no class is the successor of two
--   classes, so each class is one customer type at one stage of its route), external arrivals
--   enter only at the first class of a route (a class with a predecessor has $\lambda = 0$),
--   same-station classes share a mean service time, and every station is a single server. This is
--   a faithful re-encoding — every unidirectional ring network in the book's sense is representable
--   this way (with `I = ∑_ℓ n_ℓ`), and conversely every network satisfying it is one — and it lets
--   Theorem 8.24 reuse `IsNonIdlingSolution`, `poolBuffers` and `workloadOperator` directly rather
--   than restating them for a bespoke two-index class structure.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 152, unidirectional ring network (Section 8.6)

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

/-- A unidirectional ring network (Dai & Harrison p. 152, PDF p. 168), stated as a structural
property of a queueing network: `succ i = some j` means class `i` routes deterministically to
class `j` on completion (`succ i = none` means class `i` exits the network); the ring structure
requires the successor to sit at the very next station (mod `K`); the routes are disjoint paths
(no class is the successor of two classes: each class `(ℓ, j)` belongs to a single customer type
`ℓ` at a single stage `j`), and external arrivals enter only at the first class of a route (a
class with a predecessor has `λ = 0`, since a type-`ℓ` customer enters at the first station of its
route); all classes served at a given station share a common mean service time (`βₖ`); and all
server pools are single-server (`b ≡ 1`). -/
def IsUnidirectionalRing {I K : ℕ} (dat : QueueingNetworkData I K) (succ : Fin I → Option (Fin I)) :
    Prop :=
  (∀ i j : Fin I, dat.P i j = if succ i = some j then 1 else 0) ∧
  (∀ i j : Fin I, succ i = some j → ((dat.p i : ℕ) + 1) % K = (dat.p j : ℕ)) ∧
  (∀ i i' j : Fin I, succ i = some j → succ i' = some j → i = i') ∧
  (∀ i j : Fin I, succ i = some j → dat.lam j = 0) ∧
  (∀ i i' : Fin I, dat.p i = dat.p i' → dat.m i = dat.m i') ∧
  (∀ k : Fin K, dat.b k = 1)

end ProcessingNetworks.GlobalStability


