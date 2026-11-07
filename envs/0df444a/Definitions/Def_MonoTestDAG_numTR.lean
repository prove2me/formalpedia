-- Prove2me | Definitions.Def_MonoTestDAG_numTR
-- name    : MonoTestDAG_numTR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:26.332274+00:00
-- url     : https://prove2.me/theorems/5356ac53-d376-4275-9985-49ab27fe07b1
-- title:
--   The transitive reduction and $m$
-- statement:
--   A pair $(u,v)$ is a **cover pair** if $u\ne v$, $u\leadsto v$, and every $w$ with $u\leadsto w\leadsto v$ is $u$ or $v$. The cover pairs of a DAG $G$ are the edges of its transitive reduction (Hasse diagram) $\mathrm{TR}(G)$, and $m$ is their number. The graph $G$ is **transitively reduced** if its edges are exactly its cover pairs, in which case $m=|E|$.
--
--   **Formalization Note.** The parameter $m$ is computed from reachability, not as the number of edges of $E$: an arbitrary DAG may contain transitive edges, and the paper's main theorem counts the edges of the transitive reduction. The module also defines `IsCoverPair`, `trPairs` and `IsTransReduced`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §2.1, p.10 and §1.2, p.1

import Mathlib
import Definitions.Def_MonoTestDAG_Reach

namespace MonoTestDAG

/-- `(u, v)` is a cover pair (an edge of the transitive reduction / Hasse diagram `TR(G)`):
`u ≠ v`, `u ⇝ v`, and no third vertex lies on a path from `u` to `v`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §2.1, p.10. -/
def IsCoverPair {V : Type} (E : V → V → Prop) (u v : V) : Prop :=
  u ≠ v ∧ Reach E u v ∧ ∀ w, Reach E u w → Reach E w v → w = u ∨ w = v

open Classical in
/-- The edge set of the transitive reduction `TR(G)`: all cover pairs of `⇝`. -/
noncomputable def trPairs {V : Type} [Fintype V] (E : V → V → Prop) : Finset (V × V) :=
  Finset.univ.filter (fun p => IsCoverPair E p.1 p.2)

/-- `m`, the number of edges of the transitive reduction `TR(G)` ("We write m for the number of
edges in the transitive reduction of G", §1.2, p.1).

Yoshida, arXiv:2602.15341 (sha256 454609db…), §1.2, p.1 and §2.1, p.10.

**Formalization Note.** `m` is computed from reachability, never as the number of edges of `E`:
an arbitrary DAG may contain transitive edges. For a transitively reduced DAG it equals `|E|`. -/
noncomputable def numTR {V : Type} [Fintype V] (E : V → V → Prop) : ℕ :=
  (trPairs E).card

/-- `G` is transitively reduced, `G = TR(G)`: its edges are exactly the cover pairs.
Yoshida, arXiv:2602.15341 (sha256 454609db…), §2.1, p.10. -/
def IsTransReduced {V : Type} (E : V → V → Prop) : Prop :=
  ∀ u v, E u v ↔ IsCoverPair E u v

end MonoTestDAG


