-- Prove2me | Definitions.Def_NondetConn_Buv
-- name    : NondetConn_Buv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:23:49.337191+00:00
-- url     : https://prove2.me/theorems/54f00353-28ab-400f-95aa-00bb72e99897
-- title:
--   Shortcut family $\mathcal B_{(u,v)}$
-- statement:
--   For a set $\mathcal B$ of permutations of $[n]$ and $u, v \in [n]$,
--   $$
--   \mathcal B_{(u,v)} = \{b_{(u,v)} \mid b \in \mathcal B\},
--   $$
--   the set of shortcut maps $b_{(u,v)} : [n]\setminus\{u\} \to [n]\setminus\{v\}$ of the members of $\mathcal B$. Distinct $b$ may give the same shortcut.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_NondetConn_shortcut

namespace NondetConn

/-- **The shortcut family `ℬ_(u,v)`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
§4.1, p.10): for a set `ℬ` of permutations of `[n]` and `u, v ∈ [n]`,
`ℬ_(u,v) = {b_(u,v) | b ∈ ℬ}`, with `b_(u,v)` the shortcut map (`shortcut`). -/
def Buv {n : ℕ} (ℬ : Finset (Equiv.Perm (Fin n))) (u v : Fin n) :
    Finset ({x : Fin n // x ≠ u} ≃ {y : Fin n // y ≠ v}) :=
  ℬ.image (fun b => shortcut b u v)

end NondetConn


