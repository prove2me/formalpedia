-- Prove2me | Definitions.Def_MonDepMW_closedSymmDiff
-- name    : MonDepMW_closedSymmDiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:54.52024+00:00
-- url     : https://prove2.me/theorems/58720272-9de0-464d-b8c7-8b0555e39e68
-- title:
--   The closed symmetric difference $\Delta[u,v]$ and the Hamming distance $\mathrm{ham}_{\mathcal Q}$
-- statement:
--   For distinct $u,v$, $\Delta_G[u,v]=(N_G(u)\triangle N_G(v))\cup\{u,v\}$, and $\Delta_G[v,v]=\emptyset$. For a partition $\mathcal Q$,
--   $$\mathrm{ham}_{\mathcal Q}(u,v)=|\{Q\in\mathcal Q:\Delta[u,v]\cap Q\neq\emptyset\}|.$$
--
--   These measure how differently two vertices see the graph, in the resolution of $\mathcal Q$.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, pp.11–12; §6, p.22

import Mathlib
import Definitions.Def_MonDepMW_partsHit

set_option autoImplicit false

namespace MonDepMW

/-- **`∆[u, v]`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, pp.11–12: "∆_G[u, v] := (N_G(u) △ N_G(v)) ∪ {u, v}" for distinct `u, v`, and
"We define ∆_G(v, v) = ∆_G[v, v] = ∅." -/
def closedSymmDiff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Set (Fin n) :=
  if u = v then ∅ else symmDiff (G.neighborSet u) (G.neighborSet v) ∪ {u, v}

/-- **The Hamming distance `ham_𝒬(u, v)`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §6, p.22: "ham_𝒬(u, v) := |{Q ∈ 𝒬: ∆[u, v] ∩ Q ≠ ∅}|." -/
noncomputable def ham {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Setoid (Fin n)) (u v : Fin n) : ℕ :=
  partsHit Q (closedSymmDiff G u v)

end MonDepMW


