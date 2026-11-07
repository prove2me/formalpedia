-- Prove2me | Definitions.Def_LCPlanarSteiner_ArrivesBy
-- name    : LCPlanarSteiner_ArrivesBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:36.738415+00:00
-- url     : https://prove2.me/theorems/d79093dc-d39e-4048-9975-0ecdaa2d8f62
-- title:
--   Extensions that arrive by their arrival values
-- statement:
--   Let $A(v) \in \mathbb{Q} \cup \{+\infty\}$ be arrivals and $Q_v$ extensions, for a graph with root $r$, owned arcs $E_R$, boundary $B$ and purchased union $F$. The extensions **arrive by** $A$ when, for every vertex $v$ with finite $A(v)$, the extension $Q_v$ is a walk of owned arcs from some boundary vertex $b \in B$ to $v$, and some walk $W$ from $r$ to $b$ inside $F$ satisfies
--   $$
--   \ell(W) + \ell(Q_v) \le A(v).
--   $$
--
--   This is the property of the output of Lemma 3.2 that the forward profile of Lemma 3.3 uses.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 3.2, p.5; p.6 (actual paid prefix to a labeled boundary vertex)

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsWalk
import Definitions.Def_LCPlanarSteiner_plen

namespace LCPlanarSteiner

/-- **Extensions that arrive by their arrival values.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 3.2, p.5: "Each returned extension … arrives by A(v)"; p.6: "It starts with an actual
paid prefix to a labeled boundary vertex."

`ArrivesBy G ER B F r A Q`: for every vertex `v` with finite arrival `A(v) = a`, the extension `Q v`
is a walk of owned arcs (in `E_R`) from some boundary vertex `b ∈ B` to `v`, and some walk `W` from
the root `r` to `b` in the purchased union `F` has `ℓ(W) + ℓ(Q v) ≤ a`.

**Formalization Note.** Arrivals take values in `WithTop ℚ` (`⊤ = +∞`, no extension). This is the
part of Lemma 3.2's output that Lemma 3.3 uses. -/
def ArrivesBy (G : Net) (ER B F : Finset ℕ) (r : ℕ) (A : ℕ → WithTop ℚ) (Q : ℕ → List ℕ) :
    Prop :=
  ∀ (v : ℕ) (a : ℚ), A v = a →
    ∃ b ∈ B, IsWalk G b v (Q v) ∧ (∀ e ∈ Q v, e ∈ ER) ∧
      ∃ W : List ℕ, IsWalk G r b W ∧ (∀ e ∈ W, e ∈ F) ∧ plen G W + plen G (Q v) ≤ a

end LCPlanarSteiner


