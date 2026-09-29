-- Prove2me | Definitions.Def_GoldbergTarjan_Generic_Labeling
-- name    : GoldbergTarjan_Generic_Labeling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:22:57.43732+00:00
-- url     : https://prove2.me/theorems/c4850a91-2409-4891-8405-eb2edd39a9bb
-- title:
--   Valid labeling $d : V \to \mathbb{N} \cup \{\infty\}$ and active vertices
-- statement:
--   Let $N$ be a flow network with $n = |V|$ vertices, source $s$ and sink $t$, and let $f$ be a real function on vertex pairs with residual capacities $r_f$.
--
--   A **valid labeling** for $f$ is a function $d$ from the vertices to the nonnegative integers and infinity such that
--   $$d(s) = n, \qquad d(t) = 0, \qquad d(v) \le d(w) + 1 \ \text{ for every residual edge } (v,w),$$
--   where $\infty + 1 = \infty$.
--
--   Given a labeling $d$, a vertex $v$ is **active** if $v \in V - \{s,t\}$, $d(v) < \infty$ and $e(v) > 0$.
--
--   Distance labels are lower bounds on residual distances to the sink (or, above $n$, to the source); active vertices are exactly those on which the generic algorithm may operate.
--
--   **Formalization Note.** Labels take values in `ℕ∞` (natural numbers with a top element $\infty$), where $\infty + 1 = \infty$.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 924 (valid labeling) and p. 925 (active vertex)

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Preflow

namespace GoldbergTarjan.Generic

variable {V : Type} [Fintype V]

/-- A valid labeling (p. 924): a function `d` from the vertices to the nonnegative integers
and infinity (`ℕ∞`) such that `d(s) = n`, `d(t) = 0`, and `d(v) ≤ d(w) + 1` for every
residual edge `(v, w)`, where `n = |V|`. -/
def IsValidLabeling (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) : Prop :=
  d N.s = (Fintype.card V : ℕ∞) ∧ d N.t = 0 ∧
    ∀ v w, IsResidualEdge N f v w → d v ≤ d w + 1

/-- A vertex `v` is active (p. 925) if `v ∈ V - {s, t}`, `d(v) < ∞` and `e(v) > 0`. -/
def IsActive (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v : V) : Prop :=
  v ≠ N.s ∧ v ≠ N.t ∧ d v < ⊤ ∧ 0 < excess f v

end GoldbergTarjan.Generic


