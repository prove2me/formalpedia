-- Prove2me | Definitions.Def_AnchoredEP_RunState
-- name    : AnchoredEP_RunState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:59.92737+00:00
-- url     : https://prove2.me/theorems/2fe7f519-9065-47e1-aa25-aedb12009fec
-- title:
--   State of a run of Algorithm 3
-- statement:
--   A run of Algorithm 3 is either **running**, at the start of an outer iteration with state $(z_k,v_k,A_k)$, or has **returned** a point $\hat z$ together with a vector $\hat v$, which certifies $\hat v\in H(\hat z)$ and $\|F(\hat z)+\hat v\|\le\varepsilon$ in the complexity theorem.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Algorithm 3, p.37

import Mathlib
import Definitions.Def_AnchoredEP_IterState

namespace AnchoredEP

/-- **The state of a run of Algorithm 3.** Jiang–Yoon, arXiv:2609.30212, Algorithm 3, p.37: a run
is either still running, at the start of an outer iteration with state `(z_k, v_k, A_k)`, or has
returned a point `ẑ` together with the vector `v̂ ∈ H(ẑ)` that certifies its residual. -/
inductive RunState (d : ℕ) where
  /-- the run is at the start of an outer iteration with state `(z_k, v_k, A_k)` -/
  | running (s : IterState d)
  /-- the run has returned the point `ẑ`, with certificate vector `v̂` -/
  | returned (z v : EuclideanSpace ℝ (Fin d))

end AnchoredEP


