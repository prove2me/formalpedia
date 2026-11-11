-- Prove2me | Definitions.Def_GaussDiffSVP_isoOut
-- name    : GaussDiffSVP_isoOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:59.434211+00:00
-- url     : https://prove2.me/theorems/6c5b448b-c10b-470a-be09-b7153959072d
-- title:
--   Output list of an isolated merge
-- statement:
--   Given child lists and an activation pattern $B$, the isolated merge keeps one record $T(X_i,Y_j)$ for every activated pair $(i,j)$ such that no other activated pair uses $i$ or $j$: the edges whose two endpoints both have degree one in the completed activation graph.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.3, p.25; Algorithm 1, line 17, p.29

import Mathlib

namespace GaussDiffSVP

/-- The output of an isolated merge (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.3, p.25: "Retain an activated pair only if no other
activated pair uses either endpoint"; Algorithm 1, line 17, p.29: "Keep the edges whose two
endpoints both have degree one in the completed graph"): one record with value `T(X_i, Y_j)` for
every activated pair `(i, j)` such that no other activated pair shares `i` or `j`. -/
def isoOut {α β γ : Type*} (T : α → β → γ) (lL : List α) (lR : List β)
    (B : Fin lL.length × Fin lR.length → Bool) : List γ :=
  (List.finRange lL.length).flatMap fun i =>
    ((List.finRange lR.length).filter fun j =>
        B (i, j) && decide (∀ e : Fin lL.length × Fin lR.length,
          e ≠ (i, j) → (e.1 = i ∨ e.2 = j) → B e = false)).map
      fun j => T (lL.get i) (lR.get j)

end GaussDiffSVP


