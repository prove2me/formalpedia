-- Prove2me | Definitions.Def_GaussDiffSVP_fullOut
-- name    : GaussDiffSVP_fullOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:50.822354+00:00
-- url     : https://prove2.me/theorems/0f94f4c7-77bf-4c61-9f01-74e03e86a83e
-- title:
--   Output list of a full merge
-- statement:
--   Given child lists $(X_i)$, $(Y_j)$ and an activation pattern $B$, the full merge keeps one record with value $T(X_i,Y_j)$ for **every** activated pair $(i,j)$, in lexicographic order of the pairs. Different pairs give different records even when they produce the same value.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.1, p.22; App. C.1.5, p.81

import Mathlib

namespace GaussDiffSVP

/-- The output of a full merge (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.1, p.22: "The full merge retains one record for every
activated pair. Different input record pairs remain distinct even when they produce the same
vector"): one record with value `T(X_i, Y_j)` for every activated pair `(i, j)`, in
lexicographic order of the pairs (App. C.1.5, p.81). -/
def fullOut {α β γ : Type*} (T : α → β → γ) (lL : List α) (lR : List β)
    (B : Fin lL.length × Fin lR.length → Bool) : List γ :=
  (List.finRange lL.length).flatMap fun i =>
    ((List.finRange lR.length).filter fun j => B (i, j)).map fun j => T (lL.get i) (lR.get j)

end GaussDiffSVP


