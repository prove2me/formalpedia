-- Prove2me | Definitions.Def_GaussDiffSVP_fullMergeLaw
-- name    : GaussDiffSVP_fullMergeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:52.579205+00:00
-- url     : https://prove2.me/theorems/8e136ca6-90cc-4426-9bf6-c1a1cf7bff04
-- title:
--   Law of a full merge
-- statement:
--   The law of the output of a full merge: draw the two child lists independently from their laws, draw the activation pattern from the coin kernel given the completed child lists, and keep one record per activated pair. This is the law conditional on the merge's fixed information.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.1, pp.22–23

import Mathlib
import Definitions.Def_GaussDiffSVP_fullOut

namespace GaussDiffSVP

/-- The law of a full merge (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.1, p.22): the two child lists are drawn independently from
`μL` and `μR` ("fixed information that makes them independent"), the activation pattern is drawn
from the coin kernel `κ` given the completed child lists, and one record `T(X_i, Y_j)` is kept
for every activated pair (`fullOut`).

**Formalization Note.** The law is conditional on the merge's fixed information; independence of
the children is the product law. -/
noncomputable def fullMergeLaw {α β γ : Type*} (μL : PMF (List α)) (μR : PMF (List β))
    (T : α → β → γ)
    (κ : (lL : List α) → (lR : List β) → PMF (Fin lL.length × Fin lR.length → Bool)) :
    PMF (List γ) :=
  μL.bind fun lL => μR.bind fun lR => (κ lL lR).map (fullOut T lL lR)

end GaussDiffSVP


