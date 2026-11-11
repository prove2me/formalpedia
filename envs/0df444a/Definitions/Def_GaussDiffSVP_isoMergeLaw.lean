-- Prove2me | Definitions.Def_GaussDiffSVP_isoMergeLaw
-- name    : GaussDiffSVP_isoMergeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:38.63021+00:00
-- url     : https://prove2.me/theorems/99b69528-cc8e-4f1f-a102-095d1b14cd0d
-- title:
--   Law of an isolated merge
-- statement:
--   The law of the output of an isolated merge: independent child lists, activation pattern from the coin kernel given the completed child lists, and only isolated activated edges kept.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.3, p.25; Algorithm 1, p.29

import Mathlib
import Definitions.Def_GaussDiffSVP_isoOut

namespace GaussDiffSVP

/-- The law of an isolated merge (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §4.3, p.25; Algorithm 1, lines 12–18, p.29): the two child
lists are drawn independently, the activation pattern is drawn from the coin kernel `κ` given the
completed child lists, and only activated pairs whose two endpoints have degree one are kept
(`isoOut`). -/
noncomputable def isoMergeLaw {α β γ : Type*} (μL : PMF (List α)) (μR : PMF (List β))
    (T : α → β → γ)
    (κ : (lL : List α) → (lR : List β) → PMF (Fin lL.length × Fin lR.length → Bool)) :
    PMF (List γ) :=
  μL.bind fun lL => μR.bind fun lR => (κ lL lR).map (isoOut T lL lR)

end GaussDiffSVP


