-- Prove2me | Definitions.Def_SecondBestMatch_IsFiniteSupportLaw
-- name    : SecondBestMatch_IsFiniteSupportLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:44.791181+00:00
-- url     : https://prove2.me/theorems/7caf21ed-4850-48db-a1c8-51c35c4c298f
-- title:
--   Finite-support law
-- statement:
--   A Borel probability law $\mu$ on $\mathbb R$ has **finite support** if some finite set carries all of its mass.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.1–3.2, p.10

import Mathlib

open MeasureTheory Set

namespace SecondBestMatch

/-- A law with finite support (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.1–3.2, p.10): some finite set carries all its mass. -/
def IsFiniteSupportLaw (μ : Measure ℝ) : Prop :=
  ∃ s : Finset ℝ, μ (↑s : Set ℝ)ᶜ = 0

end SecondBestMatch


