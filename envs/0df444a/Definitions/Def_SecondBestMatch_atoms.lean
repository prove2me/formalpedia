-- Prove2me | Definitions.Def_SecondBestMatch_atoms
-- name    : SecondBestMatch_atoms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:42.320972+00:00
-- url     : https://prove2.me/theorems/5589a5d0-7175-4245-8a7e-067ac1eb4597
-- title:
--   Atoms of a law
-- statement:
--   The **atoms** of a law $\mu$ are the points $x$ with $\mu\{x\}>0$. For a finite-support prior these are its support points $v_{i,1}<\dots<v_{i,L_i}$ (respectively $c_{j,1}<\dots<c_{j,H_j}$), each of positive probability.
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Section 3.2, p.10

import Mathlib

open MeasureTheory Set

namespace SecondBestMatch

/-- The atoms `{x : μ{x} > 0}` of a law (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §3.2, p.10): for a finite-support prior these
are its support points `v_{i,1} < ⋯ < v_{i,Lᵢ}`, each of positive probability. -/
def atoms (μ : Measure ℝ) : Set ℝ := {x | 0 < μ {x}}

end SecondBestMatch


