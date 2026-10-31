-- Prove2me | Definitions.Def_PlatformCournot_linearCost
-- name    : PlatformCournot_linearCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:25.767084+00:00
-- url     : https://prove2.me/theorems/e7d0bb50-0497-41a8-a3a5-6fcee8cd8986
-- title:
--   Piecewise linear cost $(c\,s)^+$
-- statement:
--   The **piecewise linear cost** with slope $c$ is
--
--   $$s\mapsto (c\,s)^+=\max\{c\,s,0\}.$$
--
--   These are the cost functions of Lemma 2 and of the proof of Theorem 1. For $c\ge 0$ they satisfy Assumption 1.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Lemma 2, p.17; Appendix A.1, p.26; Appendix A.3, p.29

import Mathlib

namespace PlatformCournot

/-- **Piecewise linear cost `(c s)⁺`.**
Pang et al., arXiv:1903.04574v3, Lemma 2, p.17 ("C̄i(si) := (∂+Ci(…) · si)^+"), Appendix A.1, p.26
("C̄i(si) := max{λisi, 0}") and Appendix A.3, p.29 ("Ci(si) = (cisi)+").

`linearCost c s = max (c s) 0`. For `c ≥ 0` it satisfies Assumption 1. -/
def linearCost (c : ℝ) (s : ℝ) : ℝ :=
  max (c * s) 0

end PlatformCournot


