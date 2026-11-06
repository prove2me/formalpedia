-- Prove2me | Definitions.Def_MatchedUCLB_smoothMax
-- name    : MatchedUCLB_smoothMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:58.580555+00:00
-- url     : https://prove2.me/theorems/bc292e7d-6b9d-4e92-ac97-cb57b7829378
-- title:
--   The smooth maximum $M_\delta(a,b)=a+\psi_\delta(b-a)$
-- statement:
--   For $\delta>0$ and $a,b\in\mathbb R$, the **smooth maximum** is
--
--   $$
--   M_\delta(a,b)=a+\psi_\delta(b-a).
--   $$
--
--   It is a smooth convex substitute for $\max\{a,b\}$ that equals the larger argument whenever the two differ by at least $\delta$ (Lemma 4.2). It joins the base formulas (4.4) and builds the phase functions (4.12d).
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition 4.1, Eq. (4.1), p.5

import Mathlib
import Definitions.Def_MatchedUCLB_psi

namespace MatchedUCLB

/-- **The smooth maximum `M_δ`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition 4.1, Eq. (4.1), p.5:
"`M_δ(a, b) := a + ψ_δ(b − a)` (`a, b ∈ ℝ`)". -/
noncomputable def smoothMax (δ a b : ℝ) : ℝ :=
  a + psi δ (b - a)

end MatchedUCLB


