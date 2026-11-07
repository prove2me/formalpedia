-- Prove2me | Definitions.Def_GrothendieckLB_IsLocalInverseBranch
-- name    : GrothendieckLB_IsLocalInverseBranch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:30.135867+00:00
-- url     : https://prove2.me/theorems/c7fa0356-87b5-4845-909e-95d7240bd953
-- title:
--   Local inverse branch $H^{-1}$
-- statement:
--   $G$ is the **local inverse branch** of $H$ at the origin if $G$ is analytic at $0$, $G(0)=0$ and $H(G(z))=z$ for all $z$ near $0$.
--
--   **Formalization Note** When $H$ is analytic at $0$ with $H'(0)\ne0$, the inverse function theorem gives such a $G$ and its germ at $0$ is unique. Its Taylor coefficients are therefore the coefficients $a_n$ of $H^{-1}$ on the page.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 9.1, p.40

import Mathlib
open Topology

namespace GrothendieckLB

/-- `G` is the local inverse branch of `H` at the origin, `H⁻¹`: analytic at `0`, `G(0) = 0` and
`H(G(z)) = z` near `0` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 9.1, p.40).

**Formalization Note** When `H` is analytic at `0` with `H′(0) ≠ 0`, the inverse function theorem
gives such a `G` and the germ at `0` is unique, so its Taylor coefficients are the coefficients
`a_n` of the page. -/
def IsLocalInverseBranch (H G : ℝ → ℝ) : Prop :=
  AnalyticAt ℝ G 0 ∧ G 0 = 0 ∧ ∀ᶠ z in 𝓝 (0 : ℝ), H (G z) = z

end GrothendieckLB


