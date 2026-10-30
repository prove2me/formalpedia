-- Prove2me | Definitions.Def_OnlineCRS_Combine_IsRelaxation
-- name    : OnlineCRS_Combine_IsRelaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:37.0193+00:00
-- url     : https://prove2.me/theorems/15774884-56cf-4157-8df0-960d96d23391
-- title:
--   Relaxation of $P_{\mathcal F}$ (Definition 1.1)
-- statement:
--   Let $\mathcal F\subseteq 2^N$ and let $P_{\mathcal F}=\operatorname{conv}\{\mathbf 1_I : I\in\mathcal F\}$ be the convex hull of the characteristic vectors of feasible sets. A set $P\subseteq\mathbb R^N$ is a **relaxation** of $P_{\mathcal F}$ if
--   1. $P\subseteq[0,1]^N$, and
--   2. $P$ contains the same $\{0,1\}$-points as $P_{\mathcal F}$:
--   $$P\cap\{0,1\}^N=P_{\mathcal F}\cap\{0,1\}^N .$$
--
--   Online contention resolution schemes are defined relative to such a relaxation: the fractional point $x$ fed to the scheme lies in (a scaled copy of) $P$.
--
--   **Formalization Note** The paper prints $P_{\mathcal F}=\operatorname{conv}(\{\mathbf 1_F\mid I\in\mathcal F\})$; the bound variable is $I$, so this is read as $\mathbf 1_I$. The paper requires $P$ to be a polytope; here $P$ is any subset of the cube $[0,1]^N$ with the $\{0,1\}$-point property, which includes every polytope relaxation (no statement of the mission uses that $P$ is a polytope).
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, §1.1 and Definition 1.1, p. 2

import Mathlib
import Definitions.Def_OnlineCRS_Combine_indicatorVec

namespace OnlineCRS.Combine

/-- **Relaxation of `P_F` (Definition 1.1).**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, §1.1, p. 2: "`P_F = conv({1_F | I ∈ F})`" and Definition 1.1: "We say that a polytope
`P ⊆ [0,1]^N` is a relaxation of `P_F` if it contains the same `{0,1}`-points, i.e.,
`P ∩ {0,1}^N = P_F ∩ {0,1}^N`."

`IsRelaxation F P` says `P ⊆ [0,1]^N` and `P ∩ {0,1}^N = conv{1_I | I ∈ F} ∩ {0,1}^N`.

**Formalization Note.**
* Reading 1 (typo): the printed `1_F` inside the set builder is read as `1_I`, the only reading
  that typechecks ("the convex hull of all characteristic vectors of feasible sets").
* Reading 4 (generalization): `P` is any subset of the cube `[0,1]^N` (`Set.Icc 0 1` on `N → ℝ`,
  pointwise), not necessarily a polytope; every polytope relaxation is one. -/
def IsRelaxation {N : Type*} [DecidableEq N] (F : Finset (Finset N)) (P : Set (N → ℝ)) : Prop :=
  P ⊆ Set.Icc 0 1 ∧
    P ∩ {y | ∀ e, y e = 0 ∨ y e = 1} =
      convexHull ℝ (indicatorVec '' (F : Set (Finset N))) ∩ {y | ∀ e, y e = 0 ∨ y e = 1}

end OnlineCRS.Combine


