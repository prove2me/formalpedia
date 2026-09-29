-- Prove2me | Definitions.Def_OnlineConvexOpt_Blackwell_SupportFunction
-- name    : OnlineConvexOpt_Blackwell_SupportFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:52:17.504362+00:00
-- url     : https://prove2.me/theorems/fa332a0a-12de-4ea6-92cb-e39b9768b4f9
-- title:
--   Support function of a convex set
-- statement:
--   $h_S(w) = \max_{x\in S}\{w^\top x\}$ (p. 210), rendered as a real supremum — a genuine
--   maximum when $S$ is compact, as this chapter's standing "closed, bounded" hypothesis on $S$
--   ensures. Used by Algorithm 37's proxy loss $f_t(w)=w^\top u_{t-1}-h_S(w)$ and by Lemma
--   13.5's dual characterization of $\mathrm{Dist}(\cdot,S)$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 210 (PDF p. 232)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.Blackwell

/-- The support function of a closed convex set `S` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 210, PDF p. 232): `h_S(w) = max_{x∈S}{w^⊤x}`,
rendered as a real supremum (a genuine maximum when `S` is compact, as the book's standing
"closed, bounded" hypothesis on `S` ensures). -/
noncomputable def SupportFunction {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ x ∈ S, (⟪w, x⟫_ℝ : ℝ)

end OnlineConvexOpt.Blackwell


