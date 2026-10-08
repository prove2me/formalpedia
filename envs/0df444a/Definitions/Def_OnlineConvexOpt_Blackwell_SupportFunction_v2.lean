-- Prove2me | Definitions.Def_OnlineConvexOpt_Blackwell_SupportFunction_v2
-- name    : OnlineConvexOpt_Blackwell_SupportFunction_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:43.39749+00:00
-- url     : https://prove2.me/theorems/92a4157f-8852-4615-b86f-c11de14d723f
-- title:
--   Support function $h_S(w)=\max_{x\in S}w^\top x$ (genuine supremum over S)
-- statement:
--   The support function $h_S(w)=\sup\{w^\top x:x\in S\}$ of a set $S\subseteq\mathbb R^d$, a genuine maximum for compact nonempty $S$. Corrected version of `OnlineConvexOpt_Blackwell_SupportFunction`: the supremum is taken over the image of $S$ instead of via the binder `⨆ x ∈ S, …`, which on $\mathbb R$ returns the junk value $0$ outside $S$ and so computed $\max(h_S(w),0)$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 210 (PDF p. 232)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.Blackwell

/-- The support function of a closed convex set `S` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 210, PDF p. 232): `h_S(w) = max_{x∈S}{w^⊤x}`,
rendered as the real supremum of the image of `S` under `x ↦ ⟪w, x⟫` — a genuine maximum when
`S` is nonempty and compact, as the book's standing "closed, bounded" hypothesis on `S` ensures.
(The retired version used the binder `⨆ x ∈ S, …`, which on `ℝ` evaluates to the junk value
`sSup ∅ = 0` at every `x ∉ S` and so returned `max(h_S(w), 0)` instead of `h_S(w)`.) -/
noncomputable def SupportFunction {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun x => (⟪w, x⟫_ℝ : ℝ)) '' S)

end OnlineConvexOpt.Blackwell


