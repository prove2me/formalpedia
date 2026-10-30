-- Prove2me | Definitions.Def_OnlineConvexOpt_Approachability_supportFun
-- name    : OnlineConvexOpt_Approachability_supportFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:42.313081+00:00
-- url     : https://prove2.me/theorems/11abacc8-1877-4745-97dd-b7127298497b
-- title:
--   Support function $h_S$ of a set
-- statement:
--   For a set $S\subseteq\mathbb R^d$ and a vector $w\in\mathbb R^d$, the **support function** of $S$ at $w$ is
--
--   $$
--   h_S(w)=\max_{x\in S} w^\top x .
--   $$
--
--   It is a maximum of linear functions of $w$, hence convex in $w$. In Chapter 13 it enters the dual description of the distance to a convex set (Lemma 13.5) and Blackwell's condition in the form of Lemma 13.6.
--
--   **Formalization Note** The maximum is a real supremum over $S$. For a nonempty bounded $S$ it is the true supremum, and for nonempty closed bounded $S$ it is attained, as on the page. On an empty or unbounded set the Lean supremum returns $0$; every statement of this mission that uses $h_S$ assumes $S$ nonempty, closed and bounded.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, §13.2, unnumbered display, p. 210 (PDF p. 232)

import Mathlib

open scoped InnerProductSpace

namespace OnlineConvexOpt.Approachability

/-- **The support function `h_S` of a set.**
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, §13.2,
unnumbered display, p. 210: "The support function of closed convex set S is given by
h_S(w) = max_{x∈S} {w⊤x}."

`supportFun S w` is `⨆ s ∈ S, ⟪w, s⟫`, the supremum of the linear functional `x ↦ w⊤x` over `S`.

**Formalization Note.** The supremum is a real `iSup` over the subtype `S`. For a nonempty
bounded `S` it is the true supremum, and for a nonempty compact `S` (closed and bounded, as in
every statement of this mission) it is attained, i.e. it is the printed `max`. On an empty or
unbounded `S` the real `iSup` returns the junk value `0`; every statement that uses
`supportFun S` therefore assumes `S` nonempty, closed and bounded. -/
noncomputable def supportFun {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ s : S, ⟪w, (s : EuclideanSpace ℝ (Fin d))⟫_ℝ

end OnlineConvexOpt.Approachability


