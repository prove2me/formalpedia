-- Prove2me | Definitions.Def_WeakEpsNets_LowerBound_Nets
-- name    : WeakEpsNets_LowerBound_Nets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:13.514778+00:00
-- url     : https://prove2.me/theorems/19786414-341a-4b19-a58f-65f7641b2bd1
-- title:
--   Weak nets for all convex ranges
-- statement:
--   Let $P$ and $X$ be finite point sets in a real vector space, with $P$ nonempty and $r\ge1$ in the source's domain. The set $X$ is a weak $1/r$-net if
--   $$\forall C\text{ convex},\quad |C\cap P|\ge |P|/r\ \Longrightarrow\ X\cap C\ne\varnothing.$$
--   The threshold uses real division. Net points may lie anywhere in the ambient space, and the ranges include every convex subset, with no closedness or boundedness restriction.
--
--   This is the general weak-net predicate shared by the extremal quantities and the construction. It is defined on raw inputs as well; source statements enforce the relevant nonemptiness and positive-parameter domain. Its real-vector-space interface specializes to every finite-dimensional space used here.
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), §1, pp. 1–2, lines 21–24 and 42–45; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib

noncomputable section

namespace WeakEpsNets.LowerBound

/-- Finite weak nets for all convex ranges, source pp. 1–2.
The intended domain is nonempty P and r ≥ 1; no restriction is placed on net locations. -/
def IsWeakNet {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Finset E) (r : ℝ) (X : Finset E) : Prop := by
  classical
  exact ∀ C : Set E, Convex ℝ C →
    (P.card : ℝ) / r ≤ ((P.filter (fun p => p ∈ C)).card : ℝ) →
    ∃ x ∈ X, x ∈ C

end WeakEpsNets.LowerBound


