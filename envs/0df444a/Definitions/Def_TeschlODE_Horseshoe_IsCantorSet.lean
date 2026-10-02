-- Prove2me | Definitions.Def_TeschlODE_Horseshoe_IsCantorSet
-- name    : TeschlODE_Horseshoe_IsCantorSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:44:10.285541+00:00
-- url     : https://prove2.me/theorems/dfa0519d-66ac-4379-825e-3b28990fc901
-- title:
--   Cantor set: compact, perfect and totally disconnected
-- statement:
--   A subset $C$ of a topological space is a **Cantor set** if it is compact, perfect (every point of $C$ is an accumulation point of $C$) and totally disconnected. For the last property the book gives the general definition of p. 302: for any two distinct points $x, y \in C$ there are disjoint open sets $U \ni x$ and $V \ni y$ with $C \subseteq U \cup V$. For subsets of $\mathbb{R}$ this agrees with "contains no open subintervals" (p. 299, Problem 11.8).
--
--   **Formalization Note.** Mathlib's `IsCompact`, `IsTotallySeparated` (the p. 302 definition) and `Preperfect`. As in the book, the empty set qualifies; every set in this mission to which the definition is applied is nonempty.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 299, §11.4, and p. 302, §11.5

import Mathlib

namespace TeschlODE.Horseshoe

/-- Teschl, §11.4, p. 299 and §11.5, p. 302: a Cantor set is a set which is compact, perfect
(every point of it is an accumulation point of it: Mathlib's `Preperfect`) and totally
disconnected in the sense of p. 302: any two distinct points `x, y` have disjoint open
neighborhoods `U ∋ x`, `V ∋ y` with `U ∪ V` covering the set (Mathlib's `IsTotallySeparated`).
For subsets of `ℝ` this agrees with "contains no open subintervals" of p. 299 (Problem 11.8). -/
def IsCantorSet {X : Type*} [TopologicalSpace X] (C : Set X) : Prop :=
  IsCompact C ∧ IsTotallySeparated C ∧ Preperfect C

end TeschlODE.Horseshoe


