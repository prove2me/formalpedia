-- Prove2me | Definitions.Def_KelsoCrawford_OneSided_OneSided
-- name    : KelsoCrawford_OneSided_OneSided
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:26:16.157983+00:00
-- url     : https://prove2.me/theorems/29c0bf96-9ba5-4b71-a2ce-17c6eda26db9
-- title:
--   D1′–D2′ — individually rational and strict-core one-sided allocations
-- statement:
--   A one-sided allocation consists of a partition $P=(C_z)$ of the finite worker set and a real salary $s_i$ for each worker. Given a coalition production function $v$, individual rationality (D1′) requires $s_i\ge 0$ for every worker and the single aggregate budget condition
--
--   $$\sum_i s_i\le\sum_{C\in P}v(C).$$
--
--   It is in the strict core (D2′) if there are no coalition $C$ and proposed salaries $r_i$ with $r_i\ge s_i$ for all $i\in C$, $\sum_{i\in C}r_i\le v(C)$, and $r_i>s_i$ for at least one $i\in C$.
--
--   **Formalization Note** Mathlib's finite partition has nonempty parts. Empty parts in the paper would contribute zero when the no-free-lunch assumption $v(\varnothing)=0$ holds. The budget condition is aggregate, and an improving coalition requires a strictly higher worker salary.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1492–1493, D1′ (12)–(13), D2′ (14)–(15)

import Mathlib

namespace KelsoCrawford.OneSided

def IsOneSidedIR {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ) (P : Finpartition (Finset.univ : Finset W))
    (s : W → ℝ) : Prop :=
  (∀ i, 0 ≤ s i) ∧ ∑ i, s i ≤ ∑ C ∈ P.parts, v C

def IsOneSidedStrictCore {W : Type} [Fintype W] [DecidableEq W]
    (v : Finset W → ℝ) (P : Finpartition (Finset.univ : Finset W))
    (s : W → ℝ) : Prop :=
  IsOneSidedIR v P s ∧
    ¬ ∃ (C : Finset W) (r : W → ℝ),
      (∀ i ∈ C, s i ≤ r i) ∧
      (∑ i ∈ C, r i) ≤ v C ∧
      ∃ i ∈ C, s i < r i

end KelsoCrawford.OneSided


