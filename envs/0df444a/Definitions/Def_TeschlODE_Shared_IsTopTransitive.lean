-- Prove2me | Definitions.Def_TeschlODE_Shared_IsTopTransitive
-- name    : TeschlODE_Shared_IsTopTransitive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:20:13.267959+00:00
-- url     : https://prove2.me/theorems/75924bf1-c0fb-4f88-a1d3-694b4a6e2602
-- title:
--   Topologically transitive map
-- statement:
--   A map $f : M \to M$ on a topological (in the book: metric) space is **topologically transitive** if for any nonempty open sets $U, V \subseteq M$ there is an $n \in \mathbb{N} = \{1, 2, \dots\}$ with
--   $$f^n(U) \cap V \neq \emptyset .$$
--
--   This one definition serves chunk 09-interval-maps (the definition of chaos, p. 296, and of a repellor, §11.6, p. 307) and chunk 11-horseshoe (through the definition of chaos, used in Theorem 13.1, p. 333).
--
--   **Formalization Note.** The book says "for any given open sets $U, V$"; with $U = \emptyset$ the condition cannot hold, so nonemptiness is implicit and is made explicit here. The book's $\mathbb{N}$ excludes $0$, hence $n \ge 1$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 296, §11.3

import Mathlib

namespace TeschlODE.Shared

/-- Teschl, §11.3, p. 296: `f : M → M` is topologically transitive if for any given (nonempty)
open sets `U, V ⊆ M` there is an `n ∈ ℕ = {1, 2, …}` such that `fⁿ(U) ∩ V ≠ ∅`. Nonemptiness of
`U` and `V` is implicit in the book (for `U = ∅` the condition fails) and explicit here. -/
def IsTopTransitive {M : Type*} [TopologicalSpace M] (f : M → M) : Prop :=
  ∀ U V : Set M, IsOpen U → IsOpen V → U.Nonempty → V.Nonempty →
    ∃ n : ℕ, 1 ≤ n ∧ (f^[n] '' U ∩ V).Nonempty

end TeschlODE.Shared


