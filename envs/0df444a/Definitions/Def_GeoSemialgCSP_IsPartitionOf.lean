-- Prove2me | Definitions.Def_GeoSemialgCSP_IsPartitionOf
-- name    : GeoSemialgCSP_IsPartitionOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:58.695102+00:00
-- url     : https://prove2.me/theorems/6590b4ad-0060-4dfa-ac8a-9fce8dceba7b
-- title:
--   Partition into nonempty parts
-- statement:
--   Sets $S_0,\dots,S_{q-1}$ form a **partition of $X$ into nonempty parts** if each $S_a$ is nonempty, they are pairwise disjoint, and their union is $X$: $X=S_0\sqcup\dots\sqcup S_{q-1}$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §5, p.14 (PDF p.15); Lemma 5.1; Theorem 7.1, p.20 (PDF p.21)

import Mathlib

namespace GeoSemialgCSP

/-- **Partition into nonempty parts.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §5, printed p.14 (PDF p.15)
("`X = S₀ ⊔ ⋯ ⊔ S_{q−1}`"), Lemma 5.1 ("partition into `q ≤ q₀` nonempty parts"), and Theorem 7.1
("partition `ℝ^d = C₀ ⊔ ⋯ ⊔ C_{q−1}` into `q` nonempty cells"). -/
def IsPartitionOf {U : Type*} {q : ℕ} (part : Fin q → Set U) (X : Set U) : Prop :=
  (∀ a, (part a).Nonempty) ∧ Pairwise (fun a b => Disjoint (part a) (part b)) ∧ (⋃ a, part a) = X

end GeoSemialgCSP


