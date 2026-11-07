-- Prove2me | Definitions.Def_SmoothedNash_IsFrontierEnum
-- name    : SmoothedNash_IsFrontierEnum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:10.461972+00:00
-- url     : https://prove2.me/theorems/91fc090e-e382-450e-9336-08830b20ec0e
-- title:
--   Processing order of the frontiers
-- statement:
--   A **frontier enumeration** assigns to every support profile $A$ and every finite set $s$ of centers a list containing each element of $s$ exactly once. It is the order in which line 9 of Algorithm 2 ("for all $c \in F_t(A)$") visits the centers; the order matters only at the last level $D$, where the first passing center is returned.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 2 line 9, p.15

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile

namespace SmoothedNash

/-- A processing order of the frontiers for line 9 of Algorithm 2 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.15): for every support
profile `A` and finite set `s` of centers, `enum A s` lists every element of `s` exactly once. -/
def IsFrontierEnum {m n : ℕ}
    (enum : SupportProfile m n → Finset (Fin m → Fin n → ℕ) → List (Fin m → Fin n → ℕ)) : Prop :=
  ∀ A s, (enum A s).Nodup ∧ ∀ k, k ∈ enum A s ↔ k ∈ s

end SmoothedNash


