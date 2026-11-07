-- Prove2me | Definitions.Def_SmoothedNash_SupportProfile
-- name    : SmoothedNash_SupportProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:44.561433+00:00
-- url     : https://prove2.me/theorems/29de872f-b103-4dc6-81b7-f9064871923e
-- title:
--   Support profile $A = (A_1, \dots, A_m)$
-- statement:
--   A **support profile** is a tuple $A = (A_1, \dots, A_m)$ of nonempty sets of actions,
--   $$
--   \emptyset \ne A_i \subseteq [n], \qquad i \in [m].
--   $$
--   Algorithm 2 guesses the support profile of an equilibrium and searches each guess separately; there are $(2^n - 1)^m$ support profiles.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §2.1, p.13

import Mathlib

namespace SmoothedNash

/-- A **support profile** `A = (A_1, …, A_m)` with `∅ ≠ A_i ⊆ [n]` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §2.1, p.13). -/
abbrev SupportProfile (m n : ℕ) : Type :=
  {A : Fin m → Finset (Fin n) // ∀ i, (A i).Nonempty}

end SmoothedNash


