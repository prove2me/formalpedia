-- Prove2me | Definitions.Def_SmoothedNash_InK
-- name    : SmoothedNash_InK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:47.035217+00:00
-- url     : https://prove2.me/theorems/cdde71d3-694e-40db-be03-b1b7f997f2a4
-- title:
--   The product of simplices $K_A$
-- statement:
--   For a nonempty $A \subseteq [n]$ let $\Delta(A) := \{x \in \Delta_n : x(a) = 0 \text{ for all } a \notin A\}$. For a support profile $A = (A_1, \dots, A_m)$,
--   $$
--   K_A := \Delta(A_1) \times \cdots \times \Delta(A_m),
--   $$
--   the set of mixed profiles in which each player $i$ plays only actions of $A_i$. Algorithm 2 searches $K_A$ for each guessed support profile $A$.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §2.1.1, p.13

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_SmoothedNash_SupportProfile

namespace SmoothedNash

/-- Membership in `K_A := Δ(A_1) × ⋯ × Δ(A_m)` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §2.1.1, p.13), where
`Δ(A) := {x ∈ Δ_n : x(a) = 0 for all a ∉ A}`. -/
def InK {m n : ℕ} (A : SupportProfile m n) (x : Fin m → Fin n → ℝ) : Prop :=
  AGT.IsMixedProfile (S := fun _ : Fin m => Fin n) x ∧ ∀ i a, a ∉ A.1 i → x i a = 0

end SmoothedNash


