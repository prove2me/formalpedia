-- Prove2me | Definitions.Def_AvgValueAlloc_pathProb
-- name    : AvgValueAlloc_pathProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:09.950064+00:00
-- url     : https://prove2.me/theorems/3b5d362e-da83-4cd9-89fb-efcf3e821f46
-- title:
--   Randomized causal recipient rule and the law of its routing
-- statement:
--   A randomized recipient rule gives, at each funding position $t$ and for each past of decisions, a probability distribution over rejection and the positive alternatives of the current item. A routing $X$ then has probability $\prod_t \kappa_t(X_{<t})(X_t)$.
--
--   It is the setting of the half-maximum premise of Lemma 2.2 and of the local softmax rule.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), Lemma 2.2, p.5; §3.3, p.9

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **A randomized causal recipient rule on a funding path, and the law of its routings.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), Lemma 2.2, p.5: "If the conditional expected chosen
increment is at least half the maximum"; §3.3, p.9: "Choose uniformly with probability 1/2 and
otherwise proportional to exp(λ_m s_j/c_v)".

A kernel `κ t X o` is the probability of decision `o` at funding position `t` given the decisions
`X` (it may read only `X s`, `s < t`). `IsCausalKernel ρ M κ` requires causality, nonnegativity,
total mass one, and that a positive-probability recipient is a positive alternative of `M t`.
`pathProb κ X = Π_t κ t X (X t)` is the probability of the routing `X`; `pathPrefProb κ X t` is the
probability of its first `t` decisions. -/
def IsCausalKernel {n m : ℕ} (ρ : Fin n → ℚ) (M : Fin m → Vec n)
    (κ : Fin m → (Fin m → Option (Fin n)) → Option (Fin n) → ℝ) : Prop :=
  (∀ t X X', (∀ s, s < t → X s = X' s) → κ t X = κ t X') ∧ (∀ t X o, 0 ≤ κ t X o) ∧
    (∀ t X, ∑ o, κ t X o = 1) ∧ (∀ t X j, 0 < κ t X (some j) → ρ j ≤ (M t j : ℚ))

/-- The probability of a routing. -/
noncomputable def pathProb {n m : ℕ} (κ : Fin m → (Fin m → Option (Fin n)) → Option (Fin n) → ℝ)
    (X : Fin m → Option (Fin n)) : ℝ :=
  ∏ t, κ t X (X t)

/-- The probability of the first `t` decisions of a routing. -/
noncomputable def pathPrefProb {n m : ℕ}
    (κ : Fin m → (Fin m → Option (Fin n)) → Option (Fin n) → ℝ) (X : Fin m → Option (Fin n))
    (t : Fin m) : ℝ :=
  ∏ s ∈ Finset.univ.filter (· < t), κ s X (X s)

end AvgValueAlloc


