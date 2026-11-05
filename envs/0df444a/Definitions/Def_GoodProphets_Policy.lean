-- Prove2me | Definitions.Def_GoodProphets_Policy
-- name    : GoodProphets_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:54.514925+00:00
-- url     : https://prove2.me/theorems/c83301fb-b6c2-4588-98fb-2fe6e0dd822e
-- title:
--   Online algorithms that learn the horizon $T$ only after the heads-up time $\hat T$
-- statement:
--   An **online algorithm** chooses, in each period, a probability distribution over the $\ell$ actions of the arriving type. Its input is
--
--   1. the past (type, action) pairs, oldest first;
--   2. the type of the current arrival;
--   3. the horizon information, which is "unknown" in the periods $t\le\hat T$ and the true horizon $T$ in the periods $t>\hat T$ after the heads-up (Assumption 3).
--
--   The algorithm sees nothing else. In particular it never sees the arrival distribution or the future arrivals, and it does not see $T$ before the heads-up. The module also defines, for a policy, an arrival distribution $\vec p$ and a heads-up time $\hat T$:
--
--   - the probability of a trajectory $(\theta_1,a_1,\dots,\theta_T,a_T)$, which is $\prod_ip_{\theta_i}$ times the probability that the policy picks $a_i$ given the first $i-1$ pairs, $\theta_i$ and the horizon information of period $i$;
--   - the final type-action counts $x^{\mathrm{ALG}}_{\theta j}$, the number of periods in which a type-$\theta$ arrival received action $a_{\theta j}$.
--
--   **Formalization Note** A policy is a function `List (Fin k × Fin ℓ) → Fin k → Option ℕ → PMF (Fin ℓ)`. The period number is the length of the history. The horizon information is `some T` exactly in the periods $t>\hat T$.
-- source:
--   S. Banerjee and D. Freund, Good prophets know when the end is near, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript, sha256 2cfd1ada…2c46), §2, pp.7–8, "Actions", Assumption 3; §3, p.12, Algorithm 1 (the information an algorithm uses)

import Mathlib

namespace GoodProphets

/-- An online algorithm for the model of Banerjee & Freund, *Good prophets know when the end is
near*, Management Science (2024), doi:10.1287/mnsc.2023.04307 (author manuscript), §2, pp.7–8: in
each period it observes the arriving type and chooses one of the `ℓ` actions of that type, possibly
at random. Its input is

1. the list of the past `(type, action)` pairs, oldest first;
2. the type of the current arrival;
3. the horizon information: `none` before the heads-up, `some T` after it (Assumption 3, p.8).

**Formalization Note** The policy sees nothing else: not the arrival distribution `p`, not the
horizon `T` before the heads-up, not the heads-up time `T̂`, and no future arrival. That is
enforced by this type and by the quantifier order of the goal (the policy is chosen before `p`,
`T` and `T̂`). The period number is the length of the history. -/
abbrev Policy (k ℓ : ℕ) := List (Fin k × Fin ℓ) → Fin k → Option ℕ → PMF (Fin ℓ)

/-- The first `i` pairs `(θ₁, a₁), …, (θᵢ, aᵢ)` of a trajectory, oldest first. -/
def history {k ℓ T : ℕ} (θs : Fin T → Fin k) (as : Fin T → Fin ℓ) (i : ℕ) :
    List (Fin k × Fin ℓ) :=
  ((List.finRange T).filter fun j : Fin T => decide ((j : ℕ) < i)).map fun j => (θs j, as j)

/-- The horizon information in period `i + 1` (index `i`) when the true horizon `T` is revealed at
the heads-up time `T̂` (doi:10.1287/mnsc.2023.04307, Assumption 3, p.8): `some T` in the periods
`t > T̂` after the heads-up, `none` in the periods `t ≤ T̂`. -/
def horizonInfo {T : ℕ} (Th : ℕ) (i : Fin T) : Option ℕ :=
  if Th ≤ (i : ℕ) then some T else none

/-- The probability of the trajectory `(θ⃗, a⃗)` under i.i.d. arrivals from `p` and the policy `π`:
`∏ᵢ p_{θᵢ} · π(history, θᵢ, info)(aᵢ)`. -/
noncomputable def trajWeight {k ℓ T : ℕ} (π : Policy k ℓ) (p : Fin k → ℝ) (Th : ℕ)
    (θs : Fin T → Fin k) (as : Fin T → Fin ℓ) : ℝ :=
  ∏ i : Fin T, p (θs i) * ((π (history θs as i) (θs i) (horizonInfo Th i)) (as i)).toReal

/-- The final type-action counts `x^ALG_θj`: the number of periods with arrival type `θ` in which
action `a_θj` was used (doi:10.1287/mnsc.2023.04307, p.7, "Actions"). -/
def xALG {k ℓ T : ℕ} (θs : Fin T → Fin k) (as : Fin T → Fin ℓ) : Fin k → Fin ℓ → ℝ :=
  fun θ j => ((Finset.univ.filter fun i : Fin T => θs i = θ ∧ as i = j).card : ℝ)

end GoodProphets


