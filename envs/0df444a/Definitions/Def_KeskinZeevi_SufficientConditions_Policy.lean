-- Prove2me | Definitions.Def_KeskinZeevi_SufficientConditions_Policy
-- name    : KeskinZeevi_SufficientConditions_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T03:28:21.38298+00:00
-- url     : https://prove2.me/theorems/b22c2e1c-0976-45c9-b202-fafd231dbb0e
-- title:
--   Non-anticipating pricing policy and the price process it generates
-- statement:
--   A **pricing policy** $\pi = (\pi_1, \pi_2, \dots)$ is deterministic and non-anticipating. The first price $\pi_1 \in [l,u]$ is a constant. For $t \ge 1$ the price of period $t+1$ is $\pi_{t+1}(H_t)$, where $\pi_{t+1}$ is a measurable map into $[l,u]$ and
--   $$H_t = (D_1, p_1, \dots, D_t, p_t)$$
--   is the observed history of demands and prices. Under a parameter $\theta = (\alpha,\beta)$ and a noise realisation, the policy generates prices and demands recursively:
--   $$p_1 = \pi_1, \qquad D_t = \alpha + \beta p_t + \varepsilon_t, \qquad p_{t+1} = \pi_{t+1}(H_t).$$
--
--   **Formalization Note.** `Policy M` has one field `rule t : (Fin t → ℝ × ℝ) → ℝ` for each $t \ge 0$, acting on the history of the first $t$ periods as (demand, price) pairs. It is measurable and takes values in $[l,u]$. `rule 0` acts on the empty history, so it is the constant $\pi_1$. A policy sees neither $\theta$ nor the noise. `price π θ ε t ω` is $p_t$ for $t \ge 1$, built by the recursion above from the noise `ε`. It realises the law (5) of the paper on the noise space. At $t = 0$ it returns $p_1$, and no statement uses that value. `demand π θ ε t ω` is $D_t$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1145, Section 2 (pricing policies, Eq. (5))

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_Model

namespace KeskinZeevi.SufficientConditions

/-- A deterministic non-anticipating pricing policy (Keskin–Zeevi 2014, p. 1145):
`rule t` maps the history `H_t = ((D₁, p₁), …, (D_t, p_t))` of the first `t` periods
(demand, price) to the price of period `t + 1`, measurably and into `[l, u]`. `rule 0` acts on the
empty history, so it is the constant first price `π₁`. The policy sees neither `θ` nor the noise. -/
structure Policy (M : Model) where
  rule : (t : ℕ) → (Fin t → ℝ × ℝ) → ℝ
  measurable_rule : ∀ t, Measurable (rule t)
  rule_mem : ∀ t h, rule t h ∈ Set.Icc M.l M.u

/-- Internal 0-based recursion: `priceAux π θ ε ω n` is the price of period `n + 1`, obtained by
feeding the realised history (demand `α + β p_s + ε s`, price `p_s`) of periods `1, …, n` into
`π.rule n`. -/
noncomputable def priceAux {M : Model} {Ω : Type*} (π : Policy M) (θ : ℝ × ℝ)
    (ε : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ
  | n => π.rule n (fun i : Fin n =>
      (θ.1 + θ.2 * priceAux π θ ε ω i + ε ((i : ℕ) + 1) ω, priceAux π θ ε ω i))
termination_by n => n
decreasing_by exact i.isLt

/-- The price `p_t` charged in period `t ≥ 1` by policy `π` under parameter `θ` and noise
realisation `ω` (at `t = 0` it returns `p₁`; no statement uses `t = 0`). -/
noncomputable def price {M : Model} {Ω : Type*} (π : Policy M) (θ : ℝ × ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  priceAux π θ ε ω (t - 1)

/-- The demand `D_t = α + β p_t + ε_t` realised in period `t ≥ 1`. -/
noncomputable def demand {M : Model} {Ω : Type*} (π : Policy M) (θ : ℝ × ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  θ.1 + θ.2 * price π θ ε t ω + ε t ω

end KeskinZeevi.SufficientConditions


