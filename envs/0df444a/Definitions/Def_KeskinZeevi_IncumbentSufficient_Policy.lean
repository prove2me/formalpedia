-- Prove2me | Definitions.Def_KeskinZeevi_IncumbentSufficient_Policy
-- name    : KeskinZeevi_IncumbentSufficient_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:24:18.125595+00:00
-- url     : https://prove2.me/theorems/e6f47a32-04f9-4842-b12d-2cf83bbfb38c
-- title:
--   Non-anticipating pricing policy and its price, deviation and demand processes
-- statement:
--   A **pricing policy** $\pi$ is a sequence of rules: the first price $p_1 = \pi_1$ is a constant in $[l,u]$, and for $t \ge 1$ the price of period $t+1$ is a measurable function of the history $H_t = (D_1, p_1, \dots, D_t, p_t)$ of past demands and prices, with values in $[l,u]$. The policy does not know the slope $\beta$ or the shocks.
--
--   Under slope $\beta$ and shocks $\varepsilon$, the policy generates, period by period, the price $p_t$, the **price deviation** $x_t = p_t - \hat p$ and the demand
--   $$D_t = \hat D + \beta x_t + \varepsilon_t, \qquad t = 1, 2, \dots,$$
--   with $p_{t+1} = \pi_{t+1}(H_t)$.
--
--   **Formalization Note.** `Policy M` stores `rule t : (Fin t → ℝ × ℝ) → ℝ`, the price of period $t+1$ as a function of the $t$ past (demand, price) pairs, with measurability and range $[l,u]$ as fields; `rule 0` acts on the empty history and is $\pi_1$. `price π β ε t ω` is $p_t$ for $t \ge 1$, defined by recursion from the noise; this realizes the law of the sales process on the noise space $(\Omega, \mathbb P)$, so $\mathbb P^\pi_\beta$ and $\mathbb E^\pi_\beta$ become $\mathbb P$ and $\int \cdot\, d\mathbb P$. Periods are 1-based; at $t = 0$ the function returns $p_1$ and no statement uses that value. `dev` is $x_t$ and `demand` is $D_t$ as in (19).
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1145, Section 2 (policies, Eq. (5)), and p. 1148, Eq. (19)

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentSufficient_Model

namespace KeskinZeevi.IncumbentSufficient

/-- A deterministic non-anticipating pricing policy (Keskin–Zeevi 2014, p. 1145):
`rule t` maps the history `H_t = ((D₁, p₁), …, (D_t, p_t))` of the first `t` periods
(demand, price) to the price of period `t + 1`, measurably and into `[l, u]`. `rule 0` acts on the
empty history, so it is the constant first price `π₁`. The policy sees neither `β` nor the noise. -/
structure Policy (M : Model) where
  rule : (t : ℕ) → (Fin t → ℝ × ℝ) → ℝ
  measurable_rule : ∀ t, Measurable (rule t)
  rule_mem : ∀ t h, rule t h ∈ Set.Icc M.l M.u

/-- Internal 0-based recursion: `priceAux π β ε ω n` is the price of period `n + 1`, obtained by
feeding the realised history (demand `D̂ + β (p_s - p̂) + ε s`, price `p_s`) of periods
`1, …, n` into `π.rule n`. -/
noncomputable def priceAux {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ
  | n => π.rule n (fun i : Fin n =>
      (M.DHat + β * (priceAux π β ε ω i - M.pHat) + ε ((i : ℕ) + 1) ω, priceAux π β ε ω i))
termination_by n => n
decreasing_by exact i.isLt

/-- The price `p_t` charged in period `t ≥ 1` by policy `π` under slope `β` and noise
realisation `ω` (at `t = 0` it returns `p₁`; no statement uses `t = 0`). -/
noncomputable def price {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  priceAux π β ε ω (t - 1)

/-- The price deviation `x_t = p_t - p̂` from the incumbent price in period `t ≥ 1`. -/
noncomputable def dev {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  price π β ε t ω - M.pHat

/-- The demand `D_t = D̂ + β x_t + ε_t` realised in period `t ≥ 1` (Keskin–Zeevi 2014, (19)). -/
noncomputable def demand {M : Model} {Ω : Type*} (π : Policy M) (β : ℝ)
    (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.DHat + β * dev π β ε t ω + ε t ω

end KeskinZeevi.IncumbentSufficient


