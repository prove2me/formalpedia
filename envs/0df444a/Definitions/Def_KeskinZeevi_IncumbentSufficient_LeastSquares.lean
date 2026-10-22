-- Prove2me | Definitions.Def_KeskinZeevi_IncumbentSufficient_LeastSquares
-- name    : KeskinZeevi_IncumbentSufficient_LeastSquares
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T14:35:27.243756+00:00
-- url     : https://prove2.me/theorems/a7f836d9-b4f7-4e8c-9d9e-4e82fe52dc02
-- title:
--   Information metric, least squares slope estimate, truncated estimate and the events A_t
-- statement:
--   Along the price path of a policy, define the **information metric**, the **least squares estimate** of the slope and the **noise sum**
--   $$\hat J_t = \sum_{s=1}^t x_s^2, \qquad \hat\beta_t = \frac{\sum_{s=1}^t (D_s - \hat D)\, x_s}{\sum_{s=1}^t x_s^2}, \qquad M_t = \sum_{s=1}^t \varepsilon_s x_s .$$
--   The **truncated estimate** at the end of period $t$ is $b_t = b_{\min} \vee (\hat\beta_t \wedge b_{\max}) \in \mathfrak B$. For a slope $\beta$ and $t \ge 1$ the event
--   $$A_t = \bigcap_{s=\lfloor (t-1)/2 \rfloor}^{t-1} \Big\{ (\psi(\beta) - \psi(b_s))^2 \le \frac{(\psi(\beta))^2}{12} \Big\}$$
--   says that the greedy prices computed over the second half of the first $t - 1$ periods were all close to optimal.
--
--   **Formalization Note.** `Jhat`, `betaHat`, `noiseSum`, `truncEst` and `goodEvent` take the policy, the true slope $\beta$ (which drives the demand), the noise and the period. When $\hat J_t = 0$ the paper's $\hat\beta_t$ is undefined; Lean's convention $a/0 = 0$ gives $\hat\beta_t = 0$ and hence $b_t = b_{\max}$. The statements of this mission either exclude that case or use $b_t$ only where $\hat J_t > 0$. In `goodEvent` the lower index $\lfloor (t-1)/2 \rfloor$ is natural-number division; for $t \le 2$ it is $0$ and involves $b_0$, which the paper defines only for greedy ILS, so the statements use $A_t$ only for $t \ge 3$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1149 (Ĵ_t, after Eq. (24)), p. 1150 (Eqs. (26)-(27), truncated estimate), p. 1159 (Eq. (A15))

import Mathlib
import Definitions.Def_KeskinZeevi_IncumbentSufficient_Policy

namespace KeskinZeevi.IncumbentSufficient

variable {M : Model} {Ω : Type*}

/-- The information metric `Ĵ_t = Σ_{s=1}^t x_s²` (Keskin–Zeevi 2014, p. 1149, after (24)). -/
noncomputable def Jhat (π : Policy M) (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, dev π β ε s ω ^ 2

/-- The least squares estimate `β̂_t = Σ_{s=1}^t (D_s - D̂) x_s / Σ_{s=1}^t x_s²`
(Keskin–Zeevi 2014, (26)). When `Ĵ_t = 0` Lean's `x / 0 = 0` gives `β̂_t = 0`; the paper leaves
this case undefined. -/
noncomputable def betaHat (π : Policy M) (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (∑ s ∈ Finset.Icc 1 t, (demand π β ε s ω - M.DHat) * dev π β ε s ω) / Jhat π β ε t ω

/-- The noise sum `M_t = Σ_{s=1}^t ε_s x_s` (Keskin–Zeevi 2014, after (27)). -/
noncomputable def noiseSum (π : Policy M) (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ s ∈ Finset.Icc 1 t, ε s ω * dev π β ε s ω

/-- The truncated estimate `b_t = b_min ∨ (β̂_t ∧ b_max)` computed at the end of period `t`
(Keskin–Zeevi 2014, p. 1150). -/
noncomputable def truncEst (π : Policy M) (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  M.truncate (betaHat π β ε t ω)

/-- The event `A_t = ⋂_{s=⌊(t-1)/2⌋}^{t-1} {(ψ(β) - ψ(b_s))² ≤ ψ(β)²/12}` of
Keskin–Zeevi 2014, (A15), p. 1159; `(t - 1) / 2` is natural-number division, i.e. the floor. -/
def goodEvent (π : Policy M) (β : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) : Set Ω :=
  {ω | ∀ s ∈ Finset.Icc ((t - 1) / 2) (t - 1),
    (M.psi β - M.psi (truncEst π β ε s ω)) ^ 2 ≤ M.psi β ^ 2 / 12}

end KeskinZeevi.IncumbentSufficient


