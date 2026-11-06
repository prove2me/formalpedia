-- Prove2me | Definitions.Def_DelayedGamesMAO_remWeight
-- name    : DelayedGamesMAO_remWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:32.684077+00:00
-- url     : https://prove2.me/theorems/df0f9add-d667-4107-9d39-1702aa9c1e49
-- title:
--   Remaining weight $r^{(t)}_s=(\gamma+\eta_s\alpha^{(t)}_s)\mathbb 1\{s\in A_t\}$
-- statement:
--   Given a delay sequence, $\gamma>0$, learning rates $(\eta_s)$ and an allocation schedule $\alpha$, the **remaining weight** of anchor $w_s$ at time $t$ is
--   $$
--   r^{(t)}_s=\bigl(\gamma+\eta_s\alpha^{(t)}_s\bigr)\,\mathbb 1\{s\in A_t\},\qquad 1\le s\le t\le T+1,\ s\le T .
--   $$
--   The constant $\gamma$ keeps the weight strictly positive while round $s$ is active.
--
--   **Formalization Note** The function is total in $(t,s)$; only the paper's range is read.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, pp.10–11

import Mathlib
import Definitions.Def_DelayedGamesMAO_active

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Remaining weight** `r_s^{(t)} := (γ + η_s α_s^{(t)}) 𝟙{s ∈ A_t}`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, pp.10–11: "given `γ > 0` and any nondecreasing sequence `0 = η_1 ≤ ⋯ ≤ η_{T+1}`, we
define `r_s^{(t)} := (γ + η_s α_s^{(t)}) I{s ∈ A_t}` for every `1 ≤ s ≤ t ≤ T + 1` with `s ≤ T`".

`remWeight d γ η α t s` is `r_s^{(t)}`; `α t s` is `α_s^{(t)}` and `η s` is `η_s`.

**Formalization Note.** Total in `t, s`; only `1 ≤ s ≤ t ≤ T + 1`, `s ≤ T` is read. -/
noncomputable def remWeight (d : ℕ → ℕ) (γ : ℝ) (η : ℕ → ℝ) (α : ℕ → ℕ → ℝ) (t s : ℕ) : ℝ :=
  if s ∈ active d t then γ + η s * α t s else 0

end DelayedGamesMAO


