-- Prove2me | Definitions.Def_DelayedGamesMAO_IsTuning
-- name    : DelayedGamesMAO_IsTuning
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:37.069222+00:00
-- url     : https://prove2.me/theorems/47d5ec30-2fcd-40d6-b08f-1acd0b04299c
-- title:
--   The adaptive tuning (9) of the learning rates
-- statement:
--   Given a delay sequence, a horizon $T$, constants $M,\gamma$, a schedule $\alpha$, gradients $(g_s)$ and hints $(h_s)$, a sequence $(\eta_t)$ follows the **tuning (9)** if $\eta_1=0$ and, for every $t\in[T]$,
--   $$
--   \eta_{t+1}=\eta_t+\frac1M\sum_{s\in N_t}\frac{\|g_s-h_s\|_*^2}{\gamma+\eta_s\alpha^{(t)}_s}.
--   $$
--   The update uses only feedback observed by the end of round $t$, and it determines $\eta_1,\dots,\eta_{T+1}$ uniquely.
--
--   **Formalization Note** The recursion is stated as a property of a given sequence. The norm of a dual vector is the operator norm, i.e. the dual norm $\|\cdot\|_*$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, eq. (9), p.12

import Mathlib
import Definitions.Def_DelayedGamesMAO_newObs

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **The adaptive tuning** (9) of the learning rates:
`η_1 = 0` and `η_{t+1} = η_t + (1/M) ∑_{s∈N_t} ‖g_s − h_s‖_*² / (γ + η_s α_s^{(t)})` for `t ∈ [T]`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, eq. (9), p.12, with `η_1 = 0` from Algorithm 1's input "`0 = η_1 ≤ ⋯ ≤ η_{T+1}`".

**Formalization Note.** (9) determines `η_1, …, η_{T+1}` uniquely (each `s ∈ N_t` has `s ≤ t`);
the predicate states it as a recursion on a given sequence `η`. `‖·‖` on `E →L[ℝ] ℝ` is the
operator norm, i.e. the dual norm `‖·‖_*`. -/
def IsTuning {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ → ℕ) (T : ℕ)
    (M γ : ℝ) (α : ℕ → ℕ → ℝ) (g h : ℕ → E →L[ℝ] ℝ) (η : ℕ → ℝ) : Prop :=
  η 1 = 0 ∧ ∀ t ∈ Finset.Icc 1 T,
    η (t + 1) = η t + (1 / M) * ∑ s ∈ newObs d t, ‖g s - h s‖ ^ 2 / (γ + η s * α t s)

end DelayedGamesMAO


