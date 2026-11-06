-- Prove2me | Definitions.Def_DelayedGamesMAO_beta
-- name    : DelayedGamesMAO_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:36.526297+00:00
-- url     : https://prove2.me/theorems/b7d4444f-2312-474c-8f64-7e9313cffd7b
-- title:
--   Inflated learning rate $\beta_t=\eta_t+\gamma Q_t$, $\beta_0=0$
-- statement:
--   Given a delay sequence, $\gamma>0$ and learning rates $(\eta_t)_{t\ge1}$, the **inflated learning rate** is
--   $$
--   \beta_t=\eta_t+\gamma Q_t\quad(t\ge1),\qquad \beta_0=0 .
--   $$
--   It is the total weight flowing through the anchors $w_1,\dots,w_t$.
--
--   **Formalization Note** $\beta_0=0$ is set explicitly (the paper's $\eta_0=Q_0=0$), so the value of the learning-rate sequence at index $0$ is never read.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, p.11; proof of Lemma 5, p.19

import Mathlib
import Definitions.Def_DelayedGamesMAO_Qrun

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Inflated learning rate** `β_t := η_t + γ Q_t`, `β_0 := 0`.
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, p.11: "We then introduce `β_t := η_t + γQ_t`"; the proof of Lemma 5 (p.19) uses
`β_0 = 0`.

**Formalization Note.** The learning rates `η` are given for `t ≥ 1`; `β_0 = 0` is set
explicitly (the paper's `η_0 = 0`, `Q_0 = 0`), so the value `η 0` of the given sequence is
never read. -/
noncomputable def beta (d : ℕ → ℕ) (γ : ℝ) (η : ℕ → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then 0 else η t + γ * (Qrun d t : ℝ)

end DelayedGamesMAO


