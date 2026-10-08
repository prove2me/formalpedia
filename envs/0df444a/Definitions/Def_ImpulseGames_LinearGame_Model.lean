-- Prove2me | Definitions.Def_ImpulseGames_LinearGame_Model
-- name    : ImpulseGames_LinearGame_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:45:14.323289+00:00
-- url     : https://prove2.me/theorems/2615b3d9-e1f3-4682-aeed-4de85b9acce9
-- title:
--   Constants and standing assumptions of the linear impulse game (Section 4.1)
-- statement:
--   The linear impulse game of Aïd, Basei, Callegaro, Campi and Vargiolu (Section 4.1) is described by eight real constants:
--
--   1. the volatility $\sigma$ of the uncontrolled state $x+\sigma W$;
--   2. the common discount rate $\rho$;
--   3. the targets $s_1, s_2$ of the running payoffs $f_1(x)=x-s_1$ and $f_2(x)=s_2-x$;
--   4. the fixed cost $c$ and proportional cost $\lambda$ paid by a player for an impulse $\delta$, so that the intervention penalty is $\phi(\delta)=-c-\lambda|\delta|$;
--   5. the fixed gain $\tilde c$ and proportional gain $\tilde\lambda$ received by the opponent, $\psi(\delta)=\tilde c+\tilde\lambda|\delta|$.
--
--   The **standing assumptions** of Section 4.1 are
--
--   $$\sigma>0,\quad \rho>0,\quad s_1<s_2,\quad c\ge\tilde c\ge0,\quad \lambda\ge\tilde\lambda\ge0,\quad (c,\lambda)\ne(\tilde c,\tilde\lambda),\quad 1-\lambda\rho>0 .$$
--
--   Every statement of the mission takes these constants and assumptions as its hypotheses.
--
--   **Formalization Note.** The constants are the fields of a structure `Model` (with `ct` for $\tilde c$ and `lamt` for $\tilde\lambda$); the assumptions are the fields of the proposition `Model.Standing`. The additional hypothesis $c>0$, used by every statement that involves the zero $\xi$ of (4.17), is stated separately in those statements.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Section 4.1, (4.1)-(4.2) (pp. 12-13)

import Mathlib

namespace ImpulseGames.LinearGame

/-- The constants of the linear impulse game of Section 4.1 (Aïd et al. 2020, pp. 12–13):
the volatility `σ` of the state `x + σ W`, the common discount rate `ρ`, the targets `s₁`, `s₂`
of the running payoffs `f₁(x) = x − s₁`, `f₂(x) = s₂ − x`, the fixed and proportional costs
`c`, `lam` paid by the intervening player, and the fixed and proportional gains `ct` (`c̃`),
`lamt` (`λ̃`) received by the opponent. -/
structure Model where
  σ : ℝ
  ρ : ℝ
  s₁ : ℝ
  s₂ : ℝ
  c : ℝ
  ct : ℝ
  lam : ℝ
  lamt : ℝ

/-- The standing assumptions of Section 4.1 (pp. 12–13): `σ > 0`, `ρ > 0`, `s₁ < s₂` (4.1),
`c ≥ c̃ ≥ 0`, `λ ≥ λ̃ ≥ 0`, `(c, λ) ≠ (c̃, λ̃)`, and `1 − λρ > 0` (4.2). -/
structure Model.Standing (M : Model) : Prop where
  σ_pos : 0 < M.σ
  ρ_pos : 0 < M.ρ
  s₁_lt_s₂ : M.s₁ < M.s₂
  ct_nonneg : 0 ≤ M.ct
  ct_le_c : M.ct ≤ M.c
  lamt_nonneg : 0 ≤ M.lamt
  lamt_le_lam : M.lamt ≤ M.lam
  costs_ne : (M.c, M.lam) ≠ (M.ct, M.lamt)
  one_sub_lam_mul_ρ_pos : 0 < 1 - M.lam * M.ρ

end ImpulseGames.LinearGame


