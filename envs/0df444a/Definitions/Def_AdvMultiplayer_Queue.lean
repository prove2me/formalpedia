-- Prove2me | Definitions.Def_AdvMultiplayer_Queue
-- name    : AdvMultiplayer_Queue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:55.431312+00:00
-- url     : https://prove2.me/theorems/3883f107-2fa8-4ccd-8af6-f7586ca52284
-- title:
--   Weights, quantized arrivals, capped service and $\psi_{h}$
-- statement:
--   A score $z$ has weight $(1+1/D)^z$. A recording of arm $i$ with observation $y$ and rate $\xi$ gives the integer arrival $\Delta=\lfloor D\eta y/\xi\rfloor$. A queue $\mathsf B$ with arrival $\Delta$ is served by
--   $$\Gamma=\min\{4\eta D,\mathsf B+\Delta\},\qquad \mathsf B'=\mathsf B+\Delta-\Gamma.$$
--   A saved observation contributes $\psi_{h'}(y,v)=\mathbf 1\{v\le 4dK2^{-h'}/\zeta\}\lfloor D\eta2^{h'}y\rfloor$.
--
--   These integer updates are shared by the logical learner and the physical protocol.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 3.2, (10), (11), p.14; (30), p.28

import Mathlib
import Definitions.Def_AdvMultiplayer_Size

namespace AdvMultiplayer

variable (p : Size)

/-- The weight `(1+1/D)^z` of a score `z` (p.14). -/
noncomputable def weightOf (z : ℕ) : ℝ := (1 + 1 / (p.D : ℝ)) ^ z

/-- **The integer arrival** `Δ_t(i) = ⌊D η r_t(i)/ξ_i⌋` on `I_t = i` (10), (11), p.14. Gan,
arXiv:2610.05688, Section 3.2. The quantized estimate is `r̃_t(i) = Δ_t(i)/(ηD)`.

**Formalization Note.** The module also holds the capped service (11), the backlog update and the
saved-observation contribution `ψ_{h'}` (30). Arrivals and queues are natural numbers: the
arguments of the floors are nonnegative on `[0,1]` rewards and positive rates. -/
noncomputable def arrivalOf (η ξ y : ℝ) : ℕ := ⌊(p.D : ℝ) * η * y / ξ⌋₊

/-- The service `Γ = min{cap, B + Δ}` of (11), p.14. -/
def serviceOf (cap B Δ : ℕ) : ℕ := min cap (B + Δ)

/-- The queue update `B' = B + Δ - Γ` of (11), p.14. -/
def queueNext (cap B Δ : ℕ) : ℕ := B + Δ - serviceOf cap B Δ

/-- One saved observation's contribution (30), p.28, for a rate `η`:
`ψ_{h'}(y,v) = 1{v ≤ 4dK 2^{-h'}/ζ} ⌊D η 2^{h'} y⌋`. -/
noncomputable def psiOf (η : ℝ) (h : ℕ) (y v : ℝ) : ℕ := by
  classical exact
    if v ≤ 4 * p.d * p.K * ((1 : ℝ) / 2) ^ h / p.zeta then ⌊(p.D : ℝ) * η * 2 ^ h * y⌋₊ else 0

end AdvMultiplayer


