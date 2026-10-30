-- Prove2me | Definitions.Def_HolevoCQ_avgState
-- name    : HolevoCQ_avgState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:38.487674+00:00
-- url     : https://prove2.me/theorems/9b50ec69-17c0-4ae1-b8b2-c5f3046321b8
-- title:
--   Average state $\bar S=\sum_i \pi_i S_i$
-- statement:
--   For signal states $S_i$, $i\in A$, and an a priori distribution $\pi=\{\pi_i\}$ on the finite alphabet $A$, the average state is
--
--   $$
--   \bar S=\sum_{i\in A}\pi_i S_i .
--   $$
--
--   It is the state received when the input letter is drawn from $\pi$, and its entropy is the first term of the entropy bound $\Delta H(\pi)$.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, §2, p.2

import Mathlib

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, §2, p.2: the average state `S̄ = Σ_{i∈A} π_i S_i` of the signal
states under the a priori distribution `π`. -/
noncomputable def avgState {A D : Type} [Fintype A] (S : A → Matrix D D ℂ) (π : A → ℝ) :
    Matrix D D ℂ :=
  ∑ i, ((π i : ℝ) : ℂ) • S i

end HolevoCQ


