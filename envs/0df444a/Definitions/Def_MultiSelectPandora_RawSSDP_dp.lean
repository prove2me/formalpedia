-- Prove2me | Definitions.Def_MultiSelectPandora_RawSSDP_dp
-- name    : MultiSelectPandora_RawSSDP_dp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:35.709629+00:00
-- url     : https://prove2.me/theorems/7536e113-a726-4d2a-a51c-46d511e63691
-- title:
--   The value function $\mathrm{DP}_t$
-- statement:
--   The value function, by Bellman's equation:
--   $$\mathrm{DP}_t(I_t,A_t)=\max_{a_t\in A_t}E\big[\mathrm{DP}_{t+1}(f(I_t,a_t),A_t\setminus\{a_t\})+g(I_t,a_t)\big],\qquad \mathrm{DP}_{T+1}=h.$$
--
--   **Formalization Note** The first argument is the number of steps left, and the set of removed groups stands for $A_t$. A valid table always has an available action.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_outcomes
import Definitions.Def_MultiSelectPandora_RawSSDP_avail
import Definitions.Def_MultiSelectPandora_RawSSDP_after
import Definitions.Def_MultiSelectPandora_RawSSDP_terminal

namespace MultiSelectPandora

/-- **The value function `DP_t(I_t, A_t)`, by Bellman's equation.** Beyhaghi–Han–Luqman manuscript, p.8 (PDF p.9):
`DP_t(I_t, A_t) = max_{a_t ∈ A_t} E[DP_{t+1}(f(I_t, a_t), A_t \ {a_t}) + g(I_t, a_t)]`, with `DP_{T+1} = h`.

**Formalization Note.** The first argument is the number of steps left, and the removed groups stand for `A_t`. A valid program always
has an available action; with none, the value is the terminal reward. -/
noncomputable def RawSSDP.dp (S : RawSSDP) : ℕ → ℕ → Finset ℕ → ℝ
  | 0, st, _ => S.terminal st
  | t + 1, st, R =>
    if hA : ((Finset.range S.actions.length).filter fun a => S.avail R a = true).Nonempty then
      ((Finset.range S.actions.length).filter fun a => S.avail R a = true).sup' hA fun a =>
        ((S.outcomes a st).map fun o => (o.1 : ℝ) * ((o.2.1 : ℝ) + S.dp t o.2.2 (S.after R a))).sum
    else S.terminal st

end MultiSelectPandora


