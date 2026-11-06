-- Prove2me | Definitions.Def_MemQueryFeas_game1Output
-- name    : MemQueryFeas_game1Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:37:01.372653+00:00
-- url     : https://prove2.me/theorems/d67257e8-d649-43e6-b580-6c23c23aba12
-- title:
--   The decoder's output in Game 1
-- statement:
--   The decoder's output is $\mathrm{dec}(\mathrm{Message},E^{(\le i-1)},U_{dec})\in(\mathbb R^d)^k$: it sees only the message, the versions with index at most $i-1$ and its private randomness.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Game 1, line 3, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_MemQueryFeas_game1Message

namespace MemQueryFeas

/-- **The decoder's output in Game 1.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Game 1, line 3, p.12 (PDF p.13): "Decoder: Based on
Message and `E^(≤i−1)` only, return nonzero vectors `x_1, …, x_k`."

`game1Output enc dec i ch Uenc Udec ω = dec (Message(ω), E^(≤i−1)(ω), Udec ω)`, where
`E^(≤i−1) = truncSeq i ch`. -/
def game1Output {Ω A B Mes : Type*} {d k : ℕ} (enc : (ℕ → Op d) × A → Mes)
    (dec : Mes × (ℕ → Op d) × B → (Fin k → Vec d)) (i : ℕ) (ch : ℕ → Ω → Op d) (Uenc : Ω → A)
    (Udec : Ω → B) : Ω → (Fin k → Vec d) :=
  fun ω => dec (game1Message enc i ch Uenc ω, truncSeq i (fun j => ch j ω), Udec ω)

end MemQueryFeas


