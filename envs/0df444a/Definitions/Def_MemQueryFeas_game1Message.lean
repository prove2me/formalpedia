-- Prove2me | Definitions.Def_MemQueryFeas_game1Message
-- name    : MemQueryFeas_game1Message
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:32.377133+00:00
-- url     : https://prove2.me/theorems/5ca1ab30-eabe-4121-b5cd-ccd22764f9ad
-- title:
--   The message of Game 1
-- statement:
--   The message is $\mathrm{Message}=\mathrm{enc}(E^{(\le i)},U_{enc})$: the encoder's output on the versions with index at most $i$ and its private randomness.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Game 1, line 2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_MemQueryFeas_truncSeq

namespace MemQueryFeas

/-- **The message of Game 1.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Game 1, line 2, p.12 (PDF p.13): "Encoder: Observe `E^(≤i)` and
store a message Message about these."

`game1Message enc i ch Uenc ω = enc (E^(≤i)(ω), Uenc ω)`, where `E^(≤i) = truncSeq (i+1) ch`. -/
def game1Message {Ω A Mes : Type*} {d : ℕ} (enc : (ℕ → Op d) × A → Mes) (i : ℕ)
    (ch : ℕ → Ω → Op d) (Uenc : Ω → A) : Ω → Mes :=
  fun ω => enc (truncSeq (i + 1) (fun j => ch j ω), Uenc ω)

end MemQueryFeas


