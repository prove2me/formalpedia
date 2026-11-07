-- Prove2me | Definitions.Def_PrivLittlestone_contInput
-- name    : PrivLittlestone_contInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:59.240118+00:00
-- url     : https://prove2.me/theorems/b34d0bfd-2104-40f5-8cc2-2cea6e55563e
-- title:
--   Record on the continuation with a fixed aggregate
-- statement:
--   The record supplied by an input strategy at round $t$ on the **continuation with a fixed aggregate** $g$ from the phase start $t_0$: "the relevant future inputs" of (A2), and the "paired future records" of the proof of Lemma B.2.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), (A2), p.7; proof of Lemma B.2, p.22

import Mathlib
import Definitions.Def_PrivLittlestone_InputStrategy
import Definitions.Def_PrivLittlestone_contPrefix

namespace PrivLittlestone

/-- The record supplied at round `t` on the **continuation with a fixed aggregate** `g` from the
phase-start round `t₀` (He–He, *Private Online Learning of Littlestone Classes and Matroid
Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), (A2), p.7: "the relevant future
inputs"; proof of Lemma B.2, p.22: "this determines paired future records recursively"). -/
def contInput {X : Type*} {T : ℕ} (inp : InputStrategy X T) (past : Fin T → X → Bool) (t₀ : ℕ)
    (g : X → Bool) (t : Fin T) : X × Bool :=
  inp t (contPrefix past t₀ g t)

end PrivLittlestone


