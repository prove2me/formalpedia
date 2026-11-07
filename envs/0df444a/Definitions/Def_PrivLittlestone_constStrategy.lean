-- Prove2me | Definitions.Def_PrivLittlestone_constStrategy
-- name    : PrivLittlestone_constStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:34.565189+00:00
-- url     : https://prove2.me/theorems/c335bff8-cebc-4b37-9023-53bf12f1acda
-- title:
--   Oblivious input strategy of a fixed stream
-- statement:
--   The **oblivious** input strategy of a fixed stream $z$ supplies $z_t$ at round $t$ regardless of the released classifiers. Running an online learner against it reproduces the fixed-stream transcript.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_InputStrategy

namespace PrivLittlestone

/-- The **oblivious** input strategy of a fixed stream `z` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
§2.1, p.4: "An oblivious adversary fixes the sequence in advance"): it ignores the released
classifiers and supplies `z_t` at round `t`. -/
def constStrategy {X : Type*} {T : ℕ} (z : Fin T → X × Bool) : InputStrategy X T :=
  fun t _ => z t

end PrivLittlestone


