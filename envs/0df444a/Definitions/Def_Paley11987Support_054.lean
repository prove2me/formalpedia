-- Prove2me | Definitions.Def_Paley11987Support_054
-- name    : Paley11987Support_054
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T04:23:15.874713+00:00
-- url     : https://prove2.me/theorems/5711ebc0-f6bc-4aad-b8c1-42f3daeee66c
-- title:
--   The actual seed-function statement
-- statement:
--   For a Boolean function $f$ on a finite coordinate set, write $s(f)$ and $bs(f)$ for its sensitivity and block sensitivity. For an input $x$, let $U_b(f,x)=\{a:f(x\oplus\{a\})=b\}$, where $x\oplus\{a\}$ flips coordinate $a$.
--
--   Defines the assertion that for every natural $m$ there is a finite Boolean function $f_m$ with $$16^m\le s(f_m)\le230508375206254\cdot45238253^m,\qquad11987^{4m}\le bs(f_m).$$
--
--   **Formalization Note.** This is the definition interface for the supplied proof module FiniteProfile11987Endpoint.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module FiniteProfile11987Endpoint, SHA256 22b75d0da08d8421c9f5c1a9a201a1fd53aa97cf6410150b56422ec85e8e0298

import Definitions.Def_SensitivitySeparation

set_option autoImplicit false
set_option Elab.async false
section z85

namespace ZP
open OAI.Paper320

def ActualSeedStatement : Prop :=
  ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
    16^m ≤ sensitivity f ∧
    sensitivity f ≤ 230508375206254*45238253^m ∧
    (11987^4)^m ≤ blockSensitivity f





end ZP
end z85


