-- Prove2me | Definitions.Def_CompNonlocal_Supplement_Game_IsPublic
-- name    : CompNonlocal_Supplement_Game_IsPublic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:09:14.687201+00:00
-- url     : https://prove2.me/theorems/6f4aad0c-2aa5-4863-9bce-91de169e1735
-- title:
--   Public verification
-- statement:
--   A game has **public verification** if the question generation retains no private register: at every security parameter $Q$ outputs only the classical questions $(x,y)$, so the score is computed from $(a,b,x,y)$ alone.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), §11.1, p.63; Theorem 10, p.66; Theorem 11, p.69

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_Game

set_option autoImplicit false

namespace CompNonlocal.Supplement

/-- Public verification. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), §11.1, p.63: "suppose verification is public: the score can be
efficiently sampled from (x, y, a, b), without retained private information"; Theorem 10, p.66 and
Theorem 11, p.69 ("public-verification certificate"): the question generation retains no private
register `td` (its quantum output is empty at every `κ`), so Val reads only `(a, b, x, y)`. -/
def Game.IsPublic (G : Game) : Prop :=
  ∀ κ : ℕ, (G.Qg κ).outQ = []

end CompNonlocal.Supplement


