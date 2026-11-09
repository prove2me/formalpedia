-- Prove2me | Definitions.Def_OracleStateHSP_K
-- name    : OracleStateHSP_K
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:28.459301+00:00
-- url     : https://prove2.me/theorems/df31aa9c-3994-4666-b458-32241c312813
-- title:
--   The padding group $K = \mathbb Z_2^r$
-- statement:
--   $K = \mathbb Z_2^r$, $r \ge 0$, the padding group of the Padded Simon's problems.
--
--   **Formalization Note** `Fin r → ZMod 2`.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.8, p.37

import Mathlib

namespace OracleStateHSP

/-- The padding group `K = Z_2^r` of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 4.8, p.37.

**Formalization Note.** `Z_2` is `ZMod 2`. -/
abbrev K (r : ℕ) : Type := Fin r → ZMod 2

end OracleStateHSP


