-- Prove2me | Definitions.Def_OracleStateHSP_FlagQ
-- name    : OracleStateHSP_FlagQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:36.19924+00:00
-- url     : https://prove2.me/theorems/03ae1594-2bc4-42da-b5cd-0339bafa1227
-- title:
--   Query register of the family: flag, group and answer registers
-- statement:
--   The query register $\mathcal H_S$ of the Fractional Padded Simon family has the computational basis
--   $$
--   \{0, 1\} \times (\mathbb Z_2^r \times \mathbb Z_2^m) \times \mathbb Z_2^m ,
--   $$
--   a flag qubit, the group register for $G = \mathbb Z_2^r \oplus \mathbb Z_2^m$, and the answer register.
--
--   **Formalization Note** The flag is the outer index.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.3, eq. (55), p.39

import Mathlib
import Definitions.Def_OracleStateHSP_V
import Definitions.Def_OracleStateHSP_K

namespace OracleStateHSP

/-- The basis of the query register `H_S` of the Fractional Padded Simon family (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, §4.3,
eq. (55), p.39): a flag qubit, the group register `G = Z_2^r ⊕ Z_2^m`, and the answer register
`Z_2^m`.

**Formalization Note.** The flag is the outer index; `Z_2^n` is `Z_2^r × Z_2^m`. -/
abbrev FlagQ (r m : ℕ) : Type := Fin 2 × ((K r × V m) × V m)

end OracleStateHSP


