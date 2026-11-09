-- Prove2me | Definitions.Def_OracleStateHSP_V
-- name    : OracleStateHSP_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:25.699467+00:00
-- url     : https://prove2.me/theorems/41eabdd7-0d67-478e-9270-5b02f0478dfb
-- title:
--   The group $V = \mathbb Z_2^m$
-- statement:
--   $V = \mathbb Z_2^m$, the $m$-bit strings with bitwise addition modulo $2$ (XOR).
--
--   **Formalization Note** $\mathbb Z_2$ is `ZMod 2` and $V$ is the function type `Fin m → ZMod 2`.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.2.1, p.36; Definition 4.8, p.37

import Mathlib

namespace OracleStateHSP

/-- The group `V = Z_2^m` of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, §4.2.1, p.36, and Definition 4.8, p.37.

**Formalization Note.** `Z_2` is `ZMod 2`, so `+` on `V` is bitwise XOR. -/
abbrev V (m : ℕ) : Type := Fin m → ZMod 2

end OracleStateHSP


