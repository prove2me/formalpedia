-- Prove2me | Definitions.Def_NoPerfectRandComp_Bq__ccb8cb
-- name    : NoPerfectRandComp_Bq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:32.189525+00:00
-- url     : https://prove2.me/theorems/ccb8cb1e-8e04-42c7-bd66-73e03881c5a4
-- title:
--   Composed-seed cost $B_q = k_q(6q+2)\hat C_q + q^3\hat C_q$
-- statement:
--   The worst-case cost of the composed-seed algorithm of Lemma 5.10 is
--   $$
--   B_q = k_q\,(6q+2)\,\hat C_q + q^3\,\hat C_q ,
--   $$
--   that is, $k_q$ weak evaluations of the inner function plus one full read of an inner input.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (27), p.24

import Mathlib
import Definitions.Def_NoPerfectRandComp_kq
import Definitions.Def_NoPerfectRandComp_Chat

namespace NoPerfectRandComp

/-- The cost bound `B_q = k_q (6q + 2) Ĉ_q + q³ Ĉ_q` of the composed-seed algorithm
(Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (27), p.24). -/
def Bq (q : ℕ) : ℕ := kq q * (6 * q + 2) * Chat q + q ^ 3 * Chat q

end NoPerfectRandComp


