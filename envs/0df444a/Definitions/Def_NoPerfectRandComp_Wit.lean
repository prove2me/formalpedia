-- Prove2me | Definitions.Def_NoPerfectRandComp_Wit
-- name    : NoPerfectRandComp_Wit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:22.551193+00:00
-- url     : https://prove2.me/theorems/a59f7757-d0b5-4a27-95af-e174f9e0adc2
-- title:
--   Tagged witness alphabet $W_q = [u]^{[u]}\sqcup[u]$
-- statement:
--   A witness for the value one of the core specifies a column in each row, and a witness for the value zero specifies one row. The **tagged witness alphabet** is
--   $$
--   W_q = [u]^{[u]} \sqcup [u] .
--   $$
--
--   **Formalization Note** $[u]$ is `Fin u` (0-based).
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §4.2, p.13

import Mathlib

namespace NoPerfectRandComp

/-- The tagged witness alphabet `W_q = [u]^{[u]} ⊔ [u]` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §4.2, p.13): a witness for
value one names a column in each row (`Sum.inl col`); a witness for value zero names one row
(`Sum.inr i`). -/
abbrev Wit (u : ℕ) : Type := (Fin u → Fin u) ⊕ Fin u

end NoPerfectRandComp


