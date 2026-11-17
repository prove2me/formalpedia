-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_Hq
-- name    : NoPerfectRandComp_Supplement_Hq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:11:14.919431+00:00
-- url     : https://prove2.me/theorems/154a94ea-3f4d-4a60-b90f-01e9777f2503
-- title:
--   Rotated family $H_q = g_q\circ A_q^{m_q}$
-- statement:
--   The function of Theorem 10.7 is the block composition
--   $$
--   H_q = g_q\circ A_q^{m_q}:
--   $$
--   the outer function is the Blais–Brody block $g_q$ on $m_q = q^2C$ bits, and an independent copy of the helper $A_q$ (on $q^3$ bits) computes each of its $m_q$ input bits. It is total on $N_q = q^3 m_q$ bits.
--
--   **Formalization Note** The composition is the published `OAI.Paper320.compose`, with $g_q$ outside and $A_q$ inside.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), p.53

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_Supplement_gq
import Definitions.Def_NoPerfectRandComp_Supplement_Aq

namespace NoPerfectRandComp

namespace Supplement

/-- The rotated family `H_q = g_q ∘ A_q^{m_q}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.53): the outer function is the
block `g_q` on `m_q = q² C` bits, and an independent copy of the helper `A_q` (on `q³` bits) sits
at every one of its `m_q` input bits; a total function on `N_q = q³ m_q` bits.

**Formalization Note** The composition is the published `OAI.Paper320.compose`; outer `g_q`,
inner `A_q` (the other rotation `F_q = A_q ∘ g_q^{q³}` appears only in the paper's proofs). -/
def Hq (q C : ℕ) (ϕ : (Fin C → Bool) → PtrCell q) :
    ((Fin q × Fin q × Fin C) × (Fin (q ^ 2) × Fin q) → Bool) → Bool :=
  OAI.Paper320.compose (gq q C ϕ) (Aq q)

end Supplement

end NoPerfectRandComp


