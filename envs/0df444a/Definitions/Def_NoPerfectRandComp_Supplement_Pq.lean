-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_Pq
-- name    : NoPerfectRandComp_Supplement_Pq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:08:59.671712+00:00
-- url     : https://prove2.me/theorems/6142dd99-942e-4fdb-9eea-729c3aef5371
-- title:
--   Parity family $P_q = \mathrm{XOR}_q\circ g_q^q$
-- statement:
--   The **parity family** is the block composition
--   $$
--   P_q = \mathrm{XOR}_q\circ g_q^q,
--   $$
--   in which $q$ disjoint copies of the Blais–Brody block $g_q$ are fed into parity on $q$ bits; a total function on $N_q = q\,m_q$ bits.
--
--   **Formalization Note** The composition is the published `OAI.Paper320.compose`.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 6.2, p.29

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_Supplement_xorF
import Definitions.Def_NoPerfectRandComp_Supplement_gq

namespace NoPerfectRandComp

namespace Supplement

/-- The parity family `P_q = XOR_q ∘ g_q^q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Theorem 6.2, p.29): `q` disjoint
copies of the block `g_q` fed into `XOR_q`; a total function on `N_q = q m_q` bits.

**Formalization Note** The composition is the published `OAI.Paper320.compose`. -/
def Pq (q C : ℕ) (ϕ : (Fin C → Bool) → PtrCell q) :
    (Fin q × (Fin q × Fin q × Fin C) → Bool) → Bool :=
  OAI.Paper320.compose (xorF q) (gq q C ϕ)

end Supplement

end NoPerfectRandComp


