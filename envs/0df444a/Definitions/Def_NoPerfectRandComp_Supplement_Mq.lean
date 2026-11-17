-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_Mq
-- name    : NoPerfectRandComp_Supplement_Mq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:08:29.969141+00:00
-- url     : https://prove2.me/theorems/dc648b50-3c48-47e5-9196-ce1640c18647
-- title:
--   Majority family $M_q = \mathrm{Maj}_q\circ g_q^q$
-- statement:
--   The **majority family** is the block composition
--   $$
--   M_q = \mathrm{Maj}_q\circ g_q^q,
--   $$
--   in which $q$ disjoint copies of the Blais–Brody block $g_q$ (each on $m_q = q^2C$ bits) are fed into majority on $q$ bits. It is a total function on $N_q = q\,m_q$ bits.
--
--   **Formalization Note** The composition is the published block composition `OAI.Paper320.compose`; block $i$ is the coordinate set $\{i\}\times([q]\times[q]\times[C])$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 3.5, p.10

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_maj
import Definitions.Def_NoPerfectRandComp_Supplement_gq

namespace NoPerfectRandComp

namespace Supplement

/-- The majority family `M_q = Maj_q ∘ g_q^q` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Theorem 3.5, p.10): `q` disjoint
copies of the block `g_q` (on `m_q = q² C` bits each) fed into `Maj_q`; a total function on
`N_q = q m_q` bits. Block `i` is the coordinate set `{i} × ([q] × [q] × [C])`.

**Formalization Note** The composition is the published block composition
`OAI.Paper320.compose`, as in the base mission's `PartialFn.comp`. -/
def Mq (q C : ℕ) (ϕ : (Fin C → Bool) → PtrCell q) :
    (Fin q × (Fin q × Fin q × Fin C) → Bool) → Bool :=
  OAI.Paper320.compose (maj q) (gq q C ϕ)

end Supplement

end NoPerfectRandComp


