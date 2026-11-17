-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_Aq
-- name    : NoPerfectRandComp_Supplement_Aq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:10:34.013918+00:00
-- url     : https://prove2.me/theorems/95d464ac-aa14-4580-87f2-afa1e51343b0
-- title:
--   Helper $A_q = \mathrm{AND}_{q^2}\circ\mathrm{Maj}_q^{q^2}$
-- statement:
--   The helper function of §10.3 is
--   $$
--   A_q = \mathrm{AND}_{q^2}\circ\mathrm{Maj}_q^{q^2},
--   $$
--   an AND of $q^2$ disjoint majorities of $q$ bits each; a total function on $q^3$ bits.
--
--   **Formalization Note** The composition is the published `OAI.Paper320.compose`.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 10.5, p.52

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_maj
import Definitions.Def_NoPerfectRandComp_Supplement_andF

namespace NoPerfectRandComp

namespace Supplement

/-- The helper `A_q = AND_{q²} ∘ Maj_q^{q²}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Lemma 10.5, p.52): `q²` disjoint
majorities of `q` bits each, fed into an AND; a total function on `q³` bits.

**Formalization Note** The composition is the published `OAI.Paper320.compose`. -/
def Aq (q : ℕ) : (Fin (q ^ 2) × Fin q → Bool) → Bool :=
  OAI.Paper320.compose (andF (q ^ 2)) (maj q)

end Supplement

end NoPerfectRandComp


