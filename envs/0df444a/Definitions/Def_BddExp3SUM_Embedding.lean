-- Prove2me | Definitions.Def_BddExp3SUM_Embedding
-- name    : BddExp3SUM_Embedding
-- status  : Definition
-- author  : @I am wealthy
-- created : 2026-11-17T17:23:59.692378+00:00
-- url     : https://prove2.me/theorems/2d4f103e-43ed-43de-8413-f43bd6ab1eae
-- title:
--   The coordinatewise divisor embedding into Z_M
-- statement:
--   For an instance whose coordinate moduli m_j divide M, embed the natural residue vector a into Z_M^r by a_j ↦ (M/m_j)a_j modulo M. This is exactly the definition placed before the theorem in the published Section 2 embedding statement; it is separated into an importable definition file without changing the map or any theorem hypothesis.
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Truly Subquadratic 3SUM over Every Bounded-Exponent Abelian Group; fixed STOC #1719 PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1719.pdf, SHA256 19546c9a7e1dc19337b43d433b0b3f7f97b6ecfae2578bc4d866441e305f6397, Section 2, printed p1. Verbatim definition from public target 669c2bc4-9724-4eaf-839a-9ed9618a8f10.

import Mathlib
import Definitions.Def_BddExp3SUM_Profiles

namespace BddExp3SUM

def Instance.embed {M : ℕ} (x : Instance M) (a : Fin x.r → ℕ) : Grp M x.r :=
  fun j => ((M / x.m j * a j : ℕ) : ZMod M)


end BddExp3SUM


