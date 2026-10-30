-- Prove2me | Definitions.Def_BartlettBousquetMendelson_LocalRad_IsNontrivialSubRoot
-- name    : BartlettBousquetMendelson_LocalRad_IsNontrivialSubRoot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:58:21.868983+00:00
-- url     : https://prove2.me/theorems/52976e83-d935-4810-a151-f688daa6d2d9
-- title:
--   Nontrivial sub-root function
-- statement:
--   A sub-root function $\psi$ is **nontrivial** if it is not the constant function $\psi\equiv0$, i.e. $\psi(r)\ne0$ for some $r\ge0$. The paper only considers nontrivial sub-root functions (p. 9).
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), p. 9, sentence after Definition 3.1 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsSubRoot

namespace BartlettBousquetMendelson.LocalRad

/-- **Nontrivial sub-root function.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), p. 9, the sentence after Definition 3.1: "We only consider nontrivial sub-root functions,
that is, sub-root functions that are not the constant function ψ ≡ 0."

`IsNontrivialSubRoot ψ` says `ψ` is sub-root (`IsSubRoot`) and `ψ r ≠ 0` for some `r ≥ 0`.

**Formalization Note.** The paper calls every sub-root function it uses nontrivial (p. 9); the
statements of the mission assume `IsNontrivialSubRoot` wherever the paper says "sub-root"
together with a fixed point. -/
def IsNontrivialSubRoot (ψ : ℝ → ℝ) : Prop :=
  IsSubRoot ψ ∧ ∃ r, 0 ≤ r ∧ ψ r ≠ 0

end BartlettBousquetMendelson.LocalRad


