-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_IsPolyTime
-- name    : KarpLiptonOM_OracleTM_IsPolyTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:59.939866+00:00
-- url     : https://prove2.me/theorems/739d4733-88e9-4989-8d2d-caf9e6cb1e40
-- title:
--   Polynomial running time $|w|^k + k$ with every oracle
-- statement:
--   An oracle machine **runs in polynomial time** (with exponent $k$) if, for every oracle language $O$ and every input $w$, it halts within $|w|^k + k$ steps. In particular a generator on input $1^n$ runs in time polynomial in $n$.
--
--   **Formalization Note** The bound is required for every oracle, as for clocked machines; this is not a restriction, since a polynomial-time machine can be clocked.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (machines run in polynomial time)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin

namespace KarpLiptonOM

/-- The oracle machine runs in polynomial time: with **every** oracle language `O` it halts on every
input `w` within `|w|^k + k` steps (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20: "Machines run in time polynomial in the
length of their input, which is `n` for a tally input `1ⁿ`").

**Formalization Note** The bound holds for every oracle, not only the consistent ones (clocked
machines), and has the form `|w|^k + k` of the published `CookPvsNP.P`. -/
def OracleTM.IsPolyTime (M : OracleTM) (k : ℕ) : Prop :=
  ∀ (O : Set (List Bool)) (w : List (Option Bool)), M.HaltsWithin O (w.length ^ k + k) w

end KarpLiptonOM


