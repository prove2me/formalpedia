-- Prove2me | Definitions.Def_KarpLiptonOM_IsStrictLinearOn
-- name    : KarpLiptonOM_IsStrictLinearOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:27.537204+00:00
-- url     : https://prove2.me/theorems/f94b070f-7649-4968-897a-714e4e985514
-- title:
--   Strict linear order on $\{0,1\}^m$
-- statement:
--   A relation $\prec$ is a **strict linear order** on $\{0,1\}^m$ if, for all strings $u, v, w$ of length $m$:
--   1. $u \not\prec u$;
--   2. $u \prec v$ and $v \prec w$ imply $u \prec w$;
--   3. $u \ne v$ implies $u \prec v$ or $v \prec u$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definitions A.2.7 and A.2.9, pp.22–23

import Mathlib

namespace KarpLiptonOM

/-- `R` is a **strict linear order** on `{0,1}^m` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Definitions A.2.7, A.2.9, pp.22–23):
irreflexive, transitive and total on distinct strings of length `m`. -/
def IsStrictLinearOn (m : ℕ) (R : List Bool → List Bool → Prop) : Prop :=
  (∀ u, u.length = m → ¬ R u u) ∧
  (∀ u v w, u.length = m → v.length = m → w.length = m → R u v → R v w → R u w) ∧
  (∀ u v, u.length = m → v.length = m → u ≠ v → R u v ∨ R v u)

end KarpLiptonOM


