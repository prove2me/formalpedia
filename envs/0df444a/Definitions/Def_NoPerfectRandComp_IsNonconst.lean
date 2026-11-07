-- Prove2me | Definitions.Def_NoPerfectRandComp_IsNonconst
-- name    : NoPerfectRandComp_IsNonconst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:04.966947+00:00
-- url     : https://prove2.me/theorems/e6d63ea0-ba9f-4e7b-84dd-0570f7c05ff0
-- title:
--   Nonconstant Boolean function
-- statement:
--   A total Boolean function $f$ is **nonconstant** when it takes both values: there are inputs $x, y$ with $f(x) \ne f(y)$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Theorem 1.1, p.1

import Mathlib

namespace NoPerfectRandComp

/-- A total Boolean function is nonconstant when it takes both values (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), Theorem 1.1, p.1). -/
def IsNonconst {ι : Type} (f : (ι → Bool) → Bool) : Prop :=
  ∃ x y, f x ≠ f y

end NoPerfectRandComp


