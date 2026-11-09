-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_Redundancy
-- name    : DeletionHash_MixedEdit_Redundancy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:07.999582+00:00
-- url     : https://prove2.me/theorems/7427287e-e4a6-4281-bbcf-35420bed44c4
-- title:
--   Base-q logarithms and code redundancy
-- statement:
--   For an integer alphabet size $q\ge2$, write $\log_q s=\ln(s)/\ln(q)$. The redundancy of a nonempty finite code $C$ of length $n$, measured in alphabet symbols, is
--   $$\operatorname{red}(C)=n-\log_q|C|.$$
--   The definition uses real numbers. Calls in code-existence conclusions explicitly require nonempty codes and sufficiently large positive lengths. Lean totalizes logarithms and division outside their mathematical domain; those values are not used to establish a target. Redundancy connects code cardinality to the stated asymptotic bound.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), §1.1, displayed definition red(C)=n−log_q|C|, printed p. 1 (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Words

namespace DeletionHash.MixedEdit

universe u

noncomputable def logBase (q : ℕ) (x : ℝ) : ℝ := Real.log x / Real.log (q : ℝ)

/-- Used on nonempty codes and q≥2 in every code-existence conclusion. -/
noncomputable def redundancy {α : Type u} {n : ℕ} (q : ℕ) (C : Finset (Word α n)) : ℝ :=
  (n : ℝ) - logBase q (C.card : ℝ)

end DeletionHash.MixedEdit


