-- Prove2me | Definitions.Def_NearOptOWF_NmCAPPInst_accFrac
-- name    : NearOptOWF_NmCAPPInst_accFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:20.666539+00:00
-- url     : https://prove2.me/theorems/fb126148-f7e5-407c-b4c0-ff6445a8505b
-- title:
--   Acceptance probability of a non-deterministic circuit
-- statement:
--   For a non-deterministic circuit $C$, $\Pr_x[C(x) = 1]$ is the fraction of inputs $x \in \{0,1\}^n$ for which some $u \in \{0,1\}^w$ has $C(x, u) = 1$.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_NmCAPPInst
import Definitions.Def_KarpLiptonOM_Circuit_eval

namespace NearOptOWF

/-- `Pr_x[C(x) = 1]` for a non-deterministic circuit (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10)): the
fraction of `x ∈ {0,1}ⁿ` for which some `u ∈ {0,1}^w` has `C(x, u) = 1`. -/
noncomputable def NmCAPPInst.accFrac (I : NmCAPPInst) : ℝ :=
  ((Finset.univ.filter fun x : Fin I.n → Bool =>
      ∃ u : Fin I.w → Bool, I.C.eval (List.ofFn x ++ List.ofFn u) = true).card : ℝ) / 2 ^ I.n

end NearOptOWF


