-- Prove2me | Definitions.Def_PPSLattice_OWFInvProb
-- name    : PPSLattice_OWFInvProb
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:26:05.333369+00:00
-- url     : https://prove2.me/theorems/ab1450b5-8e0d-4b61-80b2-538ec7ed4256
-- title:
--   Uniform inversion probability of a one-way-function candidate
-- statement:
--   For a candidate function $f$ and a uniform PPT inverter $I$, this is the standard inversion success probability at input length $n$:
--   $$
--   \Pr_{x\leftarrow\{0,1\}^n}\bigl[f(I(1^n,f(x)))=f(x)\bigr].
--   $$
--   It packages the exact expression in the mission's uniform definition `OWFExists`, so reductions can discuss the probability without repeating the PMF formula.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, Theorems 4.3 and 4.5, pp.19–20 (one-way functions); mission Definitions/Def_PPSLattice_OWFExists (uniform PPT formulation).

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_AvgPHETH_uniformDist
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The probability that the uniform PPT inverter `I`, activated at security parameter `n` on
`f x` for a uniformly random `n`-bit `x`, returns a string having the same image under `f`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission, Theorems 4.3 and 4.5, pp.19–20; see the mission's `OWFExists`.

**Formalization Note.** This is exactly the real-valued inversion probability appearing in
`PPSLattice.OWFExists`; `I.activate` supplies the security parameter in unary and uniform coins. -/
noncomputable def owfInvProb (f : Str → Str) (I : RestrictedDec.Adversary) (n : ℕ) : ℝ :=
  (((AvgPHETH.uniformDist n).bind fun x =>
      (I.activate n [] (f x)).map fun r => decide (f r.2 = f x)) true).toReal

end PPSLattice


