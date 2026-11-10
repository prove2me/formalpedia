-- Prove2me | Definitions.Def_PPSLattice_OWFExists
-- name    : PPSLattice_OWFExists
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:31.591939+00:00
-- url     : https://prove2.me/theorems/e09c2531-4477-477b-b6d5-cece90267d9d
-- title:
--   One-way functions exist
-- statement:
--   There is a polynomial-time computable $f:\{0,1\}^*\to\{0,1\}^*$ such that for every uniform PPT inverter $I$,
--   $$\Pr_{x\leftarrow\{0,1\}^n}\bigl[f(I(1^n,f(x)))=f(x)\bigr]$$
--   is negligible in $n$.
--
--   **Formalization Note** The paper does not define one-way functions; this is the standard definition, with inverters in the same uniform machine model as every adversary of the mission. `NoisyOWMPC.OWFExists` is not reused: its inverters are non-uniform circuits.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.3, p.19; Theorem 4.5, p.20

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_AvgPHETH_uniformDist
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **One-way functions exist**: there is a polynomial-time computable `f : {0,1}* → {0,1}*` such that
every uniform PPT inverter `I`, given `1^n` and `f(x)` for `x ← {0,1}^n`, outputs a preimage of
`f(x)` with probability negligible in `n`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 4.3, p.19 and Theorem 4.5, p.20 ("Assuming the existence of one-way functions").

**Formalization Note.** The paper does not define one-way functions; this is the standard
definition with uniform inverters, in the same machine model (`RestrictedDec.Adversary`, one
activation on security parameter `n`) as every other adversary of the mission.
`NoisyOWMPC.OWFExists` is not reused because its inverters are non-uniform circuits. -/
def OWFExists : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ I : RestrictedDec.Adversary, I.Valid →
    NoisyOWMPC.Negligible fun n =>
      (((AvgPHETH.uniformDist n).bind fun x =>
          (I.activate n [] (f x)).map fun r => decide (f r.2 = f x)) true).toReal

end PPSLattice


