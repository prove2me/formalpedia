-- Prove2me | Definitions.Def_PPSLattice_PPS_PayloadHiding
-- name    : PPSLattice_PPS_PayloadHiding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:38:19.098347+00:00
-- url     : https://prove2.me/theorems/b7312e2d-9a4c-4949-baf7-7890e1715c93
-- title:
--   Payload hiding of a PPS scheme
-- statement:
--   A PPS scheme is **payload hiding** if for every PPT adversary $\mathcal A$,
--   $$\Bigl|\Pr[\text{the payload-hiding experiment outputs }1]-\tfrac12\Bigr|$$
--   is negligible in $\lambda$. Here the adversary chooses the challenge message and its set must exclude $i^*$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Payload Hiding, p.18

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_ppsGame
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Payload hiding** of a PPS scheme: for every uniform PPT adversary `A`,
`|Pr[ppsGame (payload hiding) = 1] − ½|` is negligible in `λ`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Payload Hiding, p.18 ("For any stateful admissible PPT adversary A, there exists a
negligible function negl(·) such that for any λ ∈ N, |Pr[…] − 1/2| ≤ negl(λ)", admissible: "S ⊆ [N]
and i* ∉ S").

**Formalization Note.** As for `PPS.ModeInd`; here the adversary chooses `µ_{i*}` and the admissible
sets exclude `i*`. -/
def PPS.PayloadHiding (E : PPS) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((ppsGame true E A lam) true).toReal - 1 / 2|

end PPSLattice


