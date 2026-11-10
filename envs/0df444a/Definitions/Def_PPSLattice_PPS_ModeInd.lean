-- Prove2me | Definitions.Def_PPSLattice_PPS_ModeInd
-- name    : PPSLattice_PPS_ModeInd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:38:49.397176+00:00
-- url     : https://prove2.me/theorems/85b3d895-bc4d-43dd-9e34-dd89be59aca9
-- title:
--   Mode indistinguishability of a PPS scheme
-- statement:
--   A PPS scheme is **mode indistinguishable** if for every PPT adversary $\mathcal A$,
--   $$\Bigl|\Pr[\text{the mode-indistinguishability experiment outputs }1]-\tfrac12\Bigr|$$
--   is negligible in $\lambda$. Here the adversary's set must contain $i^*$, and in mode $b=1$ the challenge encrypts a uniformly random message.
--
--   **Formalization Note** Adversaries are uniform reactive machines with a polynomial-time step function (`RestrictedDec.Adversary`); admissibility is enforced by the ½-convention of the experiment.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Mode Indistinguishability, p.18

import Mathlib
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_PPSLattice_ppsGame
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **Mode indistinguishability** of a PPS scheme: for every uniform PPT adversary `A`,
`|Pr[ppsGame (mode indistinguishability) = 1] − ½|` is negligible in `λ`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, Mode Indistinguishability, p.18 ("For any stateful admissible PPT adversary A,
there exists a negligible function negl(·) such that for any λ ∈ N, |Pr[…] − 1/2| ≤ negl(λ)").

**Formalization Note.** Adversaries are the uniform reactive machines of `RestrictedDec.Adversary`
with a polynomial-time step function. Admissibility (`S ⊆ [N]`, `i* ∈ S`) is enforced inside the game
by scoring inadmissible runs as a uniform guess, which is equivalent (see `ppsRun`). -/
def PPS.ModeInd (E : PPS) : Prop :=
  ∀ A : RestrictedDec.Adversary, A.Valid →
    NoisyOWMPC.Negligible fun lam => |((ppsGame false E A lam) true).toReal - 1 / 2|

end PPSLattice


