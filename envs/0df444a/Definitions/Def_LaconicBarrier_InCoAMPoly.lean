-- Prove2me | Definitions.Def_LaconicBarrier_InCoAMPoly
-- name    : LaconicBarrier_InCoAMPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:54.651335+00:00
-- url     : https://prove2.me/theorems/2c79544c-33ae-4418-86d0-72006bca0a53
-- title:
--   $L \in \mathsf{coAM}$ with polynomial resources
-- statement:
--   $L \in \mathsf{coAM}(\text{rounds} = 1, \text{verifier time} = \mathrm{poly}(n), \text{prover comm} = \mathrm{poly}(n), \text{verifier comm} = \mathrm{poly}(n), \text{verifier randomness} = \mathrm{poly}(n))$: the complement $\overline L$ has a one-round public-coin (Arthur–Merlin) proof with polynomial verifier time, communication and randomness, completeness at least $2/3$ and soundness at most $1/3$, where $n = |x|$.
--
--   This is the conclusion of Corollaries 7.1 and 7.3; "$\mathsf{NP} \subseteq \mathsf{coAM}$" means that every NP language satisfies it.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Corollary 7.1, p.46; §4.2.1, p.25

import Mathlib
import Definitions.Def_LaconicBarrier_InIP

namespace LaconicBarrier

/-- `L ∈ coAM(rounds = 1, verifier time = poly(n), prover comm = poly(n), verifier comm = poly(n),
verifier randomness = poly(n))` (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256
1af78662…), Corollary 7.1, p.46; §4.2.1, p.25: default errors `1/3`; "coAM = {L : L̄ ∈ AM}"): the
complement `L̄` has a one-round public-coin proof with polynomial verifier time, communication and
randomness, completeness at least `2/3` and soundness at most `1/3`; inputs are strings `x`,
`n = |x|`. -/
def InCoAMPoly (L : Set (List Bool)) : Prop :=
  ∃ d : ℕ, InAM (I := List Bool) (fun x => [x]) Lᶜ L 1 (fun x => (x.length + 2) ^ d)
    (fun x => (x.length + 2) ^ d) (fun x => (x.length + 2) ^ d) (fun x => (x.length + 2) ^ d)
    (fun _ => 1 / 3) (fun _ => 1 / 3)

end LaconicBarrier


