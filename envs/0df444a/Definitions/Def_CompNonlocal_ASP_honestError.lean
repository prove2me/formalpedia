-- Prove2me | Definitions.Def_CompNonlocal_ASP_honestError
-- name    : CompNonlocal_ASP_honestError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:27.939573+00:00
-- url     : https://prove2.me/theorems/2cf04150-b1a0-471a-9b00-6e32ece737f3
-- title:
--   The sender's estimation error, Eq. (23)
-- statement:
--   $$\mathbb E\big[\|\hat r_S-r(T)\|_2^2\big]$$
--   in an honest execution: $(\mathrm{msg}_S,\mathrm{st}_S)\leftarrow\mathrm{Sen}(1^\kappa)$, $(\mathrm{msg}_R,\zeta)\leftarrow\mathrm{Rec}(\mathrm{msg}_S)$, $T=(\mathrm{msg}_S,\mathrm{msg}_R)$, $\hat r_S\leftarrow\mathrm{Dec}(\mathrm{st}_S,\mathrm{msg}_S,\mathrm{msg}_R)$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 14, Eq. (23), p.33

import Mathlib
import Definitions.Def_CompNonlocal_ASP
import Definitions.Def_CompNonlocal_decVec

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The sender's mean squared estimation error in an honest ASP execution. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), Definition 14, p.33, Eq. (23): `E[∥r̂_S − r(T)∥₂² | (msg_S, st_S) ←
ASP.Sen(1^κ), (msg_R, ζ) ← ASP.Rec(msg_S), T := (msg_S, msg_R), r̂_S ← ASP.Dec(st_S, msg_S, msg_R)]`.

**Formalization Note** The sum over sender messages `mS`, receiver replies `mR` and decoder outputs
`d` (read as vectors by `decVec`) of `Pr[mR | mS] · Pr[mS, d] · ‖r̂_d − r(t)‖²`; transcripts of
probability `0` have weight `0`. -/
noncomputable def ASP.honestError (P : ASP) (κ : ℕ) : ℝ :=
  ∑ mS : Bits (P.Sen κ).outC.length, ∑ mR : Bits (P.Rec κ).outC.length,
    ∑ d : Bits (P.Dec κ).outC.length,
      (P.prepared κ (List.ofFn mS) (List.ofFn mR)).trace.re *
        P.decProb κ (List.ofFn mS) (List.ofFn mR) (List.ofFn d) *
        ‖decVec (List.ofFn d) - P.prepBloch κ (List.ofFn mS) (List.ofFn mR)‖ ^ 2

end CompNonlocal


