-- Prove2me | Definitions.Def_PPSLattice_garbGame
-- name    : PPSLattice_garbGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:35:05.379128+00:00
-- url     : https://prove2.me/theorems/a6b65e7f-477f-476e-8bb2-8ae186c54c62
-- title:
--   The garbling security experiment
-- statement:
--   $b\leftarrow\{0,1\}$; the adversary outputs $(1^s,1^\ell)$ with $s,\ell\ge1$ (otherwise the output is a uniform bit); $\mathrm{gk}\leftarrow\mathrm{Setup}(1^\lambda,1^s,1^\ell)$; then the interaction with the challenger. The output is $1$ iff the guess is $b$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, Security, p.20

import Mathlib
import Definitions.Def_PPSLattice_garbRun
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace PPSLattice

/-- The **garbling security experiment** (Definition 4.4), with output `1` iff the guess equals `b`:
`b ← {0,1}`; the adversary's first move `tup [1^s, 1^ℓ]` must have `s, ℓ ≥ 1` (otherwise the output is
a uniform bit); `gk ← Setup(1^λ, 1^s, 1^ℓ)`; then the interaction `garbRun` from phase `0` with `p(λ)`
further activations, the adversary first receiving `1^λ`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.4, Security, p.20. -/
noncomputable def garbGame (G : Garb) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] (BeyondDS.tup [])).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let s := BeyondDS.decNat (fs.getD 0 [])
    let ell := BeyondDS.decNat (fs.getD 1 [])
    if 1 ≤ s ∧ 1 ≤ ell then
      (PMF.uniformOfFintype Bool).bind fun b =>
        (G.setup lam s ell).bind fun gk =>
          (garbRun G A lam s ell gk b (A.p.eval lam) 0 [] r0.1 (encNat lam)).map
            fun b' => decide (b' = b)
    else PMF.uniformOfFintype Bool

end PPSLattice


