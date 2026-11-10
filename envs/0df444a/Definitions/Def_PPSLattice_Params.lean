-- Prove2me | Definitions.Def_PPSLattice_Params
-- name    : PPSLattice_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:51.941296+00:00
-- url     : https://prove2.me/theorems/264517ce-f65b-42a5-8648-7858a4878fff
-- title:
--   LWE parameters $(n,q,\chi,\tilde\chi,B)$ of Construction 4.6
-- statement:
--   Functions of $(\lambda,N)$: the dimension $n$, the modulus $q$, the Gaussian width $\chi$, the smudging width $\tilde\chi$ and the error bound $B$; and $m=n\lceil\log_2q\rceil$, the number of columns of the gadget matrix.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Parameters, p.20

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The **LWE parameters of Construction 4.6**, as functions of `(λ, N)`: the dimension `n`, the modulus
`q`, the Gaussian width `χ`, the smudging width `χ̃` (`chit`) and the error bound `B`; the number of
columns of the gadget matrix is `m = n · ⌈log₂ q⌉`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Parameters, p.20 ("n = poly(λ, log N), χ = poly(n)", "m = n · ⌈log q⌉", "χ̃ > …", "B = …",
"q > …"). -/
structure Params where
  n : ℕ → ℕ → ℕ
  q : ℕ → ℕ → ℕ
  chi : ℕ → ℕ → ℕ
  chit : ℕ → ℕ → ℕ
  B : ℕ → ℕ → ℕ

/-- `m = n · ⌈log₂ q⌉` (§4.3, p.20, "m = n · ⌈log q⌉ (Gadget matrix)"). -/
def Params.m (P : Params) (lam N : ℕ) : ℕ := P.n lam N * Nat.clog 2 (P.q lam N)

end PPSLattice


