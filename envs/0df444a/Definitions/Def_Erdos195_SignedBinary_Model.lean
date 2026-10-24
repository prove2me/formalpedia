-- Prove2me | Definitions.Def_Erdos195_SignedBinary_Model
-- name    : Erdos195_SignedBinary_Model
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T07:39:59.93015+00:00
-- url     : https://prove2.me/theorems/999817cb-3d1e-4c02-810f-c5a7a3a14be2
-- title:
--   Binary place values with a fixed sign at each digit
-- statement:
--   For a Boolean sign sequence $\varepsilon:\mathbb N\to\{\mathrm{false},\mathrm{true}\}$, define $s(\mathrm{false})=1$ and $s(\mathrm{true})=-1$. The signed binary value of a natural number is the finite sum of its binary digits, weighted by $s(\varepsilon_j)2^j$. The exact recursive definition is $v_\varepsilon(0)=0$; for $n>0$, it is twice $v_{\varepsilon(\cdot+1)}(\lfloor n/2\rfloor)$ plus the sign of the zeroth digit when $n$ is odd, and plus zero when $n$ is even. The definition makes no claim of injectivity, surjectivity, or progression avoidance. It is the minimal interface used by a generic obstruction to fixed signed-digit transports of progression-free natural-number permutations.
-- source:
--   Research-derived exact signed-binary recurrence used in the Erdős195 transport-family investigation (public mission49a38d9f-e723-48b5-9209-130dea45c67b). Context: Ho, arXiv:2609.12780v1, explicit natural-number permutation; this signed-digit transport is an investigated extension strategy, not a claim of that paper. The full scoped obstruction is submitted separately.

import Mathlib

namespace Erdos195.SignedDigitResearch

def sign (b : Bool) : ℤ := if b then -1 else 1

def signedValue (ε : ℕ → Bool) (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
    2 * signedValue (fun j => ε (j + 1)) (n / 2) +
      if n % 2 = 0 then 0 else sign (ε 0)
termination_by n
decreasing_by omega

end Erdos195.SignedDigitResearch


