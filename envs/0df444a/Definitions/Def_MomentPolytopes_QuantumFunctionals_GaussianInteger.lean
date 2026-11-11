-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_GaussianInteger
-- name    : MomentPolytopes_QuantumFunctionals_GaussianInteger
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:03:27.458083+00:00
-- url     : https://prove2.me/theorems/c291c14f-06ab-4144-85bd-f1a350639d87
-- title:
--   Gaussian-integer tensor tuples, the bit-length ⟨T⟩ and n_max
-- statement:
--   A tensor tuple $T$ has **Gaussian integer entries** if every entry lies in $\mathbb Z[i]$, i.e. is $a+bi$ with $a,b\in\mathbb Z$.
--
--   Its **bit-length** is the binary encoding length of all $n_0n_1\cdots n_d$ entries,
--   $$\langle T\rangle=\sum_{\text{entries }a+bi}\big(\operatorname{bitlen}(a)+\operatorname{bitlen}(b)\big),\qquad\operatorname{bitlen}(z)=1+\lceil\log_2(|z|+1)\rceil ,$$
--   counting a sign bit. Finally $n_{\max}=\max_{\ell\in[d]}n_\ell$.
--
--   **Formalization Note** The paper does not define $\langle T\rangle$; this is the standard binary length, and any encoding length within a constant factor of it gives the same polynomial bounds. `bitlen z = 1 + Nat.size |z|`; the integer parts of a Gaussian-integer entry are recovered exactly by `round`. $n_{\max}=0$ when $d=0$.
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 44, Theorem 6.28 and fn. 31

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction

set_option autoImplicit false

namespace MomentPolytopes.QuantumFunctionals

variable {d n0 : ℕ} {n : Fin d → ℕ}

/-- `T` has Gaussian integer entries, i.e. entries in `ℤ[i]` (p. 44). -/
def IsGaussianInteger (T : Ten d n0 n) : Prop :=
  ∀ x, ∃ a b : ℤ, T x = (a : ℂ) + (b : ℂ) * Complex.I

/-- Binary encoding length of an integer, with a sign bit: `1 + ⌈log₂(|z| + 1)⌉`. -/
def intBitLength (z : ℤ) : ℕ :=
  1 + Nat.size z.natAbs

/-- Bit-length `⟨T⟩` of a Gaussian-integer tensor tuple (Theorem 6.28, p. 44): the sum over all
`n_0 n_1 ⋯ n_d` entries `a + bi` of the binary lengths of `a` and `b`. (`round` recovers the
integer parts of a Gaussian integer entry exactly.) -/
noncomputable def bitLength (T : Ten d n0 n) : ℕ :=
  ∑ x, (intBitLength (round (T x).re) + intBitLength (round (T x).im))

/-- `n_max = max_ℓ n_ℓ` (`0` when `d = 0`). -/
def nmax (n : Fin d → ℕ) : ℕ :=
  Finset.univ.sup n

end MomentPolytopes.QuantumFunctionals


