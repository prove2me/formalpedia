-- Prove2me | Definitions.Def_RestrictedDec_UniformSets
-- name    : RestrictedDec_UniformSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:40.151206+00:00
-- url     : https://prove2.me/theorems/0ddda38e-fc1a-4da8-b69a-ecf82fc4e899
-- title:
--   Uniformly computable public coordinate sets
-- statement:
--   A sequence $(S_\lambda)_\lambda$ is a sequence of **uniformly computable public coordinate sets** for the message length $n$ if $S_\lambda\subseteq[n(\lambda)]=\{1,\dots,n(\lambda)\}$ for every $\lambda$ and one polynomial-time machine maps $1^\lambda$ to the characteristic vector of $S_\lambda$ (a string of length $n(\lambda)$).
--
--   The positions are part of the public specification of the permitted functions, fixed for each $\lambda$ rather than chosen with each query; this makes $\lambda\mapsto q_{S_\lambda}$ a single asymptotic observation.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Corollary 2, p.22; §1.2, p.9; §2.3, p.15 (uniformly indexed observations)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

/-- A sequence `S_λ ⊆ [n(λ)] = {1, …, n(λ)}` of **uniformly computable public coordinate sets**:
one polynomial-time machine maps `1^λ` to the characteristic vector of `S_λ` (of length `n(λ)`).
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Corollary 2, p.22 ("Let Sλ,
Tλ ⊆ [n(λ)] be uniformly computable public coordinate sets"); §2.3, p.15 ("An asymptotic security
notion is determined by a uniformly polynomial-time computable index sequence i = i(1λ)").

**Formalization Note.** The set is part of the public specification (p.9), so it is computed from
`λ` alone; its characteristic vector is a polynomial-length index of the observation. -/
def UniformSets (n : ℕ → ℕ) (S : ℕ → Finset ℕ) : Prop :=
  (∀ lam, S lam ⊆ Finset.Icc 1 (n lam)) ∧
    ∃ f : Str → Str, PolyTimeComputable f ∧
      ∀ lam, f (encNat lam) = (List.range (n lam)).map fun r => decide (r + 1 ∈ S lam)

end RestrictedDec


