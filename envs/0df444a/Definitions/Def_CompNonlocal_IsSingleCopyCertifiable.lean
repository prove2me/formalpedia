-- Prove2me | Definitions.Def_CompNonlocal_IsSingleCopyCertifiable
-- name    : CompNonlocal_IsSingleCopyCertifiable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:48:16.613483+00:00
-- url     : https://prove2.me/theorems/950e06f9-2e57-4b39-a684-19af364e1508
-- title:
--   $\gamma$-single-copy certifiability
-- statement:
--   A two-qubit state $\omega$ is **$\gamma$-single-copy certifiable** if some single-copy game certifies it with gap $\gamma$: $c(\kappa)-s(\kappa)\ge\gamma-\mathsf{negl}(\kappa)$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 11, p.25

import Mathlib
import Definitions.Def_CompNonlocal_IsCertificateFor

set_option autoImplicit false

namespace CompNonlocal

/-- γ-single-copy certifiability. Głuch, Morimae, *From Computational Nonlocality to Public-Key
Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 11,
p.25: "A state ω_AB is single-copy certifiable if it is not-efficiently-local with k = 1 … For
γ ∈ (0, 1], we say that ω_AB is γ-single-copy certifiable if c(κ) − s(κ) ≥ γ − negl(κ)": some
single-copy certificate for `ω` has gap `γ` in the sense of `IsCertificateFor`. -/
def IsSingleCopyCertifiable (ω : Matrix (Bool × Bool) (Bool × Bool) ℂ) (γ : ℝ) : Prop :=
  ∃ c : Certificate, IsCertificateFor c ω γ

end CompNonlocal


