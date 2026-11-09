-- Prove2me | Definitions.Def_NoisyOWMPC_Negligible
-- name    : NoisyOWMPC_Negligible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:38:23.599942+00:00
-- url     : https://prove2.me/theorems/5d3fe9d0-27a2-4ddc-b3f9-ed4e2828a76c
-- title:
--   Negligible functions and polynomially bounded lengths
-- statement:
--   A function $\nu:\mathbb N\to\mathbb R_{\ge 0}$ is **negligible** if for every constant $c>0$ there is $\lambda_0$ such that
--   $$\nu(\lambda)\le \lambda^{-c}\qquad\text{for all }\lambda\ge\lambda_0 .$$
--   A length function $p:\mathbb N\to\mathbb N$ is **polynomially bounded** if $p(\lambda)\le(\lambda+2)^c$ for one exponent $c$ and every $\lambda$; it is a **public polynomial parameter** if moreover $1^{p(\lambda)}$ is computed from $1^\lambda$ in polynomial time (Definition 4.2: "all other lengths are public polynomially bounded parameters").
--
--   These are the asymptotic notions behind every error term of the mission: negligible statistical and computational errors, and the polynomial size of all strings, circuits and parameters.
--
--   **Formalization Note** Values are real numbers and nonnegativity is the first clause of the definition (the paper's codomain is $\mathbb R_{\ge0}$).
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §3 Notation and conventions, p.15

import Mathlib
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NoisyOWMPC

/-- **Negligible functions** (Ishai, Lu, Zafar, *Non-Interactive Cryptography over Noisy Channels
from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript sha256 3a9569fa…), §3
Notation and conventions, p.15): "A function `ν : ℕ → ℝ≥0` is negligible if for every constant
`c > 0` there exists `λ₀` such that `ν(λ) ≤ λ^{−c}` for all `λ ≥ λ₀`."

**Formalization Note** Values are real numbers with nonnegativity as the first clause (the paper's
codomain `ℝ≥0`); the exponent `c` ranges over positive reals and `λ^{−c}` is `Real.rpow`. -/
def Negligible (ν : ℕ → ℝ) : Prop :=
  (∀ lam, 0 ≤ ν lam) ∧ ∀ c : ℝ, 0 < c → ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, ν lam ≤ (lam : ℝ) ^ (-c)

/-- A length function is **polynomially bounded** (STOC 2027 submission (manuscript sha256
3a9569fa…), §3, p.15: "all strings, tables, and circuit descriptions have polynomial size"):
`p(λ) ≤ (λ + 2)^c` for one exponent `c` and every `λ`. -/
def PolyBounded (p : ℕ → ℕ) : Prop := ∃ c : ℕ, ∀ lam, p lam ≤ (lam + 2) ^ c

/-- A **public polynomial parameter** (STOC 2027 submission (manuscript sha256 3a9569fa…),
Definition 4.2, p.18: "the number `N` of noisy channel uses, the noiseless message length `L ≥ 0`,
and all other lengths are public polynomially bounded parameters"; §3, p.15: all algorithms run in
polynomial time): `p` is polynomially bounded and one machine computes `1^{p(λ)}` from `1^λ` in
polynomial time.

**Formalization Note** A parameter that no polynomial-time party can compute could not be used by
the sender, the receivers or a simulator; every polynomial in `λ` qualifies. -/
def PolyParam (p : ℕ → ℕ) : Prop :=
  PolyBounded p ∧ LaconicBarrier.PolyTimeOn (ι := ℕ) (fun lam => [LaconicBarrier.unary lam])
    (fun lam => LaconicBarrier.unary (p lam))

end NoisyOWMPC


