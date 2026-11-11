-- Prove2me | Definitions.Def_QMAvsQCMAH_IsSparseAgreeing
-- name    : QMAvsQCMAH_IsSparseAgreeing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:19:15.976927+00:00
-- url     : https://prove2.me/theorems/d50e31da-b7fd-4ad7-94ca-09414b249854
-- title:
--   Oracles agreeing outside a sparse random set (Definition 21)
-- statement:
--   Fix $c>0$ and a finite nonempty domain $\mathcal X$, and put $b=\lceil\sqrt\lambda\rceil$, $\beta=2^{-b}$, $\rho=2^{-c\lambda}$. A joint law $\mu$ of $(P,B,\mathcal O)$ is admissible here if:
--   1. $\Pr_P[u_1,\dots,u_t\in P]\le\rho^t$ for all distinct $u_1,\dots,u_t$ and $1\le t\le2^\lambda$;
--   2. independently of $P$, $B(u)\leftarrow\mathrm{Bernoulli}(\beta)$ for each $u$;
--   3. $\mathcal O:\mathcal X\to\{0,1\}$ is arbitrary subject to $\mathcal O|_{\mathcal X\setminus P}=B|_{\mathcal X\setminus P}$.
--
--   The conditional law of $\mathcal O$ given $(P,B)$ is unrestricted.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 21, p.35

import Definitions.Def_QMAvsQCMAH_prob
import Definitions.Def_QMAvsQCMAH_betaNoise

set_option autoImplicit false

namespace QMAvsQCMAH

/-- A joint law `μ` of `(P, B, O)` (`P ⊆ X`, `B, O : X → {0,1}`) is a **distribution of oracles
agreeing outside a sparse random set** for the constant `c > 0` at parameter `λ`:
1. `Pr[u_1, …, u_t ∈ P] ≤ ρ^t` with `ρ = 2^{−cλ}`, for all distinct `u_1, …, u_t` and
   `1 ≤ t ≤ 2^λ`;
2. `B` is independent of `P` with independent `Bernoulli(β)` values, `β = 2^{−⌈√λ⌉}`;
3. `O` is arbitrary subject to `O|_{X∖P} = B|_{X∖P}` (almost surely).

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Definition 21, p.35 (PDF p.38): "Fix c > 0 and a finite nonempty domain X ⊆ {0, 1}∗, and
put b = ⌈√λ⌉, β = 2^{−b} and ρ = 2^{−cλ}. We define µ to be any distribution of oracles agreeing
outside a sparse random set, sampled as follows: 1. Sample P ⊆ X from any distribution satisfying
Pr_P[u1, …, ut ∈ P] ≤ ρ^t (1 ≤ t ≤ 2^λ) for all distinct u1, …, ut ∈ X. 2. Independently sample
B(u) ← Bernoulli(β) for each u ∈ X. 3. Sample O : X → {0, 1} arbitrarily subject to
O|_{X\P} = B|_{X\P}."

**Formalization Note.** The joint law is any finite distribution with these three properties
(paper.md decision 13); in particular the law of `O` given `(P, B)` is arbitrary, so the CHN
choice `O = B ∨ 1_P` is one special case. Independence of `B` and `P` is the product rule for
every event about `P` and every value of `B`. -/
def IsSparseAgreeing (X : Type) [Fintype X] [DecidableEq X] (c : ℝ) (lam : ℕ)
    (μ : Finset X × (X → Bool) × (X → Bool) → ℝ) : Prop :=
  IsDist μ ∧
  (∀ S : Finset X, 1 ≤ S.card → S.card ≤ 2 ^ lam →
    prob μ (fun t => S ⊆ t.1) ≤ ((2 : ℝ) ^ (-(c * lam))) ^ S.card) ∧
  (∀ (A : Set (Finset X)) (B0 : X → Bool),
    prob μ (fun t => t.1 ∈ A ∧ t.2.1 = B0) = prob μ (fun t => t.1 ∈ A) * bernW (betaNoise lam) B0) ∧
  prob μ (fun t => ∃ u, u ∉ t.1 ∧ t.2.2 u ≠ t.2.1 u) = 0

end QMAvsQCMAH


