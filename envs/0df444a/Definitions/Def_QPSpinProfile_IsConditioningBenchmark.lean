-- Prove2me | Definitions.Def_QPSpinProfile_IsConditioningBenchmark
-- name    : QPSpinProfile_IsConditioningBenchmark
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:51.662447+00:00
-- url     : https://prove2.me/theorems/be9d1b85-180f-4fcc-92a4-e71d53659e8f
-- title:
--   Definition 1.1: conditioning benchmark
-- statement:
--   Let $(\mathcal C_n)_{n\ge1}$ and $(\mathcal B_n)_{n\ge1}$ be classes of $n$-qubit states and write $\mathrm{conv}(\mathcal B_n)$ for the convex mixtures of states in $\mathcal B_n$. Then $(\mathcal B_n)$ is a **conditioning benchmark** for $(\mathcal C_n)$ if, for every fixed $p\ge2$ and $\alpha\in(0,1)$, each $\rho\in\mathcal C_n$ admits a set $J\subseteq[n]$ with $|J|\ge(1-\alpha)n$ and a state $\sigma\in\mathrm{conv}(\mathcal B_n)$ with
--   $$
--   \binom np^{-1}\sum_{\substack{P\in\mathcal P_{n,p}\\ \mathrm{supp}(P)\subseteq J}}|f_\rho(P)-f_\sigma(P)|^2=O_{p,\alpha}(n^{-1})
--   $$
--   as $n\to\infty$, uniformly over $\rho\in\mathcal C_n$ (display (3)).
--
--   By Corollary 2.4, $\mathrm{prod}_n$ is a conditioning benchmark for every state class; Theorem 1.2(ii) compares a class with any of its conditioning benchmarks.
--
--   **Formalization Note** "$O_{p,\alpha}(n^{-1})$ uniformly in $\rho$" is: there are $K$ and $N$, depending only on $p$ and $\alpha$, such that the sum is at most $K/n$ for all $n\ge N$ and all $\rho\in\mathcal C_n$.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), Definition 1.1, p.4 (PDF p.7), display (3)

import Mathlib
import Definitions.Def_QPSpinProfile_profile

namespace QPSpinProfile

/-- **Definition 1.1 (Conditioning benchmark)** (arXiv:2610.02166, held version sha256 a0a1ec89…,
p.4, PDF p.7). `(B_n)` is a conditioning benchmark for `(C_n)` if for every fixed `p ≥ 2` and
`α ∈ (0,1)`, each `ρ ∈ C_n` admits `J ⊆ [n]` with `|J| ≥ (1 − α)n` and `σ ∈ conv(B_n)` with
`C(n,p)^{-1} ∑_{P ∈ 𝒫_{n,p}, supp(P) ⊆ J} |f_ρ(P) − f_σ(P)|² = O_{p,α}(n^{-1})` as `n → ∞`,
uniformly over `ρ ∈ C_n` (display (3)).

**Formalization Note** `O_{p,α}(n^{-1})` uniformly in `ρ` is: a constant `K` and a threshold `N`,
both depending only on `p` and `α`, such that the sum is at most `K / n` for all `n ≥ N` and all
`ρ ∈ C_n`. `conv(B_n)` is `convexHull ℝ (B n)`. -/
def IsConditioningBenchmark (B C : (n : ℕ) → Set (Matrix (Qubits n) (Qubits n) ℂ)) : Prop :=
  ∀ p : ℕ, 2 ≤ p → ∀ α : ℝ, 0 < α → α < 1 → ∃ K : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ρ ∈ C n,
    ∃ J : Finset (Fin n), (1 - α) * (n : ℝ) ≤ (J.card : ℝ) ∧ ∃ σ ∈ convexHull ℝ (B n),
      ((n.choose p : ℝ))⁻¹ * ∑ P ∈ Finset.univ.filter (fun P : PauliString n p => P.supp ⊆ J),
        (profile p ρ P - profile p σ P) ^ 2 ≤ K / (n : ℝ)

end QPSpinProfile


