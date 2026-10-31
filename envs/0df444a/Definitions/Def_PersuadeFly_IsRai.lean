-- Prove2me | Definitions.Def_PersuadeFly_IsRai
-- name    : PersuadeFly_IsRai
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:31:26.354375+00:00
-- url     : https://prove2.me/theorems/899eb800-0ee9-4004-8237-6c44fcbc47dc
-- title:
--   A run of the Rai algorithm (Algorithm 1)
-- statement:
--   A **signaling algorithm** assigns to each time $t$ and history $h_t$ a mechanism $\sigma[h_t]$. It is a run of the **Robustness Against Ignorance (Rai)** algorithm with parameters $\gamma_0$, $\mathcal C_0$, $(\epsilon_t)$ and horizon $T$ if
--
--   1. $\gamma_0\in\mathcal B_0$ and $\mathcal B_0\subseteq\mathcal C_0\subseteq\Delta(\Omega)$;
--   2. for every $t<T$ and every history $h_t$,
--   $$
--   \sigma[h_t]\in\arg\max_\sigma\{V(\gamma_t,\sigma):\sigma\in\mathsf{Pers}(\mathcal B_t)\}.
--   $$
--
--   The recommendation $a_t$ is then drawn from $\sigma[h_t](\omega_t,\cdot)$.
--
--   **Formalization Note** Algorithm 1 says "choose any" maximizer; every theorem quantifies over all runs, so every tie-breaking rule is covered.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, Algorithm 1, p.21

import Mathlib
import Definitions.Def_PersuadeFly_persSet
import Definitions.Def_PersuadeFly_value
import Definitions.Def_PersuadeFly_raiSet

namespace PersuadeFly

/-- **`alg` is a run of the Rai algorithm** (Algorithm 1). Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, Algorithm 1, p.21: with parameters
`γ₀ ∈ B₀` and `{ϵ_t}`, at each `t ∈ [T]` and after each history `h_t`, choose any
`σ[h_t] ∈ argmax_σ {V(γ_t, σ) : σ ∈ Pers(B_t)}`, and recommend `a_t = a` with probability
`σ(ω_t, a; h_t)`.

A signaling algorithm is a map `alg t h_t : Ω → A → ℝ` (p.13). `IsRai I γ₀ C₀ ε T alg` says that the
parameters are admissible (`γ₀ ∈ B₀`, `B₀ ⊆ C₀ ⊆ Δ(Ω)`) and that for every `t < T` and every history
`h`, `alg t h` is a maximizer of `V(γ_t, ·)` over `Pers(B_t)`.

**Formalization Note** "Choose any" is a universal quantifier over `alg` in every theorem: each
tie-breaking rule is a separate `alg`. The first-round set `C₀` is explained in `raiSet`. -/
def IsRai {Ω A : Type} [Fintype Ω] [DecidableEq Ω] [Fintype A] (I : Instance Ω A)
    (γ0 : Ω → ℝ) (C0 : Set (Ω → ℝ)) (ε : ℕ → ℝ) (T : ℕ)
    (alg : (t : ℕ) → (Fin t → Ω × A) → Ω → A → ℝ) : Prop :=
  γ0 ∈ I.B0 ∧ I.B0 ⊆ C0 ∧ C0 ⊆ stdSimplex ℝ Ω ∧
    ∀ t < T, ∀ h : Fin t → Ω × A,
      alg t h ∈ persSet I (raiSet γ0 C0 ε t h) ∧
        ∀ σ ∈ persSet I (raiSet γ0 C0 ε t h),
          value I (raiEmpirical γ0 t h) σ ≤ value I (raiEmpirical γ0 t h) (alg t h)

end PersuadeFly


