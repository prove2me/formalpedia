-- Prove2me | Definitions.Def_PermLimits_Shared_ConvergesTo
-- name    : PermLimits_Shared_ConvergesTo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:56:27.345453+00:00
-- url     : https://prove2.me/theorems/36547a58-4dbb-49ad-92ae-32f62e7fe4ba
-- title:
--   Convergence $\sigma_n\to Z$ of a permutation sequence to a limit permutation
-- statement:
--   Let $(\sigma_m)_{m\in\mathbb N}$ be a permutation sequence with $|\sigma_m|\to\infty$, and let $Z\in\mathcal Z$. The sequence **converges to $Z$**, written $\sigma_m\to Z$, if
--   $$\lim_{m\to\infty} t(\tau,\sigma_m)=t(\tau,Z)\qquad\text{for every permutation } \tau .$$
--
--   The requirement $|\sigma_m|\to\infty$ is natural: a convergent sequence whose lengths have a bounded subsequence is eventually constant (Claim 2.4 of the source).
--
--   **Formalization Note** The standing assumption $|\sigma_m|\to\infty$ of the source's definition is the first conjunct, so "$\sigma_m\to Z$" includes it. The assumption $Z\in\mathcal Z$ is not part of the predicate; every statement using it assumes it separately. The pattern $\tau$ ranges over permutations of every length, including the trivial length $0$.
--
--   This definition is shared by both missions of this series: mission 1 (`01-limit-existence`, existence and uniqueness of the limit permutation) (Theorem 1.6, p. 4; Theorem 1.7, p. 5; Eq. (49), p. 17) and mission 2 (`02-cauchy-rectangular`, convergent sequences are Cauchy for the rectangular distance) (Theorem 1.6 (i), p. 4; Eq. (49), p. 17).
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, p. 4, Definition 1.5 (Eq. (5))

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity
import Definitions.Def_PermLimits_Shared_LimitMeasure

/-!
# Convergence of a permutation sequence to a limit permutation

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2, p. 4, Definition 1.5, Eq. (5).
-/

namespace PermLimits.Shared

open Filter Topology unitInterval

/-- **`σ_m → Z`** (Hoppen et al., arXiv:1103.5844v2, Definition 1.5, Eq. (5), p. 4). For a
permutation sequence `(σ_m)` with `|σ_m| → ∞` and `Z ∈ 𝒵`, `σ_m → Z` means
`lim_m t(τ, σ_m) = t(τ, Z)` for every permutation `τ`.

**Formalization Note.** The standing hypothesis `|σ_m| → ∞` of Definition 1.5 is made the first
conjunct, so `ConvergesTo s Z` asserts it. The sequence is named `s` (`σ` is reserved
notation once `unitInterval` is opened). The hypothesis `Z ∈ 𝒵` is not part of this predicate;
every statement using it assumes `IsLimitPerm Z` separately. `τ` ranges over permutations of every
length `k` (a length-`0` pattern gives the trivially true clause `1 → 1`). -/
def ConvergesTo (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) (Z : I → I → ℝ) : Prop :=
  Tendsto (fun m => (s m).1) atTop atTop ∧
  ∀ (k : ℕ) (τ : Equiv.Perm (Fin k)),
    Tendsto (fun m => permDensity τ (s m).2) atTop (𝓝 (limitDensity τ Z))

end PermLimits.Shared


