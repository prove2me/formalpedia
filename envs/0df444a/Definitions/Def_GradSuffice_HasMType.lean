-- Prove2me | Definitions.Def_GradSuffice_HasMType
-- name    : GradSuffice_HasMType
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:34.856627+00:00
-- url     : https://prove2.me/theorems/82b919c4-f052-4d9a-ba0b-9a1be13cbd5a
-- title:
--   $B^\star$ has M-type $p$ with constant $C$
-- statement:
--   For $p\ge 1$ and $C\in\mathbb R$, the dual ball $B^\star$ has **martingale type (M-type) $p$ with constant $C$** if for every $m\ge 1$ and every $B^\star$-valued adaptive sequence $\bar\xi=(\xi_1,\dots,\xi_m)$,
--   $$\mathbb E_\sigma\Big[\Big\|\sum_{i=1}^m\sigma_i\xi_i(\sigma_{<i})\Big\|_\star^p\Big]\le C\Big(\sum_{i=1}^m\mathbb E_\sigma\big[\|\xi_i(\sigma_{<i})\|_\star^p\big]\Big),$$
--   where $\sigma_1,\dots,\sigma_m$ are independent uniform signs. Nontrivial M-type ($1<p\le2$) is item 4 of Theorem 1.
--
--   **Formalization Note** $\mathbb E_\sigma$ is the average over the $2^m$ sign strings and the power is the real power `Real.rpow`.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §2, p.6, Eq. (3)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_signedSum

namespace GradSuffice

/-- **`B⋆` has M-type `p` with constant `C`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §2, p.6, Eq. (3): "`B⋆` is said to have
bounded martingale type (M-type), or more accurately M-type `p` with constant `C` if, for every
`m ≥ 1` and every adaptive sequence `ξ̄`,
`E_σ[‖∑_{i=1}^m σᵢξᵢ(σ<ᵢ)‖⋆^p] ≤ C (∑_{i=1}^m E_σ[‖ξᵢ(σ<ᵢ)‖⋆^p])`."

**Formalization Note.** Adaptive sequences are `B⋆`-valued, as defined on p.5. `E_σ` is the
average over the `2^m` sign strings; `‖·‖^p` is the real power `Real.rpow`. -/
def HasMType (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (p C : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) m, IsDualValued ξ →
    (2 ^ m : ℝ)⁻¹ * ∑ σ : Fin m → Bool, ‖signedSum ξ σ‖ ^ p ≤
      C * ∑ i : Fin m, (2 ^ m : ℝ)⁻¹ * ∑ σ : Fin m → Bool, ‖ξ i (NondualOpt.histPrefix σ i)‖ ^ p

end GradSuffice


