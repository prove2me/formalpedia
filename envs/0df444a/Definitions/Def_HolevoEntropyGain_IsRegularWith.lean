-- Prove2me | Definitions.Def_HolevoEntropyGain_IsRegularWith
-- name    : HolevoEntropyGain_IsRegularWith
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:57.724561+00:00
-- url     : https://prove2.me/theorems/a17fb67e-0cb4-4962-a105-cd3bb37f8d73
-- title:
--   Regular channel with $\Phi[I] = A$
-- statement:
--   Let $\Phi$ be a channel on $\ell^2(I)$ and $A$ a bounded operator. $\Phi$ is **regular with $\Phi[I] = A$** if $A$ is positive and there is a countable Kraus representation $\Phi[\rho] = \sum_j V_j\rho V_j^*$, $\sum_j V_j^*V_j = I$, such that
--
--   $$
--   \sum_j \|V_j^*\psi\|^2 = \langle \psi, A\psi\rangle \qquad \text{for every } \psi \in \ell^2(I).
--   $$
--
--   Condition (2) of the paper, $\sum_j\|V_j^*\psi\|^2<\infty$, makes the increasing partial sums $\sum_{j\le n}V_jV_j^*$ converge weakly (and strongly) to a bounded positive operator, denoted $\Phi[I]$; this definition names that limit $A$. For a non-regular channel, such as the completely depolarizing channel, $\Phi[I]$ is undefined.
--
--   **Formalization Note** Increasing positive partial sums converge weakly to $A$ exactly when their quadratic forms converge to that of $A$, so the quadratic-form condition is the paper's $\uparrow$. Finite Kraus families are included.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eqs. (1)–(2), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (IsKrausRepresentation)

namespace HolevoEntropyGain

/-- `Φ` is regular with `Φ[I] = A`: `A` is a positive bounded operator and some Kraus representation
`(Vⱼ)` of `Φ` has `∑ⱼ ‖Vⱼ* ψ‖² = ⟨ψ, Aψ⟩` for every `ψ`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eqs. (1)–(2), p.2, PDF p.2).

**Formalization Note** (R5) The partial sums `∑ⱼ VⱼVⱼ*` are increasing and positive, so they converge
weakly (hence strongly) to the bounded `A`, written `↑` on p.2, exactly when their quadratic forms
converge to that of `A`. Finite Kraus families are the finite index types. -/
def IsRegularWith {I : Type} (Φ : Channel I I) (A : Hilbert I →L[ℂ] Hilbert I) : Prop :=
  A.IsPositive ∧ ∃ (J : Type) (_ : Countable J) (V : J → (Hilbert I →L[ℂ] Hilbert I)),
    IsKrausRepresentation Φ.val V ∧
      ∀ ψ : Hilbert I, HasSum (fun j => ‖ContinuousLinearMap.adjoint (V j) ψ‖ ^ 2)
        (RCLike.re (inner ℂ ψ (A ψ)))

end HolevoEntropyGain


