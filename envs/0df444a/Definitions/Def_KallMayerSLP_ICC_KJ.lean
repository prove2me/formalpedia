-- Prove2me | Definitions.Def_KallMayerSLP_ICC_KJ
-- name    : KallMayerSLP_ICC_KJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:52.674256+00:00
-- url     : https://prove2.me/theorems/7f7611a6-e276-487c-9588-b72ebcc90084
-- title:
--   Joint integrated probability function $K_J(x)$
-- statement:
--   With positive parts taken componentwise, the **joint integrated probability function** is
--   $$
--   K_J(x)=\mathbb E_\xi\Big[\max_{1\le i\le s}\zeta_i^+(x,\xi)\Big].
--   $$
--   It measures the expected size of the largest violation among the $s$ rows of $T(\xi)x\le h(\xi)$.
--
--   **Formalization Note** The maximum is `Finset.sup'` over the nonempty `Fin s`, so $s\ge 1$ is an instance argument and $s=0$ has no junk value. $\mathbb E_\xi$ is the Bochner integral against the law `P`, which is $0$ when the integrand is not integrable; every theorem using `KJ` assumes integrability of $T,h$ or works with a finite discrete law.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.1.2, p.155 (PDF 165)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_zetaVec

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **The joint integrated probability function `K_J(x) = 𝔼_ξ[max_{1≤i≤s} ζᵢ⁺(x, ξ)]`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §4.1.2, p.155 (PDF 165):
`K_J(x) := ρ⁺_jic(ζ(x, ξ)) = 𝔼_ξ[max_{1≤i≤s} ζᵢ⁺(x, ξ)]`, with positive parts taken componentwise
(pp.154–155) and `z⁺ = max{0, z}`.

**Formalization Note.** The maximum over `i` is `Finset.sup'` over the nonempty `Fin s`, so `s ≥ 1`
is carried by the instance argument and there is no junk value at `s = 0`. `P` is the law of `ξ` on
`Ξ`; `𝔼_ξ` is the Bochner integral, which is `0` when the integrand is not integrable, so every
theorem about `K_J` either assumes `T` and `h` integrable (p.149) or uses a finite discrete law. -/
noncomputable def KJ {Ξ : Type*} [MeasurableSpace Ξ] {s n : ℕ} [Nonempty (Fin s)] (P : Measure Ξ)
    (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ ξ, Finset.univ.sup' Finset.univ_nonempty (fun i => max 0 (zetaVec T h x ξ i)) ∂P

end KallMayerSLP.ICC


