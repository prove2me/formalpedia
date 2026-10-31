-- Prove2me | Definitions.Def_KallMayerSLP_ICC_HJ
-- name    : KallMayerSLP_ICC_HJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:48.369293+00:00
-- url     : https://prove2.me/theorems/8f313c5e-4974-4d85-825a-e5c6f77ad410
-- title:
--   Joint integrated probability function $H_J(x)$
-- statement:
--   With negative parts taken componentwise, the **joint integrated probability function** is
--   $$
--   H_J(x)=\mathbb E_\xi\Big[\max_{1\le i\le s}\zeta_i^-(x,\xi)\Big].
--   $$
--   It is the function entering the joint integrated chance constraint $\mathbb E_\xi[\max_i\zeta_i^-(x,\xi)]\le\gamma$ when losses are negative values of $\zeta$.
--
--   **Formalization Note** The maximum is `Finset.sup'` over the nonempty `Fin s`. $\mathbb E_\xi$ is the Bochner integral against the law `P`; every theorem using `HJ` assumes integrability of $T,h$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §4.1.2, p.155 (PDF 165)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_zetaVec

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **The joint integrated probability function `H_J(x) = 𝔼_ξ[max_{1≤i≤s} ζᵢ⁻(x, ξ)]`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §4.1.2, p.155 (PDF 165):
`H_J(x) := ρ⁻_jic(ζ(x, ξ)) = 𝔼_ξ[max_{1≤i≤s} ζᵢ⁻(x, ξ)]`, with negative parts taken componentwise
(pp.154–155) and `z⁻ = max{0, −z}`.

**Formalization Note.** The maximum over `i` is `Finset.sup'` over the nonempty `Fin s`, so `s ≥ 1`
is carried by the instance argument. `P` is the law of `ξ` on `Ξ`; `𝔼_ξ` is the Bochner integral,
which is `0` when the integrand is not integrable, so every theorem about `H_J` assumes `T` and `h`
integrable (p.149). -/
noncomputable def HJ {Ξ : Type*} [MeasurableSpace Ξ] {s n : ℕ} [Nonempty (Fin s)] (P : Measure Ξ)
    (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ ξ, Finset.univ.sup' Finset.univ_nonempty (fun i => max 0 (-(zetaVec T h x ξ i))) ∂P

end KallMayerSLP.ICC


