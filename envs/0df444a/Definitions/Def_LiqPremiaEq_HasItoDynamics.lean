-- Prove2me | Definitions.Def_LiqPremiaEq_HasItoDynamics
-- name    : LiqPremiaEq_HasItoDynamics
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:13.973212+00:00
-- url     : https://prove2.me/theorems/b74a44a2-0c13-4f10-923a-0852e3afb012
-- title:
--   Itô dynamics $dX_t=a_t\,dt+b_t\,dW_t$ on $[0,T]$
-- statement:
--   Let $W$ be a $D$-dimensional Brownian motion for the filtration $(\mathcal F_t)$. A process $X$ with values in $\mathbb R^m$ **has Itô dynamics** $dX_t=a_t\,dt+b_t\,dW_t$ on $[0,T]$, with drift $a$ and diffusion matrix $b\in\mathbb R^{m\times D}$, if there are Itô integrals $J^{ij}=\int_0^\cdot b^{ij}_s\,dW^j_s$ such that for every $t\in[0,T]$, almost surely, $a$ is integrable on $[0,t]$ and
--
--   $$X_t=X_0+\int_0^t a_s\,ds+\sum_{j=1}^D J^{ij}_t\qquad\text{for each component } i.$$
--
--   This is the meaning of the differential notation in the price dynamics (2.2) and in the FBSDE of Lemma 4.2.
--
--   **Formalization Note** The Itô integral is the published `Peng1990.SMP.IsItoIntegral` (the $L^2$ limit of simple adapted integrals, for the given filtration), applied to the integrand stopped at $T$. A terminal condition $X_T=\zeta$ is stated separately.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, eq. (2.2), p.4; Lemma 4.2, p.7

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

open MeasureTheory
open scoped NNReal

namespace LiqPremiaEq

/-- `X` has Itô dynamics `dX_t = a_t dt + b_t dW_t` on `[0, T]`, for a `ι`-dimensional process
`X`, a drift `a` and a diffusion matrix `b ∈ ℝ^{ι×D}`: there are Itô integral processes
`J i j = ∫₀^· b^{ij} dW^j` (in the sense of `Peng1990.SMP.IsItoIntegral`, for the filtration
`𝓕`) such that for every `t ∈ [0, T]`, almost surely, `s ↦ a_s` is integrable on `[0, t]` and
`X_t = X_0 + ∫₀ᵗ a_s ds + ∑ⱼ J i j t` componentwise.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, eq. (2.2), p.4, and Lemma 4.2, p.7 (the meaning of
"dX_t = a_t dt + b_t dW_t").

**Formalization Note** The integrand is the diffusion stopped at `T`, `b (min t T)`, so that its
values after the horizon play no role. A terminal condition `X_T = ζ` is stated separately. -/
def HasItoDynamics {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*} [Fintype ι] {D : ℕ}
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin D → ℝ) (X : ℝ≥0 → Ω → ι → ℝ) (a : ℝ≥0 → Ω → ι → ℝ)
    (b : ℝ≥0 → Ω → Matrix ι (Fin D) ℝ) : Prop :=
  ∃ J : ι → Fin D → ℝ≥0 → Ω → ℝ,
    (∀ i j, Peng1990.SMP.IsItoIntegral 𝓕 P T (fun t ω => W t ω j)
      (fun t ω => b (min t T) ω i j) (J i j)) ∧
    ∀ t ≤ T, ∀ᵐ ω ∂P,
      IntegrableOn (fun s : ℝ => a s.toNNReal ω) (Set.Icc 0 (t : ℝ)) ∧
      ∀ i, X t ω i = X 0 ω i + (∫ s in Set.Icc (0 : ℝ) t, a s.toNNReal ω) i + ∑ j, J i j t ω

end LiqPremiaEq


