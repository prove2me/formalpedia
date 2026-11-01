-- Prove2me | Definitions.Def_DRORSEquiv_worstCaseLoss
-- name    : DRORSEquiv_worstCaseLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:12.339869+00:00
-- url     : https://prove2.me/theorems/e12c1db9-a6ce-4805-a8f9-8eff180e0506
-- title:
--   Worst-case loss $h(x,k)$ in the constraints of (DRO) and (RS)
-- statement:
--   For a decision $x$ and a fragility (dual multiplier) $k\in\mathbb R$, the **worst-case loss** is
--
--   $$h(x,k)=\frac1S\sum_{s\in[S]}\sup_{z\in\mathcal Z}\big\{f(x,z)-k\,\rho(z,\hat z_s)\big\}\in(-\infty,+\infty].$$
--
--   It is the left-hand side of the first constraint of both Problem (DRO) (p.7) and Problem (RS) (p.8); by Wasserstein duality it is the worst-case expected cost penalized by $k$ times the transport distance from $\mathbb P^\dagger$.
--
--   **Formalization Note** The supremum over an unbounded support may be $+\infty$, so $h$ takes values in `EReal`. When every sample lies in $\mathcal Z$ no term is $-\infty$.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), (DRO), p.7, and (RS), p.8

import Mathlib
import Definitions.Def_DRORSEquiv_Model

namespace DRORSEquiv

/-- **The worst-case loss** shared by the constraints of Problems (DRO) and (RS)
(Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), (DRO) p.7 and (RS) p.8):
`h(x, k) = (1/S) ∑_{s ∈ [S]} sup_{z ∈ Z} { f(x, z) − k ρ(z, ẑ_s) }`.

**Formalization Note.** The supremum over a possibly unbounded support can be `+∞`, so `h` is
`EReal`-valued (`⨆` in `EReal`). When every sample lies in `Z` each supremum is at least the real
number `f(x, ẑ_s) − k ρ(ẑ_s, ẑ_s)`, so no term is `−∞` and the sum has no `⊥ + ⊤`. -/
noncomputable def worstCaseLoss {E Ω : Type*} {S : ℕ} (M : Model E Ω S) (x : E) (k : ℝ) :
    EReal :=
  ((1 / (S : ℝ) : ℝ) : EReal) *
    ∑ s : Fin S, ⨆ z ∈ M.Z, ((M.f x z - k * M.ρ z (M.zhat s) : ℝ) : EReal)

end DRORSEquiv


