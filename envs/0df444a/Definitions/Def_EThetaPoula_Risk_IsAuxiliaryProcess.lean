-- Prove2me | Definitions.Def_EThetaPoula_Risk_IsAuxiliaryProcess
-- name    : EThetaPoula_Risk_IsAuxiliaryProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:22.433989+00:00
-- url     : https://prove2.me/theorems/736dff73-003d-47d5-ad40-9e54788ff188
-- title:
--   The auxiliary process $\bar\zeta^{\lambda,n}$ of (43)
-- statement:
--   Let $T\equiv T(\lambda):=\lfloor1/\lambda\rfloor$. The auxiliary process $\bar\zeta^{\lambda,n}_t$, $t\ge nT$, starts from the value $\bar\theta^\lambda_{nT}$ of the interpolation at time $nT$ and follows the Langevin dynamics (43): almost surely, for all $t\ge nT$,
--   $$
--   \bar\zeta^{\lambda,n}_t=\bar\theta^\lambda_{nT}-\lambda\int_{nT}^t h(\bar\zeta^{\lambda,n}_s)\,ds+\sqrt{2\lambda\beta^{-1}}\,(B^\lambda_t-B^\lambda_{nT}),
--   $$
--   with almost surely continuous paths on $[nT,\infty)$.
--
--   **Formalization Note** The pathwise integral equation replaces the SDE, as for (37). Values before $nT$ play no role.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, (43), p.24

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
import Definitions.Def_EThetaPoula_Risk_timeChanged

open MeasureTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- `T ≡ T(λ) := ⌊1/λ⌋`, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.24. -/
noncomputable def blockLength (lam : ℝ) : ℕ := ⌊1 / lam⌋₊

/-- `zb` is the auxiliary process `ζ̄^{λ,n}_t := ζ_t^{nT, θ̄^λ_{nT}, λ}`, `t ≥ nT`, of (43), Lim,
Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.24: it starts from the value of the
interpolation `θb` at time `nT` and follows
`dζ_t = −λ h(ζ_t) dt + √(2λβ⁻¹) dB^λ_t`.

**Formalization Note.** As for (37), this is the pathwise integral equation with almost surely
continuous paths on `[nT, ∞)`. Values of `zb` before `nT` play no role. -/
def Model.IsAuxiliaryProcess {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (B : ℝ≥0 → Ω → Eucl d) (lam β : ℝ) (θb : ℝ≥0 → Ω → Eucl d) (n : ℕ)
    (zb : ℝ≥0 → Ω → Eucl d) : Prop :=
  let t₀ : ℝ≥0 := n * blockLength lam
  (∀ᵐ ω ∂S.P, ContinuousOn (fun t => zb t ω) (Set.Ici t₀)) ∧
  ∀ᵐ ω ∂S.P, ∀ t : ℝ≥0, t₀ ≤ t → zb t ω =
    θb t₀ ω - lam • (∫ s in (t₀ : ℝ)..t, S.h (zb s.toNNReal ω))
      + √(2 * lam * β⁻¹) • (timeChangedBM B lam t ω - timeChangedBM B lam t₀ ω)

end EThetaPoula.Risk


