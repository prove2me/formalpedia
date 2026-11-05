-- Prove2me | Definitions.Def_BrownianEnergyRep_rotation__ef917c
-- name    : BrownianEnergyRep_rotation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:03:53.957015+00:00
-- url     : https://prove2.me/theorems/ef917c32-5297-4edf-b5ed-77c52018241f
-- title:
--   The rotation $O_\varphi$ of (5.3)
-- statement:
--   For $\varphi\in H(G)$, the rotation of $W(\mathfrak g)$ is
--   $$
--   O_\varphi(w)=\int_0^\cdot\mathrm{Ad}_\varphi\,\delta w_s .
--   $$
--   Since the inner product is $\mathrm{Ad}$-invariant, $O_\varphi$ preserves $\nu$ (Lévy's criterion). It is the rotation in the energy representation.
--
--   **Formalization Note** $\varphi$ is absolutely continuous, so the integral is taken pathwise by integration by parts:
--   $$
--   (O_\varphi w)(t)=\mathrm{Ad}_{\varphi_t}w_t-\int_0^t\mathrm{Ad}_{\varphi_s}\big[\varphi^{-1}\varphi'(s),w_s\big]\,ds .
--   $$
--   This is defined for every $w$, is bounded and linear, and agrees $\nu$-a.e. with the stochastic integral.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, (5.3), p.18

import Mathlib
import Definitions.Def_BrownianEnergyRep_MatrixLieAlgebra
import Definitions.Def_BrownianEnergyRep_WienerGroup
import Definitions.Def_BrownianEnergyRep_FiniteEnergy
import Definitions.Def_BrownianEnergyRep_WienerPath
import Definitions.Def_BrownianEnergyRep_primitive

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- The rotation `O_ϕ(w) = ∫₀^· Ad_ϕ δw_s` of (5.3) (arXiv:1511.07378v1, (5.3), p.18).

**Formalization Note** `ϕ` is absolutely continuous, so the integral is taken pathwise by parts:
`(O_ϕ w)(t) = Ad_{ϕ_t} w_t − ∫₀ᵗ Ad_{ϕ_s} [ϕ⁻¹ϕ′(s), w_s] ds`, which equals
`Ad_{ϕ_t} w_t − ∫₀ᵗ [ϕ′ϕ⁻¹(s), Ad_{ϕ_s} w_s] ds`. This is defined for every `w`, and for
`ν`-almost every `w` it equals the stochastic integral of (5.3). -/
noncomputable def rotation {n : ℕ} {G : Subgroup (GL (Fin n) ℝ)} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : MatrixLieAlgebra G E)
    {T : ℝ} [hT : Fact (0 < T)] (ϕ : ↥(WienerGroup G T)) (w : ↥(WienerPath E T)) :
    ↥(WienerPath E T) :=
  (⟨⟨fun t => L.Ad ⟨ϕ.1 t, ϕ.2.1 t⟩ (w.1 t), by
      have hx : Continuous fun t : Icc (0 : ℝ) T => (⟨ϕ.1 t, ϕ.2.1 t⟩ : ↥G) :=
        (ϕ.1.continuous).subtype_mk _
      refine continuous_iff_continuousAt.2 fun t => ?_
      have h1 : ContinuousAt (fun u => L.Ad ⟨ϕ.1 u, ϕ.2.1 u⟩ (w.1 t)) t :=
        ((L.Ad_continuous (w.1 t)).comp hx).continuousAt
      have h2 : Tendsto (fun u => L.Ad ⟨ϕ.1 u, ϕ.2.1 u⟩ (w.1 u - w.1 t)) (𝓝 t) (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [LinearIsometryEquiv.norm_map]
        have := (w.1.continuous.tendsto t).sub_const (w.1 t)
        simpa using this.norm
      have h3 := h1.tendsto.add h2
      have h4 : ContinuousAt (fun u => L.Ad ⟨ϕ.1 u, ϕ.2.1 u⟩ (w.1 u)) t := by
        simpa [ContinuousAt, map_sub] using h3
      exact h4⟩, by
      have h0 : w.1 ⟨0, le_rfl, hT.out.le⟩ = 0 := w.2
      change L.Ad _ (w.1 ⟨0, le_rfl, hT.out.le⟩) = 0
      rw [h0, map_zero]⟩ : ↥(WienerPath E T)) -
    primitive T fun s => L.Ad (pathAt ϕ s) (L.bracket (leftLog L ϕ s) (wAt w s))

end BrownianEnergyRep


