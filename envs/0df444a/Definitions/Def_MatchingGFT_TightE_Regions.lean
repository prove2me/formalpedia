-- Prove2me | Definitions.Def_MatchingGFT_TightE_Regions
-- name    : MatchingGFT_TightE_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:07.186652+00:00
-- url     : https://prove2.me/theorems/69543fe2-0efb-4a5d-9e42-51d956761735
-- title:
--   Rank down-sets, section lengths, local benchmarks, edge regions
-- statement:
--   Measurable down-sets of $(0,1)^2$, section lengths $\ell_B,\ell_S$ (zero on empty sections), the threshold-profit objectives, the benchmarks $P_S(\mathcal D)$, $P_B(\mathcal D)$, the first-best selection regions $\mathcal D_e^{\omega_{-e}}$ and the selection lengths $\ell_{B,e},\ell_{S,e}$.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §3.1–3.3, Appendix B, PDF pp. 12–13, 15, 25

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile

open MeasureTheory Set

namespace MatchingGFT.TightE

variable {B S : Type*}

/-- A measurable down-set of `(0, 1)²` (PDF p. 13). -/
structure IsRankDownSet (D : Set (ℝ × ℝ)) : Prop where
  measurable : MeasurableSet D
  subset : D ⊆ Ioo 0 1 ×ˢ Ioo 0 1
  down : ∀ ρ σ ρ' σ', (ρ, σ) ∈ D → 0 < ρ' → ρ' ≤ ρ → 0 < σ' → σ' ≤ σ → (ρ', σ') ∈ D

/-- `ℓ_B(σ) = sup {ρ ∈ (0, 1) : (ρ, σ) ∈ D}`, zero on an empty section (PDF p. 13; the real
`sSup ∅` is `0`, and the set is bounded by `1`). -/
noncomputable def sectionLengthBuyer (D : Set (ℝ × ℝ)) (σ : ℝ) : ℝ :=
  sSup {ρ : ℝ | ρ ∈ Ioo (0 : ℝ) 1 ∧ (ρ, σ) ∈ D}

/-- `ℓ_S(ρ) = sup {σ ∈ (0, 1) : (ρ, σ) ∈ D}`, zero on an empty section (PDF p. 13). -/
noncomputable def sectionLengthSeller (D : Set (ℝ × ℝ)) (ρ : ℝ) : ℝ :=
  sSup {σ : ℝ | σ ∈ Ioo (0 : ℝ) 1 ∧ (ρ, σ) ∈ D}

/-- The profit of the top-`x` threshold against cost `a`: `0` at `x = 0` (no trade), else
`x (Q_B(x) - a)` (PDF pp. 13, 25). -/
noncomputable def buyerThresholdProfit (QB : ℝ → ℝ) (a x : ℝ) : ℝ :=
  if x = 0 then 0 else x * (QB x - a)

/-- The profit of the bottom-`y` threshold against value `b`: `0` at `y = 0`, else
`y (b - Q_S(y))` (PDF pp. 13, 25). -/
noncomputable def sellerThresholdProfit (QS : ℝ → ℝ) (b y : ℝ) : ℝ :=
  if y = 0 then 0 else y * (b - QS y)

/-- `sup_{0 ≤ x < t} x (Q_B(x) - a)`. For `t = 0` the range is empty and the value is `0` (an empty
section contributes zero, PDF p. 13). -/
noncomputable def buyerSectionProfit (QB : ℝ → ℝ) (a t : ℝ) : ℝ :=
  sSup (buyerThresholdProfit QB a '' Ico 0 t)

/-- `sup_{0 ≤ y < t} y (b - Q_S(y))`, `0` for `t = 0`. -/
noncomputable def sellerSectionProfit (QS : ℝ → ℝ) (b t : ℝ) : ℝ :=
  sSup (sellerThresholdProfit QS b '' Ico 0 t)

/-- The horizontal posted-price benchmark `P_S(D)` (PDF p. 13). -/
noncomputable def benchmarkS (QB QS : ℝ → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ σ in Ioo (0 : ℝ) 1, buyerSectionProfit QB (QS σ) (sectionLengthBuyer D σ)

/-- The vertical procurement benchmark `P_B(D)` (PDF p. 13). -/
noncomputable def benchmarkB (QB QS : ℝ → ℝ) (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ ρ in Ioo (0 : ℝ) 1, sellerSectionProfit QS (QB ρ) (sectionLengthSeller D ρ)

/-- The law of the independent uniform ranks of all agents (PDF p. 9). -/
noncomputable def rankMeasure (B S : Type*) [Fintype B] [Fintype S] : Measure (Profile B S) :=
  (Measure.pi fun _ : B => volume.restrict (Ioo (0 : ℝ) 1)).prod
    (Measure.pi fun _ : S => volume.restrict (Ioo (0 : ℝ) 1))

/-- The types represented by a rank vector: `vᵢ = Qᵢ(ρᵢ)`, `cⱼ = Qⱼ(σⱼ)` (PDF p. 9). -/
noncomputable def rankProfile (m : Market B S) (ω : Profile B S) : Profile B S :=
  (fun i => buyerQuantile (m.buyerLaw i) (ω.1 i), fun j => sellerQuantile (m.sellerLaw j) (ω.2 j))

/-- The first-best selection region `𝒟_e^{ω₋ₑ}` of `e = (i, j)` (PDF p. 12). The entries `i`, `j` of `ω`
are overwritten, so the region depends on the external ranks `ω₋ₑ` only. -/
noncomputable def edgeRegion [DecidableEq B] [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) (e : B × S) (ω : Profile B S) : Set (ℝ × ℝ) :=
  {p | p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 ∧
    e ∈ firstBest m rank
      (updateSeller (updateBuyer (rankProfile m ω) e.1 (buyerQuantile (m.buyerLaw e.1) p.1)) e.2
        (sellerQuantile (m.sellerLaw e.2) p.2))}

/-- `ℓ_{B,e}(t₋ᵢ) = sup {ρ ∈ (0, 1) : e ∈ M*(Qᵢ(ρ), t₋ᵢ)}`, zero if empty (PDF p. 15). The entry `i`
of `t` is overwritten. -/
noncomputable def edgeSectionLengthBuyer [DecidableEq B] (m : Market B S)
    (rank : Finset (B × S) → ℕ) (e : B × S) (t : Profile B S) : ℝ :=
  sSup {ρ : ℝ | ρ ∈ Ioo (0 : ℝ) 1 ∧
    e ∈ firstBest m rank (updateBuyer t e.1 (buyerQuantile (m.buyerLaw e.1) ρ))}

/-- The seller-quantile selection length `ℓ_{S,e}` (PDF pp. 15, 25). -/
noncomputable def edgeSectionLengthSeller [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) (e : B × S) (t : Profile B S) : ℝ :=
  sSup {σ : ℝ | σ ∈ Ioo (0 : ℝ) 1 ∧
    e ∈ firstBest m rank (updateSeller t e.2 (sellerQuantile (m.sellerLaw e.2) σ))}

end MatchingGFT.TightE


