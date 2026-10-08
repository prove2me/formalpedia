-- Prove2me | solution 1 for ArrowDebreu.ThmII.budget_slack_on_Peps
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T15:47:07.338909+00:00
-- url     : https://prove2.me/submissions/1ca0199f-ed8d-4a61-98c6-1932ebfe43c8

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

open ArrowDebreu.Shared ArrowDebreu.ThmII in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ)))
    (p : Fin l → ℝ) (hp : p ∈ priceSimplexEps E ε) (i : Fin m) :
    ∃ x ∈ E.X i, p ⬝ᵥ x < p ⬝ᵥ E.ζ i := by
  obtain ⟨x, hx, hle, h, hh, hlt⟩ := hE.IVa' i
  refine ⟨x, hx, ?_⟩
  obtain ⟨⟨hp0, _⟩, hpe⟩ := hp
  have hph : 0 < p h := lt_of_lt_of_le hε (hpe h hh)
  have key : 0 < p ⬝ᵥ (E.ζ i - x) := by
    rw [dotProduct]
    have hnn : ∀ k ∈ (Finset.univ : Finset (Fin l)), 0 ≤ p k * (E.ζ i - x) k := by
      intro k _
      exact mul_nonneg (hp0 k) (by simpa [Pi.sub_apply] using sub_nonneg.mpr (hle k))
    have hpos : 0 < p h * (E.ζ i - x) h := by
      apply mul_pos hph
      simpa [Pi.sub_apply] using sub_pos.mpr hlt
    exact lt_of_lt_of_le hpos (Finset.single_le_sum hnn (Finset.mem_univ h))
  rw [dotProduct_sub] at key
  linarith
