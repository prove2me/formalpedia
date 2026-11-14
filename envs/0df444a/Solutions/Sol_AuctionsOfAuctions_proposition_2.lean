-- Prove2me | solution 1 for AuctionsOfAuctions.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Albert
-- created : 2026-11-13T10:00:51.887611+00:00
-- url     : https://prove2.me/submissions/d4a6ce85-c171-43c0-ac39-5b2cc8d2fe93

import Theorems.Thm_AuctionsOfAuctions_proposition_1
import Theorems.Thm_AuctionsOfAuctions_revenue_ranking_fixed_reserve
import Theorems.Thm_AuctionsOfAuctions_advertiser_profit_strictAntiOn

open AuctionsOfAuctions

theorem solution (D : ValuationDist) (hreg : D.IsRegular) (Rd Re : ℝ)
    (hRd : Rd ∈ Set.Icc (0 : ℝ) 1) (hRe : Re ∈ Set.Icc (0 : ℝ) 1)
    (hmaxd : IsMaxOn D.revDir (Set.Icc 0 1) Rd)
    (hmaxe : IsMaxOn D.revEx (Set.Icc 0 1) Re) :
    D.revEx Re < D.revDir Rd ∧ D.advertiserProfit Re < D.advertiserProfit Rd := by
  obtain ⟨hinterior, _, horder, _⟩ := proposition_1 D hreg
  have hRe' : Re ∈ Set.Ico (0 : ℝ) 1 := ⟨hRe.1, (hinterior Re hRe hmaxe).1.2⟩
  exact ⟨(revenue_ranking_fixed_reserve D Re hRe').2.2.trans_le (hmaxd hRe),
    advertiser_profit_strictAntiOn D hRd hRe (horder Rd hRd Re hRe hmaxd hmaxe)⟩
