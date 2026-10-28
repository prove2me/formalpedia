-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:17:35.344633+00:00
-- url     : https://prove2.me/theorems/60e8fc46-409c-4a37-9f93-ddc92fabf863
-- title:
--   Densified dimF le 22 / dimF pos (full combiner)
-- statement:
--   Full densified dimension-field bound on all $n<\mathrm{nNodes}=62478$:
--   $$\forall n<\mathrm{nNodes},\qquad 1\le\mathrm{dimF}(n)\le 22.$$
--   Assembled from packs `DimBound0`--`DimBound12`. Also $\mathrm{dimCF}\le 23$ and $\mathrm{dimCF}\,c=23\Leftrightarrow c=1$.
-- source:
--   R8 BitNB densified DIMT; DimBound packs 0-12

-- DimBound: densified dimF ≤ 22 / dimF > 0 (pack combiner).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound5
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound6
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound7
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound8
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound9
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound10
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound11
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound12
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.DimBound0
open IntMul.Kappa.R8.Bit.Oppbank.DimBound1
open IntMul.Kappa.R8.Bit.Oppbank.DimBound2
open IntMul.Kappa.R8.Bit.Oppbank.DimBound3
open IntMul.Kappa.R8.Bit.Oppbank.DimBound4
open IntMul.Kappa.R8.Bit.Oppbank.DimBound5
open IntMul.Kappa.R8.Bit.Oppbank.DimBound6
open IntMul.Kappa.R8.Bit.Oppbank.DimBound7
open IntMul.Kappa.R8.Bit.Oppbank.DimBound8
open IntMul.Kappa.R8.Bit.Oppbank.DimBound9
open IntMul.Kappa.R8.Bit.Oppbank.DimBound10
open IntMul.Kappa.R8.Bit.Oppbank.DimBound11
open IntMul.Kappa.R8.Bit.Oppbank.DimBound12

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound

theorem dimF_le_22 : ∀ n < SupG.nNodes, dimF n ≤ 22 := by
  intro n hn
  change n < 62478 at hn
  by_cases h0 : n < 5000
  · have hlo : 0 ≤ n := by omega
    exact DimBound0.dimF_le_22_range n hlo h0
  · by_cases h1 : n < 10000
    · have hlo : 5000 ≤ n := by omega
      exact DimBound1.dimF_le_22_range n hlo h1
    · by_cases h2 : n < 15000
      · have hlo : 10000 ≤ n := by omega
        exact DimBound2.dimF_le_22_range n hlo h2
      · by_cases h3 : n < 20000
        · have hlo : 15000 ≤ n := by omega
          exact DimBound3.dimF_le_22_range n hlo h3
        · by_cases h4 : n < 25000
          · have hlo : 20000 ≤ n := by omega
            exact DimBound4.dimF_le_22_range n hlo h4
          · by_cases h5 : n < 30000
            · have hlo : 25000 ≤ n := by omega
              exact DimBound5.dimF_le_22_range n hlo h5
            · by_cases h6 : n < 35000
              · have hlo : 30000 ≤ n := by omega
                exact DimBound6.dimF_le_22_range n hlo h6
              · by_cases h7 : n < 40000
                · have hlo : 35000 ≤ n := by omega
                  exact DimBound7.dimF_le_22_range n hlo h7
                · by_cases h8 : n < 45000
                  · have hlo : 40000 ≤ n := by omega
                    exact DimBound8.dimF_le_22_range n hlo h8
                  · by_cases h9 : n < 50000
                    · have hlo : 45000 ≤ n := by omega
                      exact DimBound9.dimF_le_22_range n hlo h9
                    · by_cases h10 : n < 55000
                      · have hlo : 50000 ≤ n := by omega
                        exact DimBound10.dimF_le_22_range n hlo h10
                      · by_cases h11 : n < 60000
                        · have hlo : 55000 ≤ n := by omega
                          exact DimBound11.dimF_le_22_range n hlo h11
                        · by_cases h12 : n < 62478
                          · have hlo : 60000 ≤ n := by omega
                            exact DimBound12.dimF_le_22_range n hlo h12
                          · omega

theorem dimF_pos : ∀ n < SupG.nNodes, 0 < dimF n := by
  intro n hn
  change n < 62478 at hn
  by_cases h0 : n < 5000
  · have hlo : 0 ≤ n := by omega
    exact DimBound0.dimF_pos_range n hlo h0
  · by_cases h1 : n < 10000
    · have hlo : 5000 ≤ n := by omega
      exact DimBound1.dimF_pos_range n hlo h1
    · by_cases h2 : n < 15000
      · have hlo : 10000 ≤ n := by omega
        exact DimBound2.dimF_pos_range n hlo h2
      · by_cases h3 : n < 20000
        · have hlo : 15000 ≤ n := by omega
          exact DimBound3.dimF_pos_range n hlo h3
        · by_cases h4 : n < 25000
          · have hlo : 20000 ≤ n := by omega
            exact DimBound4.dimF_pos_range n hlo h4
          · by_cases h5 : n < 30000
            · have hlo : 25000 ≤ n := by omega
              exact DimBound5.dimF_pos_range n hlo h5
            · by_cases h6 : n < 35000
              · have hlo : 30000 ≤ n := by omega
                exact DimBound6.dimF_pos_range n hlo h6
              · by_cases h7 : n < 40000
                · have hlo : 35000 ≤ n := by omega
                  exact DimBound7.dimF_pos_range n hlo h7
                · by_cases h8 : n < 45000
                  · have hlo : 40000 ≤ n := by omega
                    exact DimBound8.dimF_pos_range n hlo h8
                  · by_cases h9 : n < 50000
                    · have hlo : 45000 ≤ n := by omega
                      exact DimBound9.dimF_pos_range n hlo h9
                    · by_cases h10 : n < 55000
                      · have hlo : 50000 ≤ n := by omega
                        exact DimBound10.dimF_pos_range n hlo h10
                      · by_cases h11 : n < 60000
                        · have hlo : 55000 ≤ n := by omega
                          exact DimBound11.dimF_pos_range n hlo h11
                        · by_cases h12 : n < 62478
                          · have hlo : 60000 ≤ n := by omega
                            exact DimBound12.dimF_pos_range n hlo h12
                          · omega

theorem dimCF_nd_le_22 {n : ℕ} (hn : 1773 + n < codeBound) :
    dimCF (1773 + n) ≤ 22 := by
  have hne0 : ¬ (1773 + n = 0) := by omega
  have hne1 : ¬ (1773 + n = 1) := by omega
  have hge : ¬ (1773 + n < 1773) := by omega
  simp only [dimCF, hne0, hne1, hge, ↓reduceIte]
  have hn' : n < SupG.nNodes := by
    change n < 62478
    have : codeBound = 64251 := rfl
    omega
  simpa [Nat.add_sub_cancel] using dimF_le_22 n hn'

theorem dimCF_le_23 {c : ℕ} (hc : c < codeBound) : dimCF c ≤ 23 := by
  by_cases h0 : c = 0
  · subst h0; simp [dimCF]
  by_cases h1 : c = 1
  · subst h1; simp [dimCF]
  by_cases hPT : c < 1773
  · simp only [dimCF, h0, h1, hPT, ↓reduceIte]; omega
  · have : c = 1773 + (c - 1773) := by omega
    have hn : 1773 + (c - 1773) < codeBound := by omega
    rw [this]; exact le_trans (dimCF_nd_le_22 hn) (by omega)

theorem dimCF_eq_23_iff {c : ℕ} (hc : c < codeBound) :
    dimCF c = 23 ↔ c = 1 := by
  constructor
  · intro h
    by_cases h0 : c = 0
    · subst h0; simp [dimCF] at h
    by_cases h1 : c = 1
    · exact h1
    by_cases hPT : c < 1773
    · simp only [dimCF, h0, h1, hPT, ↓reduceIte] at h; omega
    · simp only [dimCF, h0, h1, hPT, ↓reduceIte] at h
      have hn : c - 1773 < SupG.nNodes := by
        change c - 1773 < 62478
        have : codeBound = 64251 := rfl
        omega
      have hle := dimF_le_22 (c - 1773) hn
      omega
  · intro h; subst h; simp [dimCF]

end IntMul.Kappa.R8.Bit.Oppbank.DimBound


