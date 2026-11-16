-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgGlue
-- name    : IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgGlue
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T18:23:37.395869+00:00
-- url     : https://prove2.me/theorems/f075448b-0104-49a8-9f5a-ea7261b0e087
-- title:
--   SegsR midA argRel glue over densified chunks
-- statement:
--   # SegsR midA argRel glue over densified chunks
--
--   Glue for the six densified midAPack argRel chunks: midAPack_split, midAPack_argRel, and argRel_of_midA_mem. Later-segs midA helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean definition name: `IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgGlue`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgGlue. Later-segs midA helper only; not a full-word W1F certificate. Uses densified MidADataD.

-- Later-segs midA helper only; not a full-word W1F / segsR / preloadHits certificate.
-- Imports densified MidADataD (not raw-n MidAData).
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADataD
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgC0
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgC1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgC2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgC3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgC4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSegsRMidADecArgC5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

theorem mem_append_midAArgRel {A B : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hA : ∀ g ∈ A, argRel (gateTp g) (gateN g) = true ∧ argRel (gateTb g) (gateN g) = true)
    (hB : ∀ g ∈ B, argRel (gateTp g) (gateN g) = true ∧ argRel (gateTb g) (gateN g) = true) :
    ∀ g ∈ A ++ B, argRel (gateTp g) (gateN g) = true ∧ argRel (gateTb g) (gateN g) = true := by
  intro g hg
  cases List.mem_append.mp hg with
  | inl h => exact hA g h
  | inr h => exact hB g h

theorem midAPack_split :
    midAPack = midAPack_c00 ++ midAPack_c01 ++ midAPack_c02 ++ midAPack_c03 ++ midAPack_c04 ++ midAPack_c05 := rfl

theorem midAPack_argRel :
    ∀ g ∈ midAPack,
      argRel (gateTp g) (gateN g) = true ∧
        argRel (gateTb g) (gateN g) = true := by
  rw [midAPack_split]
  exact mem_append_midAArgRel
    (mem_append_midAArgRel
      (mem_append_midAArgRel
        (mem_append_midAArgRel
          (mem_append_midAArgRel midAPack_argRel_c00 midAPack_argRel_c01)
          midAPack_argRel_c02)
        midAPack_argRel_c03)
      midAPack_argRel_c04)
    midAPack_argRel_c05

theorem argRel_of_midA_mem {g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ} (hg : g ∈ midAPack) :
    argRel (gateTp g) (gateN g) = true ∧
      argRel (gateTb g) (gateN g) = true :=
  midAPack_argRel g hg


