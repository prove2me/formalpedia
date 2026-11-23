-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:54.432282+00:00
-- url     : https://prove2.me/theorems/285ce69e-cc66-4c06-bb8b-0925eff25b2f
-- title:
--   Highest Weight Integral
-- statement:
--   Definitions and structural lemmas for Highest Weight Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_ext_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
section Cols
variable {m : ℕ} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
lemma qr_colH_le (hi : Interl lam nu) (c : ℤ) : colH nu c ≤ colH lam c := by
  unfold colH
  rw [← Finset.card_map Fin.castSuccEmb]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ha.trans (hi a).1
lemma qr_colH_le' (hi : Interl lam nu) (c : ℤ) : colH lam c ≤ colH nu c + 1 := by
  unfold colH
  rw [← Finset.card_map (Fin.succEmb m)]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_insert_le (0 : Fin (m + 1)) _)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  induction x using Fin.cases with
  | zero => left; rfl
  | succ a => right; exact ⟨a, hx.trans (hi a).2, rfl⟩
lemma qr_colH_eq (hi : Interl lam nu) (c : ℤ) :
    colH lam c = colH nu c + if colH lam c = colH nu c + 1 then 1 else 0 := by
  have h1 := qr_colH_le hi c
  have h2 := qr_colH_le' hi c
  split_ifs with h <;> omega
end Cols
section J
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
def qr_can (nu : Fin m → ℤ) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  ⟨(univ : Finset (Fin (colH nu c))).map (Fin.castLEEmb (colH_le nu c)), by simp⟩
def qr_base (I' : TIdx nu) (c : ℤ) : {S : Finset (Fin m) // S.card = colH nu c} :=
  if h : c ∈ TCols nu then I' ⟨c, h⟩ else qr_can nu c
def qr_j (hi : Interl lam nu) (I' : TIdx nu) : TIdx lam := fun c =>
  ⟨qr_ext (colH lam c = colH nu c + 1) (qr_base I' c).1, by
    rw [qr_ext_card, (qr_base I' c).2]; exact (qr_colH_eq hi c).symm⟩
end J
end Formalism.InvariantFactorPaths.ColumnFamilies


