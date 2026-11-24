-- Prove2me | Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
-- name    : LeanPool_BlockSpectralSensitivity_Main
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:15:28.377731+00:00
-- url     : https://prove2.me/theorems/555ebe47-230d-46eb-a091-709035ea6504
-- title:
--   Main
-- statement:
--   Definitions and structural lemmas for Main, from Alex Meiburg (Timeroot/BS_Lam) and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Block sensitivity vs squared spectral sensitivity separation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_Construction_codim_cert
public import Theorems.Thm_BSLambda_Construction_eq_gateCoord_of_conflict
public import Theorems.Thm_BSLambda_Construction_exists_conflict_of_ne
public import Theorems.Thm_BSLambda_IsTournament_arc_or_arc
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm
public import Theorems.Thm_BSLambda_paley_isDR

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace BSLambda
namespace Final
open Construction
abbrev Idx : Type := ZMod 14011
def Arc : Idx → Idx → Bool := paleyArc 14011
theorem isDR_arc : IsDRTournamentWith Arc 7005 3502 := paley_isDR
theorem isTournament_arc : IsTournament Arc := isDR_arc.toIsTournament
abbrev r : ℕ := 144
abbrev certCodim : ℕ := 7149
noncomputable def U : ℝ := 7149 + 2 * Real.sqrt 150108
noncomputable def alpha : ℝ := 2 * Real.log 14011 / Real.log U
theorem codim_cert_eq (γ : Idx → Idx → Fin r) (i : Idx) :
    (cert Arc γ i).codim = certCodim := by
  rw [codim_cert isTournament_arc, isDR_arc.card_outNbrs]
theorem uniqueConflict_cert (γ : Idx → Idx → Fin r) (i j : Idx) (hij : i ≠ j) :
    ∃! v, (cert Arc γ i).Conflict (cert Arc γ j) v := by
  obtain ⟨v, hv⟩ := exists_conflict_of_ne isTournament_arc hij
  refine ⟨v, hv, fun w hw ↦ ?_⟩
  rcases isTournament_arc.arc_or_arc hij with h | h
  · rw [eq_gateCoord_of_conflict isTournament_arc hij.symm h hw,
      eq_gateCoord_of_conflict isTournament_arc hij.symm h hv]
  · rw [eq_gateCoord_of_conflict isTournament_arc hij h hw.symm,
      eq_gateCoord_of_conflict isTournament_arc hij h hv.symm]
def ListOne (γ : Idx → Idx → Fin r) : Prop :=
  ∀ i x, (cert Arc γ i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (cert Arc γ j).dist x = 1).card ≤ 3
def ListTwo (γ : Idx → Idx → Fin r) : Prop :=
  ∀ i x, (cert Arc γ i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (cert Arc γ j).dist x ≤ 2).card ≤ 7
@[simps]
def family (γ : Idx → Idx → Fin r) (h₁ : ListOne γ) (h₂ : ListTwo γ) :
    CertFamily (Coord Idx r) Idx where
  P := cert Arc γ
  c := certCodim
  A := 3
  B := 7
  codim_eq := codim_cert_eq γ
  uniqueConflict := uniqueConflict_cert γ
  listOne := h₁
  listTwo := h₂
variable {γ : Idx → Idx → Fin r}
end Final
end BSLambda


