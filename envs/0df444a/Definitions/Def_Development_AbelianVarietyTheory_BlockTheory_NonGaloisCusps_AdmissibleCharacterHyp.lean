-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_AdmissibleCharacterHyp
-- name    : Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_AdmissibleCharacterHyp
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:02:06.841818+00:00
-- url     : https://prove2.me/theorems/6dcd32bc-c88d-4568-83fd-63495ffcdc06
-- title:
--   Admissible Character Hyp
-- statement:
--   Definitions and structural lemmas for Admissible Character Hyp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/NonGaloisCusps/AdmissibleCharacterHyp.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_GlobalTheory_AdmLoc_exData_T1_T2_T3_fortyOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses
open Formalism.BasicNotions GlobalTheory.AdmLoc TensorProduct
open ReciprocityTheory.Def (H1)
variable {l : ℕ} [Fact l.Prime]
abbrev Gal (K LL : Loc.FinExt l) : Type 1 := GalData ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)
def Hyp (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) : Prop :=
  Standing P K LL emb Γ.lam ∧ IsTopGal (P.PD K) emb D Γ ∧ D.T1 l ∧ D.T2 l ∧ D.T3 l
def admissibleClassesTwistedChar (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) (c : ℕ) (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] :
    Set (H1 (twCoef (Γ.Wchi c) Γ.χ₁ X) ⊤) :=
  adm (P.PD K) emb Γ D.t D.Ut (Γ.Wchi c) X
def Stmt (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n r : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (D : TopData n r)
    (Γ : Gal K LL), Hyp P K LL emb D Γ →
    ∀ c : ℕ, 2 ≤ c → c ≤ D.t →
    ∀ (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] [Finite X],
      admissibleClassesTwistedChar P K LL emb D Γ c X = {0}
def RealisationStatementAll (L : LocTheory) : Prop := ∀ (l : ℕ) [Fact l.Prime], Stmt (L l)
example : 2 ≤ exData.t ∧ exData.T1 41 ∧ exData.T2 41 ∧ exData.T3 41 := ⟨le_rfl, exData_T1_T2_T3_fortyOne⟩
end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses


