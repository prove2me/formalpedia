-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_GreenHCLabelOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_GreenHCLabelOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:45.568772+00:00
-- url     : https://prove2.me/theorems/d5b401b3-4e73-4e27-adb0-f93054a9ac63
-- title:
--   Green HCLabel Of
-- statement:
--   Definitions and structural lemmas for Green HCLabel Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HarishChandraLabels/GreenHCLabelOf.lean

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES CategoryTheory Polynomial
namespace PI.GreenHCLabel
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
def HCDisjoint : Prop :=
  ∀ (n s s' : ℕ) (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (lam' : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K)),
    Function.Surjective b → Function.Surjective b' →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) →
    ∀ τ : FDRep ℂ (GL (Fin n) K), Simple τ → IsConstituent τ (hcRep K b lam) → IsConstituent τ (hcRep K b' lam') →
    ∃ (π : Fin s ≃ Fin s') (e : ∀ c, {i // b i = c} ≃ {i // b' i = π c}), ∀ c, Nonempty (transp (e c) (lam c) ≅ lam' (π c))
def LabelTransp (C : LabelConv K) : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)) (P : K[X]),
    HasCuspLabel C τ P ↔ HasCuspLabel C (transp e τ) P
def LabelIso (C : LabelConv K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (τ τ' : FDRep ℂ (GL ι K)) (P : K[X]),
    Nonempty (τ ≅ τ') → HasCuspLabel C τ P → HasCuspLabel C τ' P
def TranspKeeps : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (τ : FDRep ℂ (GL ι K)),
    (Simple τ → Simple (transp e τ)) ∧ (IsCuspidal K τ → IsCuspidal K (transp e τ))
def CuspLabelAny (C : LabelConv K) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (τ : FDRep ℂ (GL ι K)), Simple τ → IsCuspidal K τ →
    ∃! P : K[X], HasCuspLabel C τ P
variable {K}
end PI.GreenHCLabel


