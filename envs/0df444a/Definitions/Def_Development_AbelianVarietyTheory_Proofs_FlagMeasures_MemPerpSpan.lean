-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:00:43.887797+00:00
-- url     : https://prove2.me/theorems/8ffaf107-8060-4a63-b2ee-54aec7df9415
-- title:
--   Mem Perp Span
-- statement:
--   Definitions and structural lemmas for Mem Perp Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemPerpSpan.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.StdLat
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
noncomputable def pr {r : ℕ} (e es : Fin r → Fin n → E) (x : Fin n → E) : Fin n → E :=
  x - ∑ j, hf L Hm x (es j) • e j - ∑ j, hf L Hm x (e j) • es j
noncomputable def lat {r : ℕ} (e es : Fin r → Fin n → E) (A : Submodule L.O (Fin n → E)) :
    Submodule L.O (Fin n → E) :=
  Submodule.span L.O (Set.range e) ⊔
    (A ⊓ (perp L Hm (Submodule.span E (Set.range es))).restrictScalars L.O) ⊔
    Submodule.span L.O (Set.range es)
section
variable {L Hm} {r : ℕ} {e es : Fin r → Fin n → E} (hH : IsHerm L Hm)
  (hee : ∀ i j, hf L Hm (e i) (e j) = 0) (hss : ∀ i j, hf L Hm (es i) (es j) = 0)
  (hes : ∀ i j, hf L Hm (e i) (es j) = if i = j then 1 else 0)
include hH hes
variable {A : Submodule L.O (Fin n → E)}
variable (hXA : ∀ x ∈ Submodule.span E (Set.range e), x ∈ A)
  (hAp : ∀ x ∈ A, ∀ j, hf L Hm x (e j) = 0)
  (hd : ∀ y, (∀ j, hf L Hm y (e j) = 0) → ((∀ x ∈ A, hf L Hm x y ∈ L.O) ↔ y ∈ A))
end
end GlobalTheory.HL.StdLat


