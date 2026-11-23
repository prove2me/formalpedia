-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:37.681189+00:00
-- url     : https://prove2.me/theorems/043913d5-359f-4990-b5d2-4c980110f0d9
-- title:
--   Is Comb In
-- statement:
--   Definitions and structural lemmas for Is Comb In, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsCombIn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SecGlue
def chartHom {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] (u : Sp S ⟶ Y)
    (h : u ⁻¹ᵁ V = ⊤) : Γ(Y, V) →+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (u.appLE V ⊤ h.ge).hom
def IsCombIn {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {ι : Type} [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) : Prop :=
  ∃ (hu : u ⁻¹ᵁ V = ⊤) (hc : c ⁻¹ᵁ V = ⊤) (hw : ∀ i, w i ⁻¹ᵁ V = ⊤), ∀ x : Γ(Y, V),
    chartHom V c hc x = chartHom V u hu x + ∑ i, a i * (chartHom V (w i) (hw i) x - chartHom V u hu x)
end GlobalTheory.SecGlue


