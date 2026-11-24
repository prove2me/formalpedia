-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:23.092383+00:00
-- url     : https://prove2.me/theorems/d9748680-e77e-4298-a746-641c5826f3a5
-- title:
--   Is Affine Of Is Affine Pullback Quotient Of Is Nilpotent
-- statement:
--   Definitions and structural lemmas for Is Affine Of Is Affine Pullback Quotient Of Is Nilpotent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsAffineOfIsAffinePullbackQuotientOfIsNilpotent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe u
namespace GlobalTheory.AffineThickening
noncomputable def rs {Y : Scheme.{u}} {U V : Y.Opens} (h : V ≤ U) : Γ(Y, U) →+* Γ(Y, V) :=
  (Y.presheaf.map (homOfLE h).op).hom
variable {Z Y : Scheme.{u}} (i : Z ⟶ Y)
def Lifts (U : Y.Opens) (a : Γ(Y, U)) (r : Γ(Z, ⊤)) : Prop :=
  (i.app U).hom a = rs le_top r
variable {i}
namespace Lifts
variable {U V : Y.Opens} {a b : Γ(Y, U)} {r s : Γ(Z, ⊤)}
end Lifts
section Cover
variable [IsClosedImmersion i] [Surjective i]
  (hK : ∀ U : Y.Opens, IsAffineOpen U → ∀ a b : Γ(Y, U), Lifts i U a 0 → Lifts i U b 0 → a * b = 0)
  {ι : Type*} {f : ι → Γ(Z, ⊤)} {U : ι → Y.Opens} (hU : ∀ j, IsAffineOpen (U j))
  (hD : ∀ j, i ⁻¹ᵁ U j = Z.basicOpen (f j))
  {s : Γ(Z, ⊤)} {σ : ∀ j, Γ(Y, U j)} (hσ : ∀ j, Lifts i (U j) (σ j) s)
variable (i σ) in

def IsCoboundary (r : Γ(Z, ⊤)) : Prop :=
  ∃ ρ t : ∀ j, Γ(Y, U j), (∀ j, Lifts i (U j) (ρ j) r) ∧ (∀ j, Lifts i (U j) (t j) 0) ∧
    ∀ j k, rs (inf_le_left : U j ⊓ U k ≤ U j) (t j) - rs inf_le_right (t k) =
      rs inf_le_left (ρ j) * (rs inf_le_left (σ j) - rs inf_le_right (σ k))
end Cover
end GlobalTheory.AffineThickening
namespace GlobalTheory
end GlobalTheory


