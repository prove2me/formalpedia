-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:00.471621+00:00
-- url     : https://prove2.me/theorems/b1749543-8616-4477-a901-ce043e2c0e26
-- title:
--   Eq Zero Of Forall Pow Dvd Germ
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Forall Pow Dvd Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqZeroOfForallPowDvdGerm.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.PrimeSection
section Integral
variable {X : Scheme.{u}} [IsIntegral X]
theorem genericPoint_mem {W : X.Opens} {x : X} (hx : x ∈ W) : genericPoint X ∈ W := ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hx⟩
theorem genericPoint_mem_basicOpen {W : X.Opens} {s : Γ(X, W)} (hs : s ≠ 0) :
    genericPoint X ∈ X.basicOpen s := by
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((basicOpen_eq_bot_iff s).mp h)
  obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen s := by
    by_contra hcon
    exact hne (eq_bot_iff.mpr fun x hx => (hcon ⟨x, hx⟩).elim)
  exact genericPoint_mem hx
end Integral
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
include hp in
theorem ne_zero : t ≠ 0 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  intro ht
  have := (hp V hV hηV).ne_zero
  rw [ht, map_zero] at this
  exact this rfl
variable [IsIntegral X]
include hp in
theorem genericPoint_mem_inf {W : X.Opens} (h : η ∈ W) : genericPoint X ∈ W ⊓ X.basicOpen t := ⟨genericPoint_mem h, genericPoint_mem_basicOpen (ne_zero hp)⟩
section Cocycle
variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
variable [IsLocallyNoetherian X]
end Cocycle
end GlobalTheory.PrimeSection


