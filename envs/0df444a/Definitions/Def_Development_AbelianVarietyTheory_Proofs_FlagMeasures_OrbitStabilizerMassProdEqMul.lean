-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:10:51.52227+00:00
-- url     : https://prove2.me/theorems/e3f68d6a-a0d6-55eb-89bb-4da0400e06f5
-- title:
--   Orbit Stabilizer Mass Prod Eq Mul
-- statement:
--   Definitions and structural lemmas for Orbit Stabilizer Mass Prod Eq Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassProdEqMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.ProdMass
noncomputable def wt (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) (x : α) : ℝ≥0∞ :=
  if x ∈ X then ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ else 0
variable {Γ G G' α β : Type} [Group Γ] [Group G] [Group G'] [MulAction G α] [MulAction G' β]
  [MulAction Γ (α × β)] (φ : Γ ≃* G × G')
  (hφ : ∀ (γ : Γ) (p : α × β), γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2))
include hφ in
theorem rel_iff (p q : α × β) : MulAction.orbitRel Γ (α × β) p q ↔
    MulAction.orbitRel G α p.1 q.1 ∧ MulAction.orbitRel G' β p.2 q.2 := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨γ, rfl⟩
    rw [hφ]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩
    refine ⟨φ.symm (g, g'), ?_⟩
    rw [hφ]
    simp [hg, hg']
def stabEquiv (p : α × β) : MulAction.stabilizer Γ p ≃
    MulAction.stabilizer G p.1 × MulAction.stabilizer G' p.2 where
  toFun γ := (⟨(φ γ).1, by
      have := hφ γ p
      rw [γ.2] at this
      exact (congrArg Prod.fst this).symm⟩, ⟨(φ γ).2, by
      have := hφ γ p
      rw [γ.2] at this
      exact (congrArg Prod.snd this).symm⟩)
  invFun g := ⟨φ.symm (g.1, g.2), by
    rw [MulAction.mem_stabilizer_iff, hφ]
    have h1 : (g.1 : G) • p.1 = p.1 := g.1.2
    have h2 : (g.2 : G') • p.2 = p.2 := g.2.2
    simp [h1, h2]⟩
  left_inv γ := by simp
  right_inv g := by simp
noncomputable def orbEquiv : MulAction.orbitRel.Quotient Γ (α × β) ≃
    MulAction.orbitRel.Quotient G α × MulAction.orbitRel.Quotient G' β where
  toFun := Quotient.lift (fun p => (Quotient.mk _ p.1, Quotient.mk _ p.2)) fun p q h => by
    obtain ⟨h1, h2⟩ := (rel_iff φ hφ p q).1 h
    exact Prod.ext (Quotient.sound h1) (Quotient.sound h2)
  invFun q := Quotient.mk _ (Quotient.out q.1, Quotient.out q.2)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h p =>
      refine Quotient.sound ((rel_iff φ hφ _ _).2 ⟨?_, ?_⟩)
      · exact Quotient.mk_out (s := MulAction.orbitRel G α) p.1
      · exact Quotient.mk_out (s := MulAction.orbitRel G' β) p.2
  right_inv q := by
    simp
end GlobalTheory.Mass.ProdMass


