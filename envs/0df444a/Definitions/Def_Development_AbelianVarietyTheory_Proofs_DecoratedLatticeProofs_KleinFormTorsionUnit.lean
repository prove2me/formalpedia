-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KleinFormTorsionUnit
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_KleinFormTorsionUnit
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:25.836973+00:00
-- url     : https://prove2.me/theorems/aa52a513-f6ab-4d0e-bf59-80c5d99fa30f
-- title:
--   Klein Form Torsion Unit
-- statement:
--   Definitions and structural lemmas for Klein Form Torsion Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/KleinFormTorsionUnit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormWeierstrassPSubEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReductionSetSubgroup
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk


set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
namespace GlobalTheory.KleinUnit
def pt (L : PeriodPair) (m : ℕ) (c d : ℤ) : ℂ := ((c : ℂ) * L.ω₁ + (d : ℂ) * L.ω₂) / (m : ℂ)
lemma pt_add (L : PeriodPair) (m : ℕ) (c d c' d' : ℤ) :
    pt L m (c + c') (d + d') = pt L m c d + pt L m c' d' := by
  simp only [pt]; push_cast; ring
lemma pt_sub (L : PeriodPair) (m : ℕ) (c d c' d' : ℤ) :
    pt L m c d - pt L m c' d' = pt L m (c - c') (d - d') := by
  simp only [pt]; push_cast; ring
lemma pt_mem_iff (L : PeriodPair) {m : ℕ} (hm : 0 < m) (c d : ℤ) :
    pt L m c d ∈ L.lattice ↔ (m : ℤ) ∣ c ∧ (m : ℤ) ∣ d := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro h
    obtain ⟨a, b, e⟩ := PeriodPair.mem_lattice.mp h
    simp only [pt] at e
    rw [eq_div_iff hm'] at e
    have e' : (((m * a - c : ℤ) : ℝ) : ℂ) * L.ω₁ + (((m * b - d : ℤ) : ℝ) : ℂ) * L.ω₂ = 0 := by
      push_cast; linear_combination e
    have := LinearIndependent.pair_iff.mp L.indep ((m * a - c : ℤ) : ℝ) ((m * b - d : ℤ) : ℝ)
      (by simpa only [Complex.real_smul] using e')
    obtain ⟨h1, h2⟩ := this
    have h1' : (m : ℤ) * a - c = 0 := by exact_mod_cast h1
    have h2' : (m : ℤ) * b - d = 0 := by exact_mod_cast h2
    exact ⟨⟨a, by linarith⟩, ⟨b, by linarith⟩⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    refine PeriodPair.mem_lattice.mpr ⟨a, b, ?_⟩
    simp only [pt]; push_cast; field_simp
def rep (L : PeriodPair) (m : ℕ) (x : ZMod m × ZMod m) : ℂ := pt L m (x.1.val : ℤ) (x.2.val : ℤ)
lemma rep_sub_pt_mem (L : PeriodPair) {m : ℕ} (hm : 0 < m) (x : ZMod m × ZMod m) (c d : ℤ)
    (h1 : x.1 = (c : ZMod m)) (h2 : x.2 = (d : ZMod m)) : rep L m x - pt L m c d ∈ L.lattice := by
  haveI : NeZero m := ⟨hm.ne'⟩
  simp only [rep, h1, h2, ZMod.val_intCast]
  rw [pt_sub, pt_mem_iff L hm]
  exact ⟨⟨-(c / m), by rw [Int.emod_def]; ring⟩, ⟨-(d / m), by rw [Int.emod_def]; ring⟩⟩
lemma rep_add (L : PeriodPair) {m : ℕ} (hm : 0 < m) (x y : ZMod m × ZMod m) :
    rep L m (x + y) - (rep L m x + rep L m y) ∈ L.lattice := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have := rep_sub_pt_mem L hm (x + y) ((x.1.val : ℤ) + (y.1.val : ℤ)) ((x.2.val : ℤ) + (y.2.val : ℤ))
    (by simp) (by simp)
  rwa [pt_add] at this
lemma rep_sub (L : PeriodPair) {m : ℕ} (hm : 0 < m) (x y : ZMod m × ZMod m) :
    rep L m (x - y) - (rep L m x - rep L m y) ∈ L.lattice := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have := rep_sub_pt_mem L hm (x - y) ((x.1.val : ℤ) - (y.1.val : ℤ)) ((x.2.val : ℤ) - (y.2.val : ℤ))
    (by simp) (by simp)
  rwa [← pt_sub] at this
lemma rep_zero (L : PeriodPair) (m : ℕ) : rep L m 0 = 0 := by
  simp [rep, pt]
def sub (L : PeriodPair) {m : ℕ} (hm : 0 < m) (G : AddSubgroup ℂ) (hG : ∀ ω ∈ L.lattice, ω ∈ G) :
    AddSubgroup (ZMod m × ZMod m) where
  carrier := {x | rep L m x ∈ G}
  zero_mem' := by
    change rep L m 0 ∈ G
    rw [rep_zero]; exact G.zero_mem
  add_mem' := fun {x y} hx hy => by
    have := G.add_mem (hG _ (rep_add L hm x y)) (G.add_mem hx hy)
    rwa [sub_add_cancel] at this
  neg_mem' := fun {x} hx => by
    change rep L m (-x) ∈ G
    have e : rep L m (-x) = rep L m (0 - x) - (rep L m 0 - rep L m x) + - rep L m x := by
      rw [rep_zero, zero_sub]; ring
    rw [e]
    exact G.add_mem (hG _ (rep_sub L hm 0 x)) (G.neg_mem hx)
end GlobalTheory.KleinUnit


