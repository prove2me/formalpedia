-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_HeckeKerZero
-- name    : Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_HeckeKerZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:26.074876+00:00
-- url     : https://prove2.me/theorems/7d63fb88-7829-4b86-afea-40eab757ec0b
-- title:
--   Hecke Ker Zero
-- statement:
--   Definitions and structural lemmas for Hecke Ker Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/HeckeKerZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoHeckeQuotient
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_LiftsToDetOne_one
import Theorems.Thm_GlobalTheory_LiftsToSymplectic_mul
import Theorems.Thm_GlobalTheory_coe_symplecticGroupMap
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_symplecticGroupMap
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HeckeKerModel
open GlobalTheory.HeckeTate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}
theorem comp_act_natCast (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  induction n with
  | zero =>
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h1 : t.act.act 0 = 1 := by simpa using h
    simp [h1]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]
theorem mem_tors_span (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ∈ t.tors T (Ideal.span {(n : 𝓞 E)}) ↔ x ^ n = 1 := by
  constructor
  · intro h
    rw [← comp_act_natCast]
    exact h _ (Ideal.mem_span_singleton_self _)
  · intro h a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    have := t.act.hom c
    rw [t.act.mul, ← Category.assoc, comp_act_natCast, h]
    simp
noncomputable def torsSub (t : SAB H S) (T : Over S) (n : ℕ) : Subgroup (T ⟶ t.G) :=
  { carrier := t.tors T (Ideal.span {(n : 𝓞 E)})
    one_mem' := (mem_tors_span t 1 n).2 (one_pow _)
    mul_mem' := fun {x y} hx hy a ha => by
      have := t.act.hom a
      rw [MonObj.mul_comp, hx a ha, hy a ha, _root_.one_mul]
    inv_mem' := fun {x} hx => (mem_tors_span t _ n).2 (by rw [inv_pow, (mem_tors_span t x n).1 hx, inv_one]) }
end GlobalTheory.HeckeKerModel


