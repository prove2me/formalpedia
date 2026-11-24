-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:10.835224+00:00
-- url     : https://prove2.me/theorems/f786b4b4-159d-4836-9329-68dfdf8c5d19
-- title:
--   Fub Gen
-- statement:
--   Definitions and structural lemmas for Fub Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ConeShifts/FubGen.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
open scoped NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
structure Split (S A B : Subgroup G) (p q : G →* G) : Prop where
  cp : Continuous p
  cq : Continuous q
  cA : IsClosed (A : Set G)
  cB : IsClosed (B : Set G)
  cS : IsClosed (S : Set G)
  mA : ∀ g ∈ S, p g ∈ A
  mB : ∀ g ∈ S, q g ∈ B
  mul : ∀ g ∈ S, p g * q g = g
  hA : ∀ a ∈ A, a ∈ S ∧ p a = a ∧ q a = 1
  hB : ∀ b ∈ B, b ∈ S ∧ q b = b ∧ p b = 1
instance scSub (S : Subgroup G) : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
variable {S A B : Subgroup G} {p q : G →* G}
def Split.e (h : Split S A B p q) : S ≃ₜ* A × B where
  toFun g := (⟨p g, h.mA _ g.2⟩, ⟨q g, h.mB _ g.2⟩)
  invFun x := ⟨x.1 * x.2, S.mul_mem (h.hA _ x.1.2).1 (h.hB _ x.2.2).1⟩
  left_inv g := Subtype.ext (h.mul _ g.2)
  right_inv x := Prod.ext (Subtype.ext (by simp [(h.hA _ x.1.2).2.1, (h.hB _ x.2.2).2.2]))
    (Subtype.ext (by simp [(h.hA _ x.1.2).2.2, (h.hB _ x.2.2).2.1]))
  map_mul' a b := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
  continuous_toFun := ((h.cp.comp continuous_subtype_val).subtype_mk _).prodMk ((h.cq.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).subtype_mk _
variable {R : Type} [CommRing R]
structure Sys (P : R → G →* G) (K : Subgroup G) (U : Set G) (good : R → Prop) : Prop where
  cont : ∀ a, good a → Continuous (P a)
  comp : ∀ a b, good a → good b → ∀ g, P a (P b g) = P (a * b) g
  zero : ∀ g, P 0 g = 1
  add : ∀ a b, good a → good b → a * b = 0 → good (a + b) ∧ ∀ g, P (a + b) g = P a g * P b g
  idem : ∀ a, good a → a * a = a
  cK : IsClosed (K : Set G)
  mK : ∀ a, good a → ∀ g ∈ K, P a g ∈ K
  mU : MeasurableSet U
  one : (1 : G) ∈ U
  mul : ∀ g ∈ U, ∀ g' ∈ U, g * g' ∈ U
  pU : ∀ a, good a → ∀ g ∈ U, P a g ∈ U
def part (P : R → G →* G) (K : Subgroup G) (a : R) : Subgroup G := K ⊓ (P a).eqLocus (MonoidHom.id G)
variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}
def CO (P : R → G →* G) (K : Subgroup G) (U : Set G) (a : R) : Prop :=
  IsCompact {x : part P K a | x.1 ∈ U} ∧ IsOpen {x : part P K a | x.1 ∈ U}
def unitP {A : Type} [Ring A] [Algebra R A] (a : R) : Aˣ →* Aˣ := by
  classical
  exact if h : a * a = a then Units.map
    { toFun := fun x : A => a • x + (1 - a) • (1 : A)
      map_one' := by rw [← add_smul]; simp
      map_mul' := fun x y => by
        have h1 : a * (1 - a) = 0 := by rw [mul_sub, h]; simp
        have h2 : (1 - a) * a = 0 := by rw [mul_comm, h1]
        have h3 : (1 - a) * (1 - a) = 1 - a := by rw [mul_sub, h2]; simp
        simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, zero_smul, mul_one, add_zero, zero_add] } else 1
end PositivityTheory.ThKG.Fub
end


