-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionPrime
-- name    : GroundTheory_LocalFields_BrauerInductionPrime
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T02:05:40.617194+00:00
-- url     : https://prove2.me/theorems/15f8ccc2-f55a-4c0d-8913-da6d2413c7b5
-- title:
--   Brauer Induction Prime
-- statement:
--   Definitions and structural lemmas for Brauer Induction Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G]
section MulSubgroup
def mulSubgroup (C P : Subgroup G) (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) : Subgroup G where
  carrier := {h | ∃ c ∈ C, ∃ y ∈ P, h = c * y}
  one_mem' := ⟨1, C.one_mem, 1, P.one_mem, (mul_one 1).symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, hc, y, hy, rfl⟩ ⟨c', hc', y', hy', rfl⟩
    refine ⟨c * c', C.mul_mem hc hc', y * y', P.mul_mem hy hy', ?_⟩
    rw [show c * y * (c' * y') = c * (y * c') * y' by group, ← hcomm c' hc' y hy]
    group
  inv_mem' := by
    rintro _ ⟨c, hc, y, hy, rfl⟩
    refine ⟨c⁻¹, C.inv_mem hc, y⁻¹, P.inv_mem hy, ?_⟩
    rw [mul_inv_rev]
    exact (hcomm c⁻¹ (C.inv_mem hc) y⁻¹ (P.inv_mem hy)).symm
theorem mem_mulSubgroup {C P : Subgroup G} {hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c} {h : G} :
    h ∈ mulSubgroup C P hcomm ↔ ∃ c ∈ C, ∃ y ∈ P, h = c * y := Iff.rfl
theorem left_le_mulSubgroup {C P : Subgroup G} (hcomm : ∀ c ∈ C, ∀ y ∈ P, c * y = y * c) :
    C ≤ mulSubgroup C P hcomm := fun c hc ↦ ⟨c, hc, 1, P.one_mem, (mul_one c).symm⟩
end MulSubgroup
variable [Fintype G] (p : ℕ) [hp : Fact p.Prime] (x : G)
def sylowCent : Subgroup G :=
  ((Classical.arbitrary (Sylow p (Subgroup.centralizer {x}))) : Subgroup (Subgroup.centralizer {x})).map
    (Subgroup.centralizer {x}).subtype
variable {p x}
omit [Fintype G] hp in
theorem commute_of_mem_sylowCent {y : G} (hy : y ∈ sylowCent p x) : y * x = x * y := by
  have : y ∈ Subgroup.centralizer {x} := Subgroup.map_subtype_le _ hy
  exact Subgroup.mem_centralizer_singleton_iff.mp this
omit [Fintype G] hp in
theorem commute_zpowers_sylowCent :
    ∀ c ∈ Subgroup.zpowers x, ∀ y ∈ sylowCent p x, c * y = y * c := by
  intro c hc y hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact ((Commute.symm (commute_of_mem_sylowCent hy)).zpow_left i).eq
variable (p x) in

def elemSub : Subgroup G := mulSubgroup (Subgroup.zpowers x) (sylowCent p x) commute_zpowers_sylowCent
omit [Fintype G] hp in
theorem mem_elemSub_self : x ∈ elemSub p x :=
  left_le_mulSubgroup _ (Subgroup.mem_zpowers x)
variable (p x) in

abbrev sylowCentIn : Subgroup (elemSub p x) := (sylowCent p x).subgroupOf (elemSub p x)
instance normal_sylowCentIn : (sylowCentIn p x).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨c, hc, y, hy, hg⟩ := mem_mulSubgroup.mp g.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
  have hw : y * n * y⁻¹ ∈ sylowCent p x :=
    (sylowCent p x).mul_mem ((sylowCent p x).mul_mem hy hn) ((sylowCent p x).inv_mem hy)
  rw [show c * y * (n : G) * (c * y)⁻¹ = c * (y * n * y⁻¹) * c⁻¹ by group,
    commute_zpowers_sylowCent c hc _ hw, mul_inv_cancel_right]
  exact hw
section Theta
variable (p x) in

def xIn : elemSub p x := ⟨x, mem_elemSub_self⟩
variable (p x) in

def theta (h : elemSub p x) : ℂ :=
  if (h : elemSub p x ⧸ sylowCentIn p x) = (xIn p x : elemSub p x ⧸ sylowCentIn p x) then
    (Nat.card (elemSub p x ⧸ sylowCentIn p x) : ℂ) else 0
end Theta
section ThetaSpan
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
end ThetaSpan
section Count
end Count
section Main
def classRep (c : ConjClasses G) : G := Classical.choose c.exists_rep
variable (p) in

def brauerFun : G → ℂ := ∑ c : ConjClasses G,
  if (orderOf (classRep c)).Coprime p then
    indFun (elemSub p (classRep c)).subtype (theta p (classRep c)) else 0
variable {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
  (hmono : ∀ K : Subgroup G, IsElementaryAt p K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
include hζ hmono
end Main
end GroundTheory.LocalField


