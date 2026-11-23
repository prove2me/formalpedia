-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:27.053524+00:00
-- url     : https://prove2.me/theorems/f43022a5-9949-4555-afea-097aac2ebaed
-- title:
--   Is Locally Constant Orbit
-- statement:
--   Definitions and structural lemmas for Is Locally Constant Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
namespace GlobalTheory.IwahoriInj
section Abstract
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (π) in

def Inj (I J : Subgroup G) : Prop := ∀ v ∈ fixed π I, v ∈ twKer π J 1 → v = 0
end Abstract
section Depth
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def Deep (a : ℤ) (x : k) : Prop := valuation k x ≤ uniformizer k ^ a
theorem unif_pos : 0 < uniformizer k := uniformizer_pos
theorem deep_zero (a : ℤ) : Deep a (0 : k) := by simp [Deep]
theorem deep_zero_iff {x : k} : Deep 0 x ↔ valuation k x ≤ 1 := by simp [Deep]
theorem Deep.mono {a b : ℤ} {x : k} (h : Deep a x) (hab : b ≤ a) : Deep b x :=
  le_trans h (zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le hab)
theorem Deep.mul {a b : ℤ} {x y : k} (hx : Deep a x) (hy : Deep b y) : Deep (a + b) (x * y) := by
  unfold Deep at *
  rw [map_mul, zpow_add₀ unif_pos.ne']
  exact mul_le_mul' hx hy
theorem Deep.sum {ι : Type} {s : Finset ι} {a : ℤ} {x : ι → k} (h : ∀ i ∈ s, Deep a (x i)) :
    Deep a (∑ i ∈ s, x i) := Valuation.map_sum_le _ h
end Depth
section Chambers
variable {n : Type}
def Conc (f : n → n → ℤ) : Prop := (∀ i, f i i = 0) ∧ ∀ i j l, f i j ≤ f i l + f l j
def Chamber (f : n → n → ℤ) : Prop := Conc f ∧ ∀ i j, i ≠ j → f i j + f j i = 1
end Chambers
section Groups
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
variable (k) in

def grp {f : n → n → ℤ} (hf : Conc f) : Subgroup (GL n k) where
  carrier := {g | (∀ i j, Deep (f i j) (g.val i j)) ∧ ∀ i j, Deep (f i j) ((g⁻¹).val i j)}
  one_mem' := by
    have : ∀ i j, Deep (f i j) ((1 : Matrix n n k) i j) := fun i j => by
      by_cases h : i = j
      · subst h; simp [hf.1, deep_zero_iff]
      · simp [one_apply_ne h, deep_zero]
    exact ⟨this, this⟩
  mul_mem' := by
    have : ∀ A B : Matrix n n k, (∀ i j, Deep (f i j) (A i j)) → (∀ i j, Deep (f i j) (B i j)) →
        ∀ i j, Deep (f i j) ((A * B) i j) := fun A B hA hB i j => by
      rw [mul_apply]
      exact Deep.sum fun l _ => ((hA i l).mul (hB l j)).mono (hf.2 i j l)
    intro a b ha hb
    refine ⟨this _ _ ha.1 hb.1, ?_⟩
    rw [_root_.mul_inv_rev]
    exact this _ _ hb.2 ha.2
  inv_mem' := fun h => ⟨h.2, by simpa using h.1⟩
def elem {i j : n} (h : i ≠ j) (y : k) : GL n k :=
  ⟨transvection i j y, transvection i j (-y), by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩
variable {g f f' : n → n → ℤ} {i j : n}
variable {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL n k) V}
variable [LinearOrder n]
def ray (m : ℕ) (i j : n) : ℤ :=
  (if j < i then 1 else 0) + m * (((Finset.univ.filter (· < i)).card : ℤ) - (Finset.univ.filter (· < j)).card)
theorem chamber_ray (m : ℕ) : Chamber (ray (n := n) m) := by
  refine ⟨⟨fun i => by simp [ray], fun i j l => ?_⟩, fun i j h => ?_⟩
  · have : (if j < i then 1 else 0 : ℤ) ≤ (if l < i then 1 else 0) + if j < l then 1 else 0 := by
      split_ifs <;> first | omega | (exfalso; order)
    simp only [ray]
    linarith
  · have : (if j < i then 1 else 0 : ℤ) + (if i < j then 1 else 0) = 1 := by
      split_ifs <;> first | omega | (exfalso; order)
    simp only [ray]
    linarith
end Groups
end GlobalTheory.IwahoriInj


