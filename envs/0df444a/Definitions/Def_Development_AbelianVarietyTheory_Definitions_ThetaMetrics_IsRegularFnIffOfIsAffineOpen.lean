-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:12.862417+00:00
-- url     : https://prove2.me/theorems/10b83078-15a4-414b-8ff9-0a1acd42d183
-- title:
--   Is Regular Fn Iff Of Is Affine Open
-- statement:
--   Definitions and structural lemmas for Is Regular Fn Iff Of Is Affine Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
theorem resG_resG {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl
theorem germ_resG {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (a : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom (resG X h a) = (X.presheaf.germ U x (h hx)).hom a :=
  X.presheaf.germ_res_apply (homOfLE h) x hx a
theorem app_resG (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (φ.app V).hom (resG X h a) = resG Y (φ.preimage_mono h) ((φ.app U).hom a) := by
  change ((X.presheaf.map (homOfLE h).op ≫ φ.app V).hom) a = _
  rw [Scheme.Hom.naturality]
  rfl
def IsRegularFn {U : X.Opens} (a : Γ(X, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), resG X h a ∈ nonZeroDivisors Γ(X, V)
namespace IsRegularFn
variable {U : X.Opens} {a b : Γ(X, U)}
theorem resG (ha : IsRegularFn a) {V : X.Opens} (h : V ≤ U) : IsRegularFn (resG X h a) :=
  fun W hW => by rw [resG_resG]; exact ha W _
end IsRegularFn
theorem sec_compat {L : LB X} (s : L.Sec) (i j : L.ι) {W : X.Opens} (hi : W ≤ L.U i)
    (hj : W ≤ L.U j) :
    resG X hi (s.f i) = resG X (le_inf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X hj (s.f j) := by
  have := congrArg (resG X (le_inf hi hj)) (s.compat i j)
  rwa [map_mul, resG_resG, resG_resG] at this
def IsRegularSec {L : LB X} (s : L.Sec) : Prop := ∀ i, IsRegularFn (s.f i)
def SecMaps {A B : LB X} (w : LB.Iso A B) (a : A.Sec) (b : B.Sec) : Prop :=
  ∀ p : B.ι × A.ι, resG X (inf_le_left : B.U p.1 ⊓ A.U p.2 ≤ B.U p.1) (b.f p.1) =
    (@id (Γ(X, B.U p.1 ⊓ A.U p.2)ˣ) (w.s p) : Γ(X, B.U p.1 ⊓ A.U p.2)) *
      resG X (inf_le_right : B.U p.1 ⊓ A.U p.2 ≤ A.U p.2) (a.f p.2)
theorem pull_U (L : LB X) (φ : Y ⟶ X) (j : PUnit → L.ι) : (L.pull φ).U j = φ ⁻¹ᵁ L.U (j ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ => φ) j ⟨⟩) fun _ hy => Set.mem_iInter.2 fun _ => hy
theorem pull_g (L : LB X) (φ : Y ⟶ X) (j j' : PUnit → L.ι) :
    (L.pull φ).g j j' = res (LB.wchart_inter_le L (fun _ => φ) j j' ⟨⟩)
      (pullU φ _ (L.g (j ⟨⟩) (j' ⟨⟩))) := by
  change LB.lcg L (fun _ : PUnit => φ) (fun _ => 1) j j' = _
  rw [LB.lcg, Fintype.prod_unique, zpow_one]
def secPull {L : LB X} (s : L.Sec) (φ : Y ⟶ X) : (L.pull φ).Sec where
  f j := resG Y (pull_U L φ j).le ((φ.app _).hom (s.f (j ⟨⟩)))
  compat j j' := by
    have e := congrArg (fun a => resG Y (LB.wchart_inter_le L (fun _ => φ) j j' ⟨⟩)
      ((φ.app _).hom a)) (s.compat (j ⟨⟩) (j' ⟨⟩))
    simp only [map_mul] at e
    rw [app_resG, app_resG, resG_resG, resG_resG] at e
    refine (resG_resG _ _ _).trans (e.trans ?_)
    exact congrArg₂ (· * ·) (congrArg Units.val (pull_g L φ j j')).symm (resG_resG _ _ _).symm
theorem lbPow_U (L : LB X) (n : ℕ) (j : PUnit → L.ι) : (lbPow L n).U j = L.U (j ⟨⟩) :=
  le_antisymm (LB.wchart_le L (fun _ => 𝟙 X) j ⟨⟩) fun _ hy => Set.mem_iInter.2 fun _ => hy
theorem lbPow_g (L : LB X) (n : ℕ) (j j' : PUnit → L.ι) :
    (lbPow L n).g j j' = res (inf_le_inf (lbPow_U L n j).le (lbPow_U L n j').le)
      (L.g (j ⟨⟩) (j' ⟨⟩)) ^ n := by
  change LB.lcg L (fun _ : PUnit => 𝟙 X) (fun _ => (n : ℤ)) j j' = _
  rw [LB.lcg, Fintype.prod_unique, zpow_natCast]
  rfl
def secPow {L : LB X} (s : L.Sec) (n : ℕ) : (lbPow L n).Sec where
  f j := resG X (lbPow_U L n j).le (s.f (j ⟨⟩)) ^ n
  compat j j' := by
    have e := sec_compat s (j ⟨⟩) (j' ⟨⟩) (inf_le_left.trans (lbPow_U L n j).le)
      (inf_le_right.trans (lbPow_U L n j').le)
    change resG X _ _ = _ * resG X _ _
    rw [map_pow, map_pow, resG_resG, resG_resG, e, mul_pow]
    exact congrArg (· * _) ((congrArg Units.val (lbPow_g L n j j')).trans
      (Units.val_pow_eq_pow_val _ _)).symm
section Rational
variable [IsIntegral X]
theorem genericPoint_mem (W : X.Opens) [h : Nonempty W] : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)
theorem germK_resG {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (a : Γ(X, U)) :
    (X.germToFunctionField V).hom (resG X h a) = (X.germToFunctionField U).hom a :=
  germ_resG h _ _ a
def ratSecs {L : LB X} (s : L.Sec) (V : X.Opens) [Nonempty V] :
    Submodule Γ(X, V) X.functionField where
  carrier := {h | ∀ (i : L.ι) [Nonempty (V ⊓ L.U i : X.Opens)], ∃ a : Γ(X, V ⊓ L.U i),
    (X.germToFunctionField _).hom a =
      (X.germToFunctionField (V ⊓ L.U i)).hom (resG X inf_le_right (s.f i)) * h}
  add_mem' := fun {h h'} hh hh' i _ => by
    obtain ⟨a, ha⟩ := hh i
    obtain ⟨a', ha'⟩ := hh' i
    exact ⟨a + a', by rw [map_add, ha, ha', mul_add]⟩
  zero_mem' := fun i _ => ⟨0, by rw [map_zero, mul_zero]⟩
  smul_mem' := fun c h hh i _ => by
    obtain ⟨a, ha⟩ := hh i
    refine ⟨resG X inf_le_left c * a, ?_⟩
    rw [map_mul, ha, germK_resG, Algebra.smul_def, mul_left_comm]
    rfl
def genericChart {L : LB X} (hL : L.IsLB) : L.ι := (LB.mem_of_cover hL (genericPoint X)).choose
theorem mem_genericChart {L : LB X} (hL : L.IsLB) : genericPoint X ∈ L.U (genericChart hL) :=
  (LB.mem_of_cover hL (genericPoint X)).choose_spec
def ratOf {L : LB X} (hL : L.IsLB) (s : L.Sec) (V : X.Opens) [Nonempty V] :
    (∀ i, Γ(X, V ⊓ L.U i)) →+ X.functionField where
  toFun t := (X.presheaf.germ (V ⊓ L.U (genericChart hL)) (genericPoint X)
      ⟨genericPoint_mem V, mem_genericChart hL⟩).hom (t _) *
    (@id X.functionField
      ((X.presheaf.germ _ (genericPoint X) (mem_genericChart hL)).hom (s.f _)))⁻¹
  map_zero' := by rw [Pi.zero_apply, map_zero, zero_mul]
  map_add' t t' := by rw [Pi.add_apply, map_add, add_mul]
end Rational
end GlobalTheory.Cartier


