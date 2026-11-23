-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_WeilPolarization_WmSysObjects
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_WeilPolarization_WmSysObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:22.599494+00:00
-- url     : https://prove2.me/theorems/f537ed58-5b37-4d6d-80bb-04fdf571dcde
-- title:
--   Wm Sys Objects
-- statement:
--   Definitions and structural lemmas for Wm Sys Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/WeilPolarization/WmSysObjects.lean

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
namespace GroundTheory.Heights₂.Theta
open MeasureTheory Matrix
set_option linter.unusedSectionVars false
section Alg
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
def sympGroup (ω : LinearMap.BilinForm R W) : Subgroup (W ≃ₗ[R] W) where
  carrier := {g | ∀ w w', ω (g w) (g w') = ω w w'}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb w w' := by
    change ω (a (b w)) (a (b w')) = _
    rw [ha, hb]
  inv_mem' {a} ha w w' := by
    change ω (a.symm w) (a.symm w') = _
    conv_rhs => rw [← a.apply_symm_apply w, ← a.apply_symm_apply w']
    rw [ha]
@[ext]
structure Heis (ω : LinearMap.BilinForm R W) where

  w : W

  t : R
namespace Heis
variable {ω : LinearMap.BilinForm R W} [Invertible (2 : R)]
instance : Mul (Heis ω) := ⟨fun h h' => ⟨h.w + h'.w, h.t + h'.t + ⅟2 * ω h.w h'.w⟩⟩
instance : One (Heis ω) := ⟨⟨0, 0⟩⟩
instance : Inv (Heis ω) := ⟨fun h => ⟨-h.w, -h.t + ⅟2 * ω h.w h.w⟩⟩
@[simp] theorem mul_w (h h' : Heis ω) : (h * h').w = h.w + h'.w := rfl
@[simp] theorem product_torus_component (h h' : Heis ω) : (h * h').t = h.t + h'.t + ⅟2 * ω h.w h'.w := rfl
@[simp] theorem one_w : (1 : Heis ω).w = 0 := rfl
@[simp] theorem indicator_eq_one_of_true : (1 : Heis ω).t = 0 := rfl
@[simp] theorem inv_w (h : Heis ω) : h⁻¹.w = -h.w := rfl
@[simp] theorem exists_inverse_fontaineElement_mem_fil_neg_one (h : Heis ω) : h⁻¹.t = -h.t + ⅟2 * ω h.w h.w := rfl
instance : Group (Heis ω) where
  mul_assoc a b c := by
    ext
    · simp [add_assoc]
    · simp only [product_torus_component, mul_w, map_add, LinearMap.add_apply]
      ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv_mul_cancel a := by
    ext
    · simp
    · simp only [product_torus_component, exists_inverse_fontaineElement_mem_fil_neg_one, inv_w, indicator_eq_one_of_true, map_neg, LinearMap.neg_apply]
      ring
end Heis
def sympAct {ω : LinearMap.BilinForm R W} (g : W ≃ₗ[R] W) (h : Heis ω) : Heis ω := ⟨g h.w, h.t⟩
variable {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
structure SympPolarization (ω : LinearMap.BilinForm R W) (X Y : Type*) [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] where

  e : W ≃ₗ[R] X × Y

  isoX : ∀ x x' : X, ω (e.symm (x, 0)) (e.symm (x', 0)) = 0

  isoY : ∀ y y' : Y, ω (e.symm (0, y)) (e.symm (0, y')) = 0
namespace SympPolarization
variable {ω : LinearMap.BilinForm R W}
def pair (P : SympPolarization ω X Y) (x : X) (y : Y) : R := ω (P.e.symm (x, 0)) (P.e.symm (0, y))
def xPart (P : SympPolarization ω X Y) (w : W) : X := (P.e w).1
def yPart (P : SympPolarization ω X Y) (w : W) : Y := (P.e w).2
def schr [Invertible (2 : R)] (P : SympPolarization ω X Y) (ψ : AddChar R Circle) (h : Heis ω)
    (φ : X → ℂ) : X → ℂ :=
  fun x => (ψ (h.t + P.pair x (P.yPart h.w) + ⅟2 * P.pair (P.xPart h.w) (P.yPart h.w)) : ℂ) *
    φ (x + P.xPart h.w)
def Stab (P : SympPolarization ω X Y) (g : W ≃ₗ[R] W) : Prop :=
  (∀ x : X, (P.e (g (P.e.symm (x, 0)))).2 = 0) ∧ ∀ y : Y, (P.e (g (P.e.symm (0, y)))).1 = 0
theorem stab_mul (P : SympPolarization ω X Y) {a b : W ≃ₗ[R] W} (ha : P.Stab a)
    (hb : P.Stab b) : P.Stab (a * b) := by
  constructor
  · intro x
    have h1 : b (P.e.symm (x, 0)) = P.e.symm ((P.e (b (P.e.symm (x, 0)))).1, 0) := by
      apply P.e.injective
      rw [LinearEquiv.apply_symm_apply]
      exact Prod.ext rfl (hb.1 x)
    change (P.e (a (b (P.e.symm (x, 0))))).2 = 0
    rw [h1]
    exact ha.1 _
  · intro y
    have h1 : b (P.e.symm (0, y)) = P.e.symm (0, (P.e (b (P.e.symm (0, y)))).2) := by
      apply P.e.injective
      rw [LinearEquiv.apply_symm_apply]
      exact Prod.ext (hb.2 y) rfl
    change (P.e (a (b (P.e.symm (0, y))))).1 = 0
    rw [h1]
    exact ha.2 _
def levi (P : SympPolarization ω X Y) : Subgroup (W ≃ₗ[R] W) where
  carrier := {g | g ∈ sympGroup ω ∧ P.Stab g ∧ P.Stab g⁻¹}
  one_mem' := ⟨(sympGroup ω).one_mem, ⟨fun x => by simp, fun y => by simp⟩,
    ⟨fun x => by simp, fun y => by simp⟩⟩
  mul_mem' {a b} ha hb := ⟨(sympGroup ω).mul_mem ha.1 hb.1, P.stab_mul ha.2.1 hb.2.1, by
    rw [_root_.mul_inv_rev]
    exact P.stab_mul hb.2.2 ha.2.2⟩
  inv_mem' {a} ha := ⟨(sympGroup ω).inv_mem ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩
def leviX (P : SympPolarization ω X Y) (g : W ≃ₗ[R] W) : X →ₗ[R] X :=
  LinearMap.fst R X Y ∘ₗ P.e.toLinearMap ∘ₗ g.toLinearMap ∘ₗ P.e.symm.toLinearMap ∘ₗ
    LinearMap.inl R X Y
theorem leviX_apply (P : SympPolarization ω X Y) (g : W ≃ₗ[R] W) (x : X) :
    P.leviX g x = (P.e (g (P.e.symm (x, 0)))).1 := rfl
theorem leviX_mul (P : SympPolarization ω X Y) {a b : W ≃ₗ[R] W} (hb : P.Stab b) (x : X) :
    P.leviX (a * b) x = P.leviX a (P.leviX b x) := by
  rw [leviX_apply, leviX_apply, leviX_apply]
  have h1 : b (P.e.symm (x, 0)) = P.e.symm ((P.e (b (P.e.symm (x, 0)))).1, 0) := by
    apply P.e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext rfl (hb.1 x)
  change (P.e (a (b (P.e.symm (x, 0))))).1 = _
  conv_lhs => rw [h1]
theorem leviX_one (P : SympPolarization ω X Y) (x : X) : P.leviX 1 x = x := by
  simp [leviX_apply]
def leviXEquiv (P : SympPolarization ω X Y) (g : P.levi) : X ≃ₗ[R] X where
  toLinearMap := P.leviX g
  invFun := P.leviX (g⁻¹ : P.levi)
  left_inv x := by
    change P.leviX ((g : W ≃ₗ[R] W)⁻¹) (P.leviX g x) = x
    rw [← leviX_mul P g.2.2.1, inv_mul_cancel, leviX_one]
  right_inv x := by
    change P.leviX g (P.leviX ((g : W ≃ₗ[R] W)⁻¹) x) = x
    rw [← leviX_mul P g.2.2.2, mul_inv_cancel, leviX_one]
section Top
variable [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace X] [IsModuleTopology R X]
def leviXHomeo (P : SympPolarization ω X Y) (g : P.levi) : X ≃ₜ+ X :=
  haveI := IsModuleTopology.toContinuousAdd R X
  { toAddEquiv := (P.leviXEquiv g).toAddEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (P.leviXEquiv g).toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (P.leviXEquiv g).symm.toLinearMap }
variable [MeasurableSpace X] [BorelSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
def leviModulus (P : SympPolarization ω X Y) (g : P.levi) : NNReal :=
  addEquivAddHaarChar (P.leviXHomeo g)
def rXX (P : SympPolarization ω X Y) (g : P.levi) (φ : X → ℂ) : X → ℂ :=
  fun x => (((P.leviModulus g : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * φ (P.leviX (g⁻¹ : P.levi) x)
end Top
section L2
variable [MeasurableSpace X] [Invertible (2 : R)]
def Implements (P : SympPolarization ω X Y) (ψ : AddChar R Circle) (μ : Measure X)
    (g : W ≃ₗ[R] W) (M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ (h : Heis ω) (f f' : Lp ℂ 2 μ), (f' : X → ℂ) =ᵐ[μ] P.schr ψ h f →
    (M f' : X → ℂ) =ᵐ[μ] P.schr ψ (sympAct g h) (M f)
def IsSplitting (P : SympPolarization ω X Y) (ψ : AddChar R Circle) (μ : Measure X)
    (G : Subgroup (sympGroup ω)) (om : G →* unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)) : Prop :=
  ∀ g : G, P.Implements ψ μ ((g : sympGroup ω) : W ≃ₗ[R] W) (om g : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
end L2
end SympPolarization
def fourShuffle (P₁ P₂ Q₁ Q₂ : Type*) [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂]
    [Module R P₂] [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂] :
    ((P₁ × P₂) × (Q₁ × Q₂)) ≃ₗ[R] ((P₁ × Q₂) × (Q₁ × P₂)) where
  toFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  invFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
variable {P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]
structure FourPieces (ω : LinearMap.BilinForm R W) (P₁ P₂ Q₁ Q₂ : Type*) [AddCommGroup P₁]
    [Module R P₁] [AddCommGroup P₂] [Module R P₂] [AddCommGroup Q₁] [Module R Q₁]
    [AddCommGroup Q₂] [Module R Q₂] where

  e : W ≃ₗ[R] (P₁ × P₂) × (Q₁ × Q₂)

  a₁ : P₁ →ₗ[R] Q₁ →ₗ[R] R

  a₂ : P₂ →ₗ[R] Q₂ →ₗ[R] R

  form : ∀ w w', ω w w' = a₁ (e w).1.1 (e w').2.1 + a₂ (e w).1.2 (e w').2.2
    - a₁ (e w').1.1 (e w).2.1 - a₂ (e w').1.2 (e w).2.2
namespace FourPieces
variable {ω : LinearMap.BilinForm R W}
def pol₁ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : SympPolarization ω (P₁ × P₂) (Q₁ × Q₂) where
  e := F.e
  isoX x x' := by rw [F.form]; simp
  isoY y y' := by rw [F.form]; simp
def pol₂ (F : FourPieces ω P₁ P₂ Q₁ Q₂) : SympPolarization ω (P₁ × Q₂) (Q₁ × P₂) where
  e := F.e.trans (fourShuffle P₁ P₂ Q₁ Q₂)
  isoX x x' := by
    rw [F.form]
    simp [fourShuffle]
  isoY y y' := by
    rw [F.form]
    simp [fourShuffle]
def partialFourier (F : FourPieces ω P₁ P₂ Q₁ Q₂) [MeasurableSpace P₂] (ψ : AddChar R Circle)
    (ν : Measure P₂) (φ : P₁ × P₂ → ℂ) : P₁ × Q₂ → ℂ :=
  fun z => ∫ p, φ (z.1, p) * (ψ (F.a₂ p z.2) : ℂ) ∂ν
end FourPieces
section Std
variable (R) in

def stdForm {d : ℕ} (M : Matrix (Fin d) (Fin d) R) :
    LinearMap.BilinForm R ((Fin d → R) × (Fin d → R)) :=
  LinearMap.mk₂ R (fun u v => u.1 ⬝ᵥ (M *ᵥ v.2) - v.1 ⬝ᵥ (M *ᵥ u.2))
    (fun u u' v => by
      simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, mulVec_add, dotProduct_add]; ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, mulVec_smul, dotProduct_smul,
        smul_eq_mul]; ring)
    (fun u v v' => by
      simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, mulVec_add, dotProduct_add]; ring)
    (fun c u v => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, mulVec_smul, dotProduct_smul,
        smul_eq_mul]; ring)
theorem stdForm_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) R) (u v : (Fin d → R) × (Fin d → R)) :
    stdForm R M u v = u.1 ⬝ᵥ (M *ᵥ v.2) - v.1 ⬝ᵥ (M *ᵥ u.2) := rfl
def stdPol {d : ℕ} (M : Matrix (Fin d) (Fin d) R) :
    SympPolarization (stdForm R M) (Fin d → R) (Fin d → R) where
  e := LinearEquiv.refl R _
  isoX x x' := by simp [stdForm_apply]
  isoY y y' := by simp [stdForm_apply]
end Std
end Alg
end GroundTheory.Heights₂.Theta


