-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
-- name    : GroundTheory_AutomorphicForms_GKModules_RightRegular
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:40.157535+00:00
-- url     : https://prove2.me/theorems/f985fafa-e5be-44e8-b47a-2743a81d599d
-- title:
--   Right Regular
-- statement:
--   Definitions and structural lemmas for Right Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/RightRegular.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_Ad_expG
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
def rightTranslate {M : Type*} [Mul M] {F : Type*} (a : M) (f : M → F) (g : M) : F := f (g * a)
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
def IsSmoothFun (f : G → F) : Prop :=
  letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f
theorem isSmoothFun_iff {f : G → F} :
    h.IsSmoothFun f ↔ ∀ g : G, ContDiff ℝ ∞ (fun Y : 𝔤 => f (g * h.expG Y)) :=
  h.contMDiff_iff_expG f
theorem IsSmoothFun.contDiff_comp {f : G → F} (hf : h.IsSmoothFun f) (g₀ : G) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ φ₃ : V → 𝔤} (h₁ : ContDiff ℝ ∞ φ₁)
    (h₂ : ContDiff ℝ ∞ φ₂) (h₃ : ContDiff ℝ ∞ φ₃) :
    ContDiff ℝ ∞ (fun p => f (g₀ * h.expG (φ₁ p) * h.expG (φ₂ p) * h.expG (φ₃ p))) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞
      (fun p => g₀ * h.expG (φ₁ p) * h.expG (φ₂ p) * h.expG (φ₃ p)) :=
    ((contMDiff_const.mul (h.contMDiff_expG_comp h₁)).mul (h.contMDiff_expG_comp h₂)).mul
      (h.contMDiff_expG_comp h₃)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff
noncomputable def rightDeriv (X : 𝔤) (f : G → F) (g : G) : F :=
  fderiv ℝ (fun Y : 𝔤 => f (g * h.expG Y)) 0 X
theorem differentiable_comp_expG {f : G → F} (hf : h.IsSmoothFun f) (g : G) :
    Differentiable ℝ (fun Y : 𝔤 => f (g * h.expG Y)) :=
  ((h.isSmoothFun_iff).1 hf g).differentiable (by simp)
theorem hasDerivAt_rightDeriv {f : G → F} (hf : h.IsSmoothFun f) (X : 𝔤) (g : G) :
    HasDerivAt (fun t : ℝ => f (g * h.expG (t • X))) (h.rightDeriv X f g) 0 := by
  have h1 := hasDerivAt_comp_line (h.differentiable_comp_expG hf g 0) X
  simp only [zero_add] at h1
  exact h1
theorem isSmoothFun_rightTranslate {f : G → F} (hf : h.IsSmoothFun f) (a : G) :
    h.IsSmoothFun (rightTranslate a f) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf (contMDiff_id.mul contMDiff_const)
theorem isSmoothFun_rightDeriv {f : G → F} (hf : h.IsSmoothFun f) (X : 𝔤) :
    h.IsSmoothFun (h.rightDeriv X f) := by
  rw [isSmoothFun_iff]
  intro g₀
  have hΨ : ContDiff ℝ ∞ (Function.uncurry fun Z Y : 𝔤 => f (g₀ * h.expG Z * h.expG Y)) := by
    have := hf.contDiff_comp h g₀ (φ₁ := fun p : 𝔤 × 𝔤 => p.1) (φ₂ := fun p => p.2)
      (φ₃ := fun _ => 0) contDiff_fst contDiff_snd contDiff_const
    convert this using 2 with p
    simp [Function.uncurry]
  have hd : ContDiff ℝ ∞ (fun Z : 𝔤 => fderiv ℝ (fun Y : 𝔤 => f (g₀ * h.expG Z * h.expG Y)) 0) :=
    ContDiff.fderiv hΨ contDiff_const (by simp)
  exact hd.clm_apply contDiff_const
theorem rightDeriv_add_left (X Y : 𝔤) (f : G → F) :
    h.rightDeriv (X + Y) f = h.rightDeriv X f + h.rightDeriv Y f := by
  funext g; simp [rightDeriv]
theorem rightDeriv_smul_left (r : ℝ) (X : 𝔤) (f : G → F) :
    h.rightDeriv (r • X) f = r • h.rightDeriv X f := by
  funext g; simp [rightDeriv]
theorem rightDeriv_neg_left (X : 𝔤) (f : G → F) : h.rightDeriv (-X) f = -h.rightDeriv X f := by
  funext g; simp [rightDeriv]
theorem rightDeriv_add {f₁ f₂ : G → F} (hf₁ : h.IsSmoothFun f₁) (hf₂ : h.IsSmoothFun f₂)
    (X : 𝔤) : h.rightDeriv X (f₁ + f₂) = h.rightDeriv X f₁ + h.rightDeriv X f₂ := by
  funext g
  simp only [rightDeriv, Pi.add_apply]
  rw [fderiv_fun_add (h.differentiable_comp_expG hf₁ g 0) (h.differentiable_comp_expG hf₂ g 0)]
  rfl
theorem rightDeriv_smul {f : G → F} (hf : h.IsSmoothFun f) (c : ℂ) (X : 𝔤) :
    h.rightDeriv X (c • f) = c • h.rightDeriv X f := by
  funext g
  simp only [rightDeriv, Pi.smul_apply]
  rw [fderiv_fun_const_smul (h.differentiable_comp_expG hf g 0) c]
  rfl
theorem rightDeriv_bracket {f : G → F} (hf : h.IsSmoothFun f) (X Y : 𝔤) :
    h.rightDeriv (h.bracket X Y) f =
      h.rightDeriv X (h.rightDeriv Y f) - h.rightDeriv Y (h.rightDeriv X f) := by
  funext g
  set A : ℝ × ℝ × ℝ → F :=
    fun p => f (g * h.expG (p.1 • X) * h.expG (p.2.1 • Y) * h.expG (p.2.2 • (-X))) with hAdef
  have hA : ContDiff ℝ ∞ A := hf.contDiff_comp h g
    (contDiff_fst.smul contDiff_const) ((contDiff_fst.comp contDiff_snd).smul contDiff_const)
    ((contDiff_snd.comp contDiff_snd).smul contDiff_const)
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  set D2 := fderiv ℝ (fderiv ℝ A) 0
  set er : ℝ × ℝ × ℝ := (1, 0, 0)
  set et : ℝ × ℝ × ℝ := (0, 1, 0)
  set eu : ℝ × ℝ × ℝ := (0, 0, 1)
  have hY := h.isSmoothFun_rightDeriv hf Y
  have hX := h.isSmoothFun_rightDeriv hf X
  have da : ∀ r : ℝ, fderiv ℝ A (r • er) et = h.rightDeriv Y f (g * h.expG (r • X)) := by
    intro r
    have h1 := hasDerivAt_comp_line (hAd (r • er)) et
    have h2 := h.hasDerivAt_rightDeriv hf Y (g * h.expG (r • X))
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp [A, er, et]
  have dc : ∀ t : ℝ, fderiv ℝ A (t • et) eu = -h.rightDeriv X f (g * h.expG (t • Y)) := by
    intro t
    have h1 := hasDerivAt_comp_line (hAd (t • et)) eu
    have h2 := h.hasDerivAt_rightDeriv hf (-X) (g * h.expG (t • Y))
    rw [rightDeriv_neg_left] at h2
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp [A, et, eu]
  have db : D2 er et = h.rightDeriv X (h.rightDeriv Y f) g := by
    have h1 := hasDerivAt_fderiv_line hA 0 er et
    have h2 := h.hasDerivAt_rightDeriv hY X g
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp only [zero_add]
    rw [da]
  have dd : D2 et eu = -h.rightDeriv Y (h.rightDeriv X f) g := by
    have h1 := hasDerivAt_fderiv_line hA 0 et eu
    have h2 := (h.hasDerivAt_rightDeriv hX Y g).neg
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp only [zero_add]
    rw [dc]
    rfl
  have hsymm : D2 eu et = D2 et eu :=
    (hA.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) eu et
  have diag : ∀ s : ℝ, fderiv ℝ A (s • (er + eu)) et =
      fderiv ℝ (fun Z : 𝔤 => f (g * h.expG Z)) 0 (h.Ad (h.expG (s • X)) Y) := by
    intro s
    have h1 := hasDerivAt_comp_line (hAd (s • (er + eu))) et
    have h2 := h.hasDerivAt_rightDeriv hf (h.Ad (h.expG (s • X)) Y) g
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
    simp only [A, er, eu, et, Prod.smul_mk, Prod.mk_add_mk, smul_zero, smul_eq_mul, mul_one,
      mul_zero, add_zero, zero_add]
    rw [← map_smul, expG_Ad, smul_neg, expG_neg]
    simp only [mul_assoc]
  have hg := hasDerivAt_fderiv_line hA 0 (er + eu) et
  have hg' := (fderiv ℝ (fun Z : 𝔤 => f (g * h.expG Z)) 0).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (h.hasDerivAt_Ad_expG X Y)
  have e := hg.unique (hg'.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
  · change D2 (er + eu) et = h.rightDeriv (h.bracket X Y) f g at e
    rw [Pi.sub_apply, ← e, map_add, ContinuousLinearMap.add_apply, db, hsymm, dd, sub_eq_add_neg]
  · simp only [zero_add, Function.comp_apply]
    rw [diag]
def smoothFuns : Submodule ℂ (G → F) where
  carrier := {f | h.IsSmoothFun f}
  zero_mem' := by
    show h.IsSmoothFun (0 : G → F)
    letI := h.chartedSpace
    exact contMDiff_const
  add_mem' {f₁ f₂} hf₁ hf₂ := by
    change h.IsSmoothFun f₁ at hf₁
    change h.IsSmoothFun f₂ at hf₂
    show h.IsSmoothFun (f₁ + f₂)
    letI := h.chartedSpace
    exact hf₁.add hf₂
  smul_mem' c f hf := by
    change h.IsSmoothFun f at hf
    show h.IsSmoothFun (c • f)
    letI := h.chartedSpace
    have e : c • f = ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ) ∘ f := by
      funext g; simp
    rw [e]
    exact ((c • ContinuousLinearMap.id ℂ F).restrictScalars ℝ).contDiff.comp_contMDiff hf
noncomputable def rightDerivEnd (X : 𝔤) : Module.End ℂ (h.smoothFuns (F := F)) where
  toFun f := ⟨h.rightDeriv X f, h.isSmoothFun_rightDeriv f.2 X⟩
  map_add' f₁ f₂ := by ext1; exact h.rightDeriv_add f₁.2 f₂.2 X
  map_smul' c f := by ext1; exact h.rightDeriv_smul f.2 c X
def rightTranslateEnd (a : G) : Module.End ℂ (h.smoothFuns (F := F)) where
  toFun f := ⟨rightTranslate a f, h.isSmoothFun_rightTranslate f.2 a⟩
  map_add' f₁ f₂ := rfl
  map_smul' c f := rfl
attribute [local instance 100] LieRing.ofAssociativeRing
noncomputable def rightDerivLie : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (h.smoothFuns (F := F)) where
  toFun X := h.rightDerivEnd (h.ofLie X)
  map_add' X Y := by ext1 f; ext1; exact h.rightDeriv_add_left _ _ _
  map_smul' r X := by ext1 f; ext1; exact h.rightDeriv_smul_left r _ _
  map_lie' {X Y} := by
    ext1 f; ext1
    rw [h.ofLie_lie, Ring.lie_def]
    exact h.rightDeriv_bracket f.2 _ _
noncomputable def rightUAction :
    UniversalEnvelopingAlgebra ℝ h.lieSubalgebra →ₐ[ℝ] Module.End ℂ (h.smoothFuns (F := F)) :=
  UniversalEnvelopingAlgebra.lift ℝ h.rightDerivLie
def centerU : Subalgebra ℝ (UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :=
  Subalgebra.center ℝ _
def IsZFinite (f : h.smoothFuns (F := F)) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ ((fun z => h.rightUAction z f) '' (h.centerU : Set _)))
def IsRightKFinite (K : Subgroup G) (f : G → F) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => rightTranslate (k : G) f))
end IsExpLieAlgebra
end GroundTheory.Automorphic


