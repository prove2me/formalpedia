-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
-- name    : GroundTheory_AutomorphicForms_GKModules_SmoothVectors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:45.556858+00:00
-- url     : https://prove2.me/theorems/511aa3e5-da49-444f-a1bc-bae87ca5124e
-- title:
--   Smooth Vectors
-- statement:
--   Definitions and structural lemmas for Smooth Vectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_Ad_expG
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
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
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
structure BanachRep (G : Type*) [Group G] [TopologicalSpace G] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] where

  toHom : G →* (E →L[ℂ] E)

  continuous_orbit' : ∀ v : E, Continuous fun g => toHom g v
namespace BanachRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
noncomputable instance : CoeFun (BanachRep G E) (fun _ => G → E →L[ℂ] E) := ⟨fun π => π.toHom⟩
variable (π : BanachRep G E)
@[simp] theorem map_one : π 1 = 1 := π.toHom.map_one
theorem map_mul (g g' : G) : π (g * g') = π g * π g' := π.toHom.map_mul g g'
theorem map_mul_apply (g g' : G) (v : E) : π (g * g') v = π g (π g' v) := by
  rw [map_mul]; rfl
@[simp] theorem map_one_apply (v : E) : π 1 v = v := by rw [map_one]; rfl
@[simp] theorem map_inv_apply_map (g : G) (v : E) : π g⁻¹ (π g v) = v := by
  rw [← map_mul_apply, inv_mul_cancel, map_one_apply]
@[simp] theorem map_apply_map_inv (g : G) (v : E) : π g (π g⁻¹ v) = v := by
  rw [← map_mul_apply, mul_inv_cancel, map_one_apply]
noncomputable def ofUnitary {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : UnitaryRep G H) : BanachRep G H where
  toHom := (unitary (H →L[ℂ] H)).subtype.comp σ.toHom
  continuous_orbit' v := σ.continuous_orbit' v
@[simp] theorem ofUnitary_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : UnitaryRep G H) (g : G) : ofUnitary σ g = σ g := rfl
end BanachRep
section Line
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem hasDerivAt_comp_line {f : V → F} {x : V} (hf : DifferentiableAt ℝ f x) (a : V) :
    HasDerivAt (fun s : ℝ => f (x + s • a)) (fderiv ℝ f x a) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • a) := by simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hl
theorem hasDerivAt_fderiv_line {f : V → F} (hf : ContDiff ℝ ∞ f) (x a b : V) :
    HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • a) b) (fderiv ℝ (fderiv ℝ f) x a b) 0 := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 := hasDerivAt_comp_line ((h1.differentiable (by simp)) x) a
  exact (ContinuousLinearMap.apply ℝ F b).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
end Line
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
@[simp] theorem expG_zero : h.expG 0 = 1 := by
  apply Subtype.ext; apply Units.ext; simp
theorem expG_neg (X : 𝔤) : h.expG (-X) = (h.expG X)⁻¹ := by
  apply Subtype.ext; apply Units.ext
  show exp (-(X : 𝔸)) = ↑((expUnit ℝ 𝔸 (X : 𝔸))⁻¹)
  rw [coe_expUnit_inv]
theorem contMDiff_expG : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ h.expG := by
  letI := h.chartedSpace
  intro X
  exact h.contMDiffAt_of_val (f := h.expG)
    (((contDiff_exp ℝ 𝔸).comp 𝔤.subtypeL.contDiff).contMDiff X)
theorem contMDiff_expG_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : V → 𝔤}
    (hφ : ContDiff ℝ ∞ φ) : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞ (fun p => h.expG (φ p)) := by
  letI := h.chartedSpace
  exact h.contMDiff_expG.comp hφ.contMDiff
theorem contMDiff_iff_expG {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : G → F) :
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, F) ∞ f) ↔
      ∀ g : G, ContDiff ℝ ∞ (fun Y : 𝔤 => f (g * h.expG Y)) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  constructor
  · intro hf g
    have : ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ (fun Y : 𝔤 => g * h.expG Y) :=
      contMDiff_const.mul h.contMDiff_expG
    exact (hf.comp this).contDiff
  · intro hf x
    rw [contMDiffAt_iff_source]
    have : f ∘ (extChartAt 𝓘(ℝ, 𝔤) x).symm = fun Y : 𝔤 => f (x * h.expG Y) := rfl
    rw [this]
    exact (hf x).contMDiff.contMDiffAt.contMDiffWithinAt
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
def IsSmoothVector (v : E) : Prop :=
  letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, E) ∞ (fun g : G => π g v)
noncomputable def expOrbit (v : E) (Y : 𝔤) : E := π (h.expG Y) v
theorem isSmoothVector_iff {v : E} : h.IsSmoothVector π v ↔ ContDiff ℝ ∞ (h.expOrbit π v) := by
  unfold IsSmoothVector
  rw [h.contMDiff_iff_expG]
  constructor
  · intro hv
    have h1 := hv 1
    simp only [one_mul] at h1
    exact h1
  · intro hv g
    have : (fun Y : 𝔤 => π (g * h.expG Y) v) = ((π g).restrictScalars ℝ) ∘ h.expOrbit π v := by
      funext Y; simp [expOrbit, BanachRep.map_mul_apply]
    rw [this]
    exact ((π g).restrictScalars ℝ).contDiff.comp hv
theorem expOrbit_add (v w : E) : h.expOrbit π (v + w) = h.expOrbit π v + h.expOrbit π w := by
  funext Y; simp [expOrbit]
theorem expOrbit_smul (c : ℂ) (v : E) : h.expOrbit π (c • v) = c • h.expOrbit π v := by
  funext Y; simp [expOrbit]
def smoothVectors : Submodule ℂ E where
  carrier := {v | h.IsSmoothVector π v}
  zero_mem' := by
    show h.IsSmoothVector π 0
    rw [isSmoothVector_iff]
    have : h.expOrbit π 0 = fun _ => 0 := by funext Y; simp [expOrbit]
    rw [this]; exact contDiff_const
  add_mem' {v w} hv hw := by
    change h.IsSmoothVector π v at hv
    change h.IsSmoothVector π w at hw
    show h.IsSmoothVector π (v + w)
    rw [isSmoothVector_iff] at hv hw ⊢
    rw [expOrbit_add]; exact hv.add hw
  smul_mem' c v hv := by
    change h.IsSmoothVector π v at hv
    show h.IsSmoothVector π (c • v)
    rw [isSmoothVector_iff] at hv ⊢
    rw [expOrbit_smul]; exact hv.const_smul c
theorem expOrbit_map (g : G) (v : E) :
    h.expOrbit π (π g v) = fun Y => π g (h.expOrbit π v (h.Ad g⁻¹ Y)) := by
  funext Y
  simp only [expOrbit, ← BanachRep.map_mul_apply, expG_Ad, inv_inv]
  congr 1
  group
theorem isSmoothVector_map {v : E} (hv : h.IsSmoothVector π v) (g : G) :
    h.IsSmoothVector π (π g v) := by
  rw [isSmoothVector_iff] at hv ⊢
  rw [expOrbit_map]
  exact ((π g).restrictScalars ℝ).contDiff.comp (hv.comp (h.AdL g⁻¹).contDiff)
noncomputable def derivOp (X : 𝔤) (v : E) : E := fderiv ℝ (h.expOrbit π v) 0 X
theorem differentiable_expOrbit {v : E} (hv : h.IsSmoothVector π v) :
    Differentiable ℝ (h.expOrbit π v) :=
  ((h.isSmoothVector_iff π).1 hv).differentiable (by simp)
theorem hasDerivAt_derivOp {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    HasDerivAt (fun t : ℝ => π (h.expG (t • X)) v) (h.derivOp π X v) 0 := by
  have h1 := hasDerivAt_comp_line (h.differentiable_expOrbit π hv 0) X
  simp only [zero_add] at h1
  exact h1
theorem derivOp_add_left (X Y : 𝔤) (v : E) :
    h.derivOp π (X + Y) v = h.derivOp π X v + h.derivOp π Y v := by
  simp [derivOp]
theorem derivOp_smul_left (r : ℝ) (X : 𝔤) (v : E) :
    h.derivOp π (r • X) v = r • h.derivOp π X v := by
  simp [derivOp]
theorem derivOp_neg_left (X : 𝔤) (v : E) : h.derivOp π (-X) v = -h.derivOp π X v := by
  simp [derivOp]
theorem derivOp_add {v w : E} (hv : h.IsSmoothVector π v) (hw : h.IsSmoothVector π w) (X : 𝔤) :
    h.derivOp π X (v + w) = h.derivOp π X v + h.derivOp π X w := by
  simp only [derivOp, expOrbit_add]
  rw [fderiv_add (h.differentiable_expOrbit π hv 0) (h.differentiable_expOrbit π hw 0)]
  rfl
theorem derivOp_smul {v : E} (hv : h.IsSmoothVector π v) (c : ℂ) (X : 𝔤) :
    h.derivOp π X (c • v) = c • h.derivOp π X v := by
  simp only [derivOp, expOrbit_smul]
  rw [fderiv_const_smul (h.differentiable_expOrbit π hv 0) c]
  rfl
theorem contDiff_orbit_expG_mul {v : E} (hv : h.IsSmoothVector π v) {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {φ₁ φ₂ φ₃ : V → 𝔤} (h₁ : ContDiff ℝ ∞ φ₁)
    (h₂ : ContDiff ℝ ∞ φ₂) (h₃ : ContDiff ℝ ∞ φ₃) :
    ContDiff ℝ ∞ (fun p => π (h.expG (φ₁ p) * h.expG (φ₂ p) * h.expG (φ₃ p)) v) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, 𝔤) ∞
      (fun p => h.expG (φ₁ p) * h.expG (φ₂ p) * h.expG (φ₃ p)) :=
    ((h.contMDiff_expG_comp h₁).mul (h.contMDiff_expG_comp h₂)).mul (h.contMDiff_expG_comp h₃)
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hv hm).contDiff
theorem isSmoothVector_derivOp {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    h.IsSmoothVector π (h.derivOp π X v) := by
  rw [isSmoothVector_iff]
  have hΨ : ContDiff ℝ ∞ (fun p : 𝔤 × 𝔤 => π (h.expG p.1 * h.expG p.2 * h.expG 0) v) :=
    h.contDiff_orbit_expG_mul π hv contDiff_fst contDiff_snd contDiff_const
  have hΨ' : ContDiff ℝ ∞ (Function.uncurry fun Z Y : 𝔤 => π (h.expG Z) (π (h.expG Y) v)) := by
    convert hΨ using 2 with p
    simp [BanachRep.map_mul_apply, Function.uncurry]
  have hd : ContDiff ℝ ∞ (fun Z : 𝔤 =>
      fderiv ℝ (fun Y : 𝔤 => π (h.expG Z) (π (h.expG Y) v)) 0) :=
    ContDiff.fderiv hΨ' contDiff_const (by simp)
  have key : h.expOrbit π (h.derivOp π X v) =
      fun Z => fderiv ℝ (fun Y : 𝔤 => π (h.expG Z) (π (h.expG Y) v)) 0 X := by
    funext Z
    have hc := ((π (h.expG Z)).restrictScalars ℝ).hasFDerivAt.comp (0 : 𝔤)
      (h.differentiable_expOrbit π hv 0).hasFDerivAt
    have e : (fun Y : 𝔤 => π (h.expG Z) (π (h.expG Y) v)) =
        ((π (h.expG Z)).restrictScalars ℝ) ∘ h.expOrbit π v := rfl
    rw [e, hc.fderiv]
    rfl
  rw [key]
  exact hd.clm_apply contDiff_const
theorem derivOp_bracket {v : E} (hv : h.IsSmoothVector π v) (X Y : 𝔤) :
    h.derivOp π (h.bracket X Y) v =
      h.derivOp π X (h.derivOp π Y v) - h.derivOp π Y (h.derivOp π X v) := by

  set A : ℝ × ℝ × ℝ → E :=
    fun p => π (h.expG (p.1 • X) * h.expG (p.2.1 • Y) * h.expG (p.2.2 • (-X))) v with hAdef
  have hA : ContDiff ℝ ∞ A := h.contDiff_orbit_expG_mul π hv
    (contDiff_fst.smul contDiff_const) ((contDiff_fst.comp contDiff_snd).smul contDiff_const)
    ((contDiff_snd.comp contDiff_snd).smul contDiff_const)
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  set D2 := fderiv ℝ (fderiv ℝ A) 0
  set er : ℝ × ℝ × ℝ := (1, 0, 0)
  set et : ℝ × ℝ × ℝ := (0, 1, 0)
  set eu : ℝ × ℝ × ℝ := (0, 0, 1)
  have hY := h.isSmoothVector_derivOp π hv Y
  have hX := h.isSmoothVector_derivOp π hv X

  have da : ∀ r : ℝ, fderiv ℝ A (r • er) et = π (h.expG (r • X)) (h.derivOp π Y v) := by
    intro r
    have h1 := hasDerivAt_comp_line (hAd (r • er)) et
    have h2 := ((π (h.expG (r • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π hv Y)
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp [A, er, et, BanachRep.map_mul_apply]

  have dc : ∀ t : ℝ, fderiv ℝ A (t • et) eu = -π (h.expG (t • Y)) (h.derivOp π X v) := by
    intro t
    have h1 := hasDerivAt_comp_line (hAd (t • et)) eu
    have h2 := ((π (h.expG (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π hv (-X))
    rw [derivOp_neg_left] at h2
    refine h1.unique ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', map_neg] at h2
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp [A, et, eu, BanachRep.map_mul_apply]

  have db : D2 er et = h.derivOp π X (h.derivOp π Y v) := by
    have h1 := hasDerivAt_fderiv_line hA 0 er et
    have h2 := h.hasDerivAt_derivOp π hY X
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp only [zero_add]
    rw [da]
  have dd : D2 et eu = -h.derivOp π Y (h.derivOp π X v) := by
    have h1 := hasDerivAt_fderiv_line hA 0 et eu
    have h2 := (h.hasDerivAt_derivOp π hX Y).neg
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp only [zero_add]
    rw [dc]
    rfl
  have hsymm : D2 eu et = D2 et eu :=
    (hA.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) eu et

  have diag : ∀ s : ℝ, fderiv ℝ A (s • (er + eu)) et = h.derivOp π (h.Ad (h.expG (s • X)) Y) v := by
    intro s
    have h1 := hasDerivAt_comp_line (hAd (s • (er + eu))) et
    have h2 := h.hasDerivAt_derivOp π hv (h.Ad (h.expG (s • X)) Y)
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
    simp only [A, er, eu, et, Prod.smul_mk, Prod.mk_add_mk, smul_zero, smul_eq_mul, mul_one,
      mul_zero, add_zero, zero_add]
    rw [← map_smul, expG_Ad, smul_neg, expG_neg]
  have hg := hasDerivAt_fderiv_line hA 0 (er + eu) et
  have hg' := (fderiv ℝ (h.expOrbit π v) 0).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (h.hasDerivAt_Ad_expG X Y)
  have e := hg.unique (hg'.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
  · change D2 (er + eu) et = h.derivOp π (h.bracket X Y) v at e
    rw [← e, map_add, ContinuousLinearMap.add_apply, db, hsymm, dd, sub_eq_add_neg]
  · simp only [zero_add, Function.comp_apply]
    rw [diag]
    rfl
def toLie (X : 𝔤) : h.lieSubalgebra := ⟨X, X.2⟩
def ofLie (X : h.lieSubalgebra) : 𝔤 := ⟨X, X.2⟩
@[simp] theorem coe_ofLie (X : h.lieSubalgebra) : ((h.ofLie X : 𝔤) : 𝔸) = X := rfl
theorem ofLie_lie (X Y : h.lieSubalgebra) : h.ofLie ⁅X, Y⁆ = h.bracket (h.ofLie X) (h.ofLie Y) := rfl
noncomputable def smoothOp (g : G) : h.smoothVectors π →ₗ[ℂ] h.smoothVectors π where
  toFun v := ⟨π g v, h.isSmoothVector_map π v.2 g⟩
  map_add' v w := by ext; simp
  map_smul' c v := by ext; simp
@[simp] theorem coe_smoothOp (g : G) (v : h.smoothVectors π) :
    ((h.smoothOp π g v : h.smoothVectors π) : E) = π g v := rfl
noncomputable def derivEnd (X : 𝔤) : Module.End ℂ (h.smoothVectors π) where
  toFun v := ⟨h.derivOp π X v, h.isSmoothVector_derivOp π v.2 X⟩
  map_add' v w := by ext; exact h.derivOp_add π v.2 w.2 X
  map_smul' c v := by ext; exact h.derivOp_smul π v.2 c X
@[simp] theorem coe_derivEnd (X : 𝔤) (v : h.smoothVectors π) :
    ((h.derivEnd π X v : h.smoothVectors π) : E) = h.derivOp π X v := rfl
attribute [local instance 100] LieRing.ofAssociativeRing
noncomputable def derivLie : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (h.smoothVectors π) where
  toFun X := h.derivEnd π (h.ofLie X)
  map_add' X Y := by ext v; exact h.derivOp_add_left π _ _ _
  map_smul' r X := by ext v; exact h.derivOp_smul_left π r _ _
  map_lie' {X Y} := by
    ext v
    rw [h.ofLie_lie, Ring.lie_def]
    exact h.derivOp_bracket π v.2 _ _
noncomputable def uAction :
    UniversalEnvelopingAlgebra ℝ h.lieSubalgebra →ₐ[ℝ] Module.End ℂ (h.smoothVectors π) :=
  UniversalEnvelopingAlgebra.lift ℝ (h.derivLie π)
end IsExpLieAlgebra
end GroundTheory.Automorphic


