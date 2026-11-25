-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_EqZeroOfIsIsoSub
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_EqZeroOfIsIsoSub
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:03:01.845392+00:00
-- url     : https://prove2.me/theorems/a83e1a63-fdc0-5a2b-90aa-562989d61917
-- title:
--   Eq Zero Of Is Iso Sub
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Is Iso Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/EqZeroOfIsIsoSub.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Lattice
variable {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]
def IsIsoSub (form : abelian₂ →ₗ[ℤ] abelian₂ →ₗ[ℤ] ℤ) (I : Submodule O abelian₂) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, form v w = 0
def IsSaturated (I : Submodule O abelian₂) : Prop :=
  ∀ (v : abelian₂) (n : ℤ), n ≠ 0 → n • v ∈ I → v ∈ I
def IsNzFamily (I : Submodule O abelian₂) (ρ : ℕ) (v : Fin ρ → abelian₂) : Prop :=
  1 ≤ ρ ∧ (∀ a, v a ∈ I) ∧ LinearIndependent O v ∧
    (Submodule.span O (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0
end Lattice
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
structure CuspData (D : ComponentData II Ψ K ι Ω E) (O : Type) [CommRing O] (abelian₂ : Type)
    [AddCommGroup abelian₂] [Module O abelian₂] where

  rank : ℕ
  basis : Module.Basis (Fin rank) ℤ abelian₂

  form : abelian₂ →ₗ[ℤ] abelian₂ →ₗ[ℤ] ℤ
  alt : ∀ v, form v v = 0
  unimod : IsUnit (Matrix.of fun a b => form (basis a) (basis b)).det

  emb : Ψ → O →+* ℂ

  normSq : ((Σ k, ι k) → ℂ) → abelian₂ → ℝ
  normSq_pos : ∀ z ∈ D.Xo, ∀ v, v ≠ 0 → 0 < normSq z v
  form_le : ∀ z ∈ D.Xo, ∀ v w, ((form v w : ℤ) : ℝ) ^ 2 ≤ normSq z v * normSq z w

  lie : ((Σ k, ι k) → ℂ) → Ψ → abelian₂ → Fin (D.N - D.j) → ℂ
  lie_add : ∀ z τ v w, lie z τ (v + w) = lie z τ v + lie z τ w
  lie_smul : ∀ z τ (a : O) v, lie z τ (a • v) = emb τ a • lie z τ v
  lie_le : ∀ z ∈ D.Xo, ∀ v, ∑ τ, ∑ c, ‖lie z τ v c‖ ^ 2 ≤ normSq z v
  inj : ∀ z ∈ D.Xo, ∀ τ (I : Submodule O abelian₂), IsIsoSub form I → ∀ (ρ : ℕ) (v : Fin ρ → abelian₂),
    (∀ a, v a ∈ I) → LinearIndependent O v → LinearIndependent ℂ fun a => lie z τ (v a)
  torus : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
    normSq (torusSmul c z) = normSq z ∧ lie (torusSmul c z) = lie z
namespace CuspData
variable {D : ComponentData II Ψ K ι Ω E} {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]
  (Cd : CuspData D O abelian₂)
def gramLie (z : (Σ k, ι k) → ℂ) (τ : Ψ) {ρ : ℕ} (v : Fin ρ → abelian₂) : Matrix (Fin ρ) (Fin ρ) ℂ :=
  Matrix.of fun a b => ∑ c, starRingEnd ℂ (Cd.lie z τ (v a) c) * Cd.lie z τ (v b) c
open Classical in

def Nz (z : (Σ k, ι k) → ℂ) (I : Submodule O abelian₂) : ℝ :=
  if h : ∃ ρ v, IsNzFamily I ρ v then
    (∏ τ, (Cd.gramLie z τ h.choose_spec.choose).det.re) /
      ((Submodule.span O (Set.range h.choose_spec.choose)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)
  else 1
def cuspWeight (z : (Σ k, ι k) → ℂ) : ℝ :=
  max 0 (sSup {x | ∃ I : Submodule O abelian₂, I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧
    x = -Real.log (Cd.Nz z I)})
end CuspData
namespace Line
open GaussianInt
def gaussEquiv : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := ![v.re, v.im]
  invFun f := ⟨f 0, f 1⟩
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' n v := by
    ext i; fin_cases i <;> simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  left_inv v := by simp
  right_inv f := by ext i; fin_cases i <;> simp
def gaussBasis : Module.Basis (Fin 2) ℤ GaussianInt := Module.Basis.ofEquivFun gaussEquiv
theorem gaussBasis_zero : gaussBasis 0 = ⟨1, 0⟩ := by
  simp [gaussBasis, gaussEquiv, Module.Basis.coe_ofEquivFun]
theorem gaussBasis_one : gaussBasis 1 = ⟨0, 1⟩ := by
  simp [gaussBasis, gaussEquiv, Module.Basis.coe_ofEquivFun]
def gaussForm : GaussianInt →ₗ[ℤ] GaussianInt →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => v.re * w.im - v.im * w.re)
    (fun v v' w => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)
    (fun v w w' => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)
theorem gaussForm_apply (v w : GaussianInt) : gaussForm v w = v.re * w.im - v.im * w.re := rfl
theorem normSq_toComplex (v : GaussianInt) : Complex.normSq (toComplex v) = (v.re : ℝ) ^ 2 + (v.im : ℝ) ^ 2 := by
  rw [toComplex_def₂, Complex.normSq_mk]
  ring
theorem eq_zero_of_isIsoSub {I : Submodule GaussianInt GaussianInt} (hI : IsIsoSub gaussForm I) {v : GaussianInt}
    (hv : v ∈ I) : v = 0 := by
  have h := hI v hv (⟨0, 1⟩ • v) (I.smul_mem _ hv)
  rw [gaussForm_apply, smul_eq_mul] at h
  simp [Zsqrtd.re_mul, Zsqrtd.im_mul] at h
  have h2 : v.re * v.re + v.im * v.im = 0 := by linarith
  have hre : v.re = 0 := by nlinarith [mul_self_nonneg v.re, mul_self_nonneg v.im]
  have him : v.im = 0 := by nlinarith [mul_self_nonneg v.re, mul_self_nonneg v.im]
  exact Zsqrtd.ext hre him
def gaussCusp (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    CuspData (lineData II hII) GaussianInt GaussianInt where
  rank := 2
  basis := gaussBasis
  form := gaussForm
  alt v := by rw [gaussForm_apply]; ring
  unimod := by
    have : (Matrix.of fun a b => gaussForm (gaussBasis a) (gaussBasis b)).det = 1 := by
      rw [Matrix.det_fin_two]
      simp [gaussForm_apply, gaussBasis_zero, gaussBasis_one]
    rw [this]
    exact isUnit_one
  emb _ := toComplex
  normSq _ v := Complex.normSq (toComplex v)
  normSq_pos _ _ v hv := Complex.normSq_pos.2 fun h => hv (toComplex_injective (by rw [h, map_zero]))
  form_le _ _ v w := by
    rw [gaussForm_apply, normSq_toComplex, normSq_toComplex]
    push_cast
    nlinarith [sq_nonneg ((v.re : ℝ) * w.re + v.im * w.im)]
  lie _ _ v _ := toComplex v
  lie_add _ _ v w := by funext c; simp
  lie_smul _ _ a v := by funext c; simp [smul_eq_mul]
  lie_le _ _ v := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Complex.sq_norm]
    show ∑ _c : Fin 1, Complex.normSq (toComplex v) ≤ Complex.normSq (toComplex v)
    simp
  inj _ _ _ I hI ρ v hv hli := by
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ
    · exact linearIndependent_empty_type
    · exact absurd (eq_zero_of_isIsoSub hI (hv ⟨0, hρ⟩)) (hli.ne_zero ⟨0, hρ⟩)
  torus _ _ _ _ := ⟨rfl, rfl⟩
end Line
end GroundTheory.Heights₂.Heights.LowerBoundFree


