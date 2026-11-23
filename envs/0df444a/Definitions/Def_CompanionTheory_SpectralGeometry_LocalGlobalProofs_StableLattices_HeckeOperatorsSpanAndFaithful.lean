-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:03.804681+00:00
-- url     : https://prove2.me/theorems/750770c5-b82c-4f2a-8bd3-591446a3cfb1
-- title:
--   Hecke Operators Span And Faithful
-- statement:
--   Definitions and structural lemmas for Hecke Operators Span And Faithful, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeBasis
variable {G : Type} [Group G] (K : Subgroup G)
theorem lam_single (g : G) (y : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single y c) = Finsupp.single (g • y) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
theorem lam_mul (g g' : G) (u : (G ⧸ K) →₀ ℂ) :
    lam K (g * g') u = lam K g (lam K g' u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single, mul_smul]
theorem lam_apply_smul (g : G) (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) :
    lam K g u (g • y) = u y :=
  Finsupp.mapDomain_apply (MulAction.injective g) u y
def IsFixed (u : (G ⧸ K) →₀ ℂ) : Prop := ∀ k ∈ K, lam K k u = u
variable {K}
theorem lam_congr {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x x' : G}
    (h : (x : G ⧸ K) = x') : lam K x u = lam K x' u := by
  have hk : x⁻¹ * x' ∈ K := QuotientGroup.eq.1 h
  have : x' = x * (x⁻¹ * x') := by group
  rw [this, lam_mul, hu _ hk]
variable (K)
def op (u : (G ⧸ K) →₀ ℂ) : Module.End ℂ ((G ⧸ K) →₀ ℂ) :=
  Finsupp.lsum ℂ fun y => LinearMap.toSpanSingleton ℂ _ (lam K (Quotient.out y) u)
theorem op_single_out (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) (c : ℂ) :
    op K u (Finsupp.single y c) = c • lam K (Quotient.out y) u := by
  simp [op, LinearMap.toSpanSingleton_apply]
variable {K}
theorem op_single {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) (x : G) (c : ℂ) :
    op K u (Finsupp.single (x : G ⧸ K) c) = c • lam K x u := by
  rw [op_single_out, lam_congr hu (QuotientGroup.out_eq' (x : G ⧸ K))]
theorem op_mem {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u ∈ Hk K := by
  rw [Hk, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hgx : g • (x : G ⧸ K) = ((g * x : G) : G ⧸ K) := rfl
    simp only [Finsupp.lsingle_apply, Module.End.mul_apply, LinearMap.comp_apply]
    rw [op_single hu, lam_single, hgx, op_single hu, lam_mul]
    simp
variable (K)
def delta : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1
variable {K}
def orbitVec (hK : IsHeckePair K) (g : G) : (G ⧸ K) →₀ ℂ :=
  ∑ y ∈ (hK g).toFinset, Finsupp.single y (1 : ℂ)
open Classical in
theorem orbitVec_apply (hK : IsHeckePair K) (g : G) (z : G ⧸ K) :
    orbitVec hK g z = if z ∈ MulAction.orbit K (g : G ⧸ K) then 1 else 0 := by
  classical
  simp [orbitVec, Finsupp.finsetSum_apply, Finsupp.single_apply]
theorem lam_apply (k : G) (u : (G ⧸ K) →₀ ℂ) (z : G ⧸ K) :
    lam K k u z = u ((k⁻¹ : G) • z) := by
  have := lam_apply_smul K k u ((k⁻¹ : G) • z)
  rwa [smul_inv_smul] at this
theorem orbitVec_fixed (hK : IsHeckePair K) (g : G) : IsFixed K (orbitVec hK g) := by
  classical
  intro k hk
  ext z
  have hmem : ((k⁻¹ : G) • z ∈ MulAction.orbit K (g : G ⧸ K)) ↔
      z ∈ MulAction.orbit K (g : G ⧸ K) := by
    have e : (k⁻¹ : G) • z = (⟨k, hk⟩ : K)⁻¹ • z := rfl
    rw [e, ← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff (a := z), MulAction.orbit_smul]
  rw [lam_apply, orbitVec_apply, orbitVec_apply]
  simp only [hmem]
def heckeOp (hK : IsHeckePair K) (g : G) : Hk K :=
  ⟨op K (orbitVec hK g), op_mem (orbitVec_fixed hK g)⟩
end GlobalTheory.CompanionTheory.HeckeBasis


