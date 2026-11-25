-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
-- name    : GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:27:30.160134+00:00
-- url     : https://prove2.me/theorems/058a1bcf-8ad1-43de-a195-a05abd898202
-- title:
--   Gelfand Kazhdan
-- statement:
--   Definitions and structural lemmas for Gelfand Kazhdan, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose/GelfandKazhdan.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCriterion
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_MatrixSimilarity
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_ContCoeff_mul
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_BiEquivariantSigmaInvariant_inv
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic.ContragredientTranspose
open Set Filter Topology MulAction Matrix GroundTheory.Automorphic.Whittaker
section ConjActTop
variable {G : Type*} [Group G] [TopologicalSpace G]
scoped instance conjActTopology : TopologicalSpace (ConjAct G) := ‹TopologicalSpace G›
theorem continuous_ofConjAct : Continuous (ConjAct.ofConjAct : ConjAct G → G) := continuous_id
scoped instance [IsTopologicalGroup G] : IsTopologicalGroup (ConjAct G) :=
  inferInstanceAs (IsTopologicalGroup G)
scoped instance [LocallyCompactSpace G] : LocallyCompactSpace (ConjAct G) :=
  inferInstanceAs (LocallyCompactSpace G)
scoped instance [T2Space G] : T2Space (ConjAct G) := inferInstanceAs (T2Space G)
scoped instance [TotallyDisconnectedSpace G] : TotallyDisconnectedSpace (ConjAct G) :=
  inferInstanceAs (TotallyDisconnectedSpace G)
scoped instance [SigmaCompactSpace G] : SigmaCompactSpace (ConjAct G) :=
  inferInstanceAs (SigmaCompactSpace G)
scoped instance [IsTopologicalGroup G] : ContinuousSMul (ConjAct G) G where
  continuous_smul := by
    have e : (fun p : ConjAct G × G => p.1 • p.2) =
        fun p => ConjAct.ofConjAct p.1 * p.2 * (ConjAct.ofConjAct p.1)⁻¹ := by
      funext p
      exact ConjAct.smul_def _ _
    rw [e]
    have h1 : Continuous fun p : ConjAct G × G => ConjAct.ofConjAct p.1 :=
      continuous_ofConjAct.comp continuous_fst
    exact (h1.mul continuous_snd).mul h1.inv
end ConjActTop
section Transpose
variable {F : Type*} [Field F] {n : ℕ}
def transposeGL (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨(g : Matrix (Fin n) (Fin n) F)ᵀ, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
@[simp]
theorem coe_transposeGL (g : GL (Fin n) F) :
    (transposeGL g : Matrix (Fin n) (Fin n) F) = (g : Matrix (Fin n) (Fin n) F)ᵀ := rfl
@[simp]
theorem transposeGL_transposeGL (g : GL (Fin n) F) : transposeGL (transposeGL g) = g :=
  Units.ext (transpose_transpose _)
theorem transposeGL_mul (g h : GL (Fin n) F) :
    transposeGL (g * h) = transposeGL h * transposeGL g :=
  Units.ext (by simp [transpose_mul])
@[simp]
theorem transposeGL_one : transposeGL (1 : GL (Fin n) F) = 1 :=
  Units.ext (by simp)
theorem transposeGL_inv (g : GL (Fin n) F) : transposeGL g⁻¹ = (transposeGL g)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← transposeGL_mul, mul_inv_cancel, transposeGL_one]
def thetaT : GL (Fin n) F ≃* GL (Fin n) F where
  toFun g := (transposeGL g)⁻¹
  invFun g := (transposeGL g)⁻¹
  left_inv g := by simp [← transposeGL_inv]
  right_inv g := by simp [← transposeGL_inv]
  map_mul' g h := by rw [transposeGL_mul, _root_.mul_inv_rev]
variable [TopologicalSpace F]
theorem continuous_transposeGL :
    Continuous (transposeGL : GL (Fin n) F → GL (Fin n) F) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_transpose,
    Units.continuous_coe_inv.matrix_transpose⟩
def transposeHomeo : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toFun := transposeGL
  invFun := transposeGL
  left_inv := transposeGL_transposeGL
  right_inv := transposeGL_transposeGL
  continuous_toFun := continuous_transposeGL
  continuous_invFun := continuous_transposeGL
end Transpose
section Baire
variable {H X : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H] [TopologicalSpace X]
  [T2Space X] [LocallyCompactSpace X] [MulAction H X] [ContinuousSMul H X]
end Baire
section Relations
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
def tauSpan (U : Set (GL (Fin n) F)) : Submodule ℂ (GL (Fin n) F → ℂ) :=
  Submodule.span ℂ {r | ∃ f ∈ supportedIn U, r = f + fun x => f (transposeGL x)}
def relT (U : Set (GL (Fin n) F)) : Submodule ℂ (GL (Fin n) F → ℂ) :=
  relSpan (1 : ConjAct (GL (Fin n) F) →* ℂ) U ⊔ tauSpan U
end Relations
section OneClass
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
end OneClass
section Stability
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
def thetaC (h : ConjAct (GL (Fin n) F)) : ConjAct (GL (Fin n) F) :=
  ConjAct.toConjAct (thetaT (ConjAct.ofConjAct h))
end Stability
section Fibre
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
end Fibre
section Global
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
noncomputable def charCoeffs (x : GL (Fin n) F) : Fin (n + 1) → F :=
  fun k => (x : Matrix (Fin n) (Fin n) F).charpoly.coeff k
end Global
end GroundTheory.Automorphic.ContragredientTranspose


