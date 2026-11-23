-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__OfPositiveTrivial_b4304d4fbed4f169
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__OfPositiveTrivial_b4304d4fbed4f169
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:34.026291+00:00
-- url     : https://prove2.me/theorems/1f5130d9-9b37-4e50-a7f7-99cad099a5ec
-- title:
--   Of Positive Trivial
-- statement:
--   Definitions and structural lemmas for Of Positive Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/OfPositiveTrivial.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStabiliserImageSubgroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_mul_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions
open scoped Matrix ENNReal
namespace GlobalTheory.Published
namespace GaussBonnet
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
theorem mat_mul {P Q : ℕ} (g g' : UpqT P Q) : UpqT.mat (g * g') = UpqT.mat g * UpqT.mat g' := rfl
theorem mat_one {P Q : ℕ} : UpqT.mat (1 : UpqT P Q) = 1 := rfl
def IsOrthFrame (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {P Q : ℕ}
    (B : Matrix (Fin r) (Fin P ⊕ Fin Q) ℂ) : Prop :=
  ∀ a b, hermC τ G (fun k => B k a) (fun k => B k b) = Formalism.UG.Jpq P Q a b
def realImage (Ψ : Finset (E →+* ℂ)) {P Q : Ψ → ℕ}
    (B : ∀ τ : Ψ, Matrix (Fin r) (Fin (P τ) ⊕ Fin (Q τ)) ℂ) (Γ : Subgroup (GL (Fin r) E)) :
    Subgroup (∀ τ : Ψ, UpqT (P τ) (Q τ)) where
  carrier := {g | ∃ γ ∈ Γ, ∀ τ : Ψ,
    B τ * UpqT.mat (g τ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * B τ}
  one_mem' := ⟨1, Γ.one_mem, fun τ => by simp [mat_one]⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ, ha⟩ ⟨δ, hδ, hb⟩
    refine ⟨γ * δ, Γ.mul_mem hγ hδ, fun τ => ?_⟩
    rw [Pi.mul_apply, mat_mul, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Units.val_mul,
      Matrix.map_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro a ⟨γ, hγ, ha⟩
    refine ⟨γ⁻¹, Γ.inv_mem hγ, fun τ => ?_⟩
    have h1 : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        (γ : Matrix (Fin r) (Fin r) E).map τ.1 = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul]; simp
    have h2 : UpqT.mat (a τ) * UpqT.mat (a⁻¹ τ) = 1 := by
      rw [← mat_mul, Pi.inv_apply, mul_inv_cancel, mat_one]
    calc B τ * UpqT.mat (a⁻¹ τ)
        = ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
          ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * B τ) * UpqT.mat (a⁻¹ τ) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = _ := by rw [← ha, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
end GaussBonnet
open GaussBonnet
def GaussBonnetUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (Γ : Subgroup (GL (Fin r) E)) (P Q : Ψ → ℕ)
    (B : ∀ τ : Ψ, Matrix (Fin r) (Fin (P τ) ⊕ Fin (Q τ)) ℂ) (c : CDHaar)
    (D : Set (∀ τ : Ψ, UpqT (P τ) (Q τ))),
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 →
    Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
    (∀ τ, P τ + Q τ = r) → (∀ τ : Ψ, IsOrthFrame τ.1 G (B τ)) →
    (∀ γ ∈ Γ, ∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) →
    Subgroup.Commensurable Γ (GlobalTheory.FiniteCovolume.uStabSubgroup G Λ) →
    (∀ γ ∈ Γ, ∀ (n : ℕ) (z : E), 0 < n →
      ((γ ^ n : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = z • (1 : Matrix (Fin r) (Fin r) E) → γ = 1) →
    IsFundamentalDomain (realImage Ψ B Γ) D (Measure.pi fun τ : Ψ => c.cd (P τ) (Q τ)) →
    ∃ n : ℕ, (Measure.pi fun τ : Ψ => c.cd (P τ) (Q τ)) D * ∏ τ : Ψ, (r.choose (P τ) : ℝ≥0∞) = n
namespace GaussBonnet
end GaussBonnet
end GlobalTheory.Published


