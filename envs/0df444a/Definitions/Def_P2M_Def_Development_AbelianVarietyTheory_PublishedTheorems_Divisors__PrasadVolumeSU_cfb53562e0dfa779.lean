-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PrasadVolumeSU_cfb53562e0dfa779
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PrasadVolumeSU_cfb53562e0dfa779
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:13.647385+00:00
-- url     : https://prove2.me/theorems/4210a4d3-d77a-4a1e-ae46-658d508b5f8e
-- title:
--   Prasad Volume SU
-- statement:
--   Definitions and structural lemmas for Prasad Volume SU, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PrasadVolumeSU.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Statements_PlaceShiftStatements_DefiniteBound
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsCompactDualHaar_372789bc53a272b8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SUVol
open NumberField IsDedekindDomain MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
abbrev suReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : Subgroup (Ψ → GL (Fin r) ℂ) :=
  suGrp fun τ : Ψ => G.map τ.1
def suStab (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Subgroup (suReal Ψ G) where
  carrier := {g | ∃ γ : GL (Fin r) E, IsUStab G Λ γ ∧ (γ : Matrix (Fin r) (Fin r) E).det = 1 ∧
    ∀ τ : Ψ, ((g.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  one_mem' := ⟨1, ⟨by simp, by simp⟩, by simp, fun τ => by simp⟩
  mul_mem' := by
    rintro g h ⟨γ, ⟨g1, g2⟩, g3, g4⟩ ⟨δ, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨γ * δ, ⟨fun x y => ?_, fun x => ?_⟩, by simp [g3, h3], fun τ => ?_⟩
    · rw [Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, g1, h1]
    · rw [Units.val_mul, ← mulVec_mulVec, ← g2, ← h2]
    · rw [Units.val_mul, Matrix.map_mul, ← g4, ← h4]; rfl
  inv_mem' := by
    rintro g ⟨γ, ⟨g1, g2⟩, g3, g4⟩
    have e : ∀ x, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) = x := by
      intro x
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    have e1 : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨γ⁻¹, ⟨fun x y => ?_, fun x => ?_⟩, ?_, fun τ => ?_⟩
    · rw [← g1, e, e]
    · rw [g2 (_ *ᵥ x), e]
    · have := congrArg Matrix.det e1
      rwa [det_mul, g3, one_mul, det_one] at this
    · have e2 : ((g.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 = 1 := by
        rw [g4, ← Matrix.map_mul, e1]; simp
      exact Units.inv_eq_of_mul_eq_one_right e2
variable (E) in

def splitSign (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ℝ :=
  if (v.asIdeal.primesOver (𝓞 E)).ncard = 2 then 1 else -1
variable (E) in

def localFactor (r : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : ℝ :=
  ∏ j ∈ Finset.Icc 2 r, (1 - splitSign E v ^ j / (Ideal.absNorm v.asIdeal : ℝ) ^ j)⁻¹
def archFactor (r : ℕ) : ℝ := ∏ j ∈ Finset.Ico 1 r, (j.factorial : ℝ) / (2 * Real.pi) ^ (j + 1)
end GlobalTheory.SUVol
namespace GlobalTheory.Published
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SUVol GlobalTheory.UCls
def PrasadVolumeSU : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)),
    Unr E → SelfDualLat G Λ → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
    (∃ (τ : E →+* ℂ) (x y : Fin r → ℂ), 0 < (hermC τ G x x).re ∧ (hermC τ G y y).re < 0) →
    ∃ ℰ : ℝ, HasProd (localFactor E r) ℰ ∧
      ∀ [MeasurableSpace (suReal Ψ G)] [BorelSpace (suReal Ψ G)] (m : Measure (suReal Ψ G)),
        IsCompactDualHaar (fun τ : Ψ => G.map τ.1) m →
        ∀ 𝓕 : Set (suReal Ψ G), IsFundamentalDomain (suStab Ψ G Λ) 𝓕 m →
          m 𝓕 = ENNReal.ofReal (|(discr (maximalRealSubfield E) : ℝ)| ^ (((r : ℝ) ^ 2 - 1) / 2) *
            archFactor r ^ fdeg E * ℰ)
end GlobalTheory.Published


