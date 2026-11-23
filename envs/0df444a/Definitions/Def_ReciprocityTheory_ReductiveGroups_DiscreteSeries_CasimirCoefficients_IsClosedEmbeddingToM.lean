-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:16.690831+00:00
-- url     : https://prove2.me/theorems/4c7ff6fc-4e38-487a-a42c-ee7191f30a81
-- title:
--   Is Closed Embedding To M
-- statement:
--   Definitions and structural lemmas for Is Closed Embedding To M, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/IsClosedEmbeddingToM.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
import Theorems.Thm_UpperTheory_Reformulated_B_Qk16_isClosedEmbedding_toM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology MeasureTheory
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def hs (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖ ^ 2
lemma Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]
def UJ (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε (g : Matrix (Fin n) (Fin n) ℂ)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g : Matrix (Fin n) (Fin n) ℂ) * h)
        = (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg, hh]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq, inUJ] at *
    have h1 : ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (g : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    calc ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg]
      _ = Jm ε := by
          rw [show ∀ A B C D E : Matrix (Fin n) (Fin n) ℂ, A * (B * C * D) * E = (A * B) * C * (D * E)
            from fun A B C D E => by simp only [Matrix.mul_assoc], h1, h2, Matrix.one_mul, Matrix.mul_one]
abbrev toM {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
lemma isClosedEmbedding_toM (ε : Fin n → Bool) : IsClosedEmbedding (fun g : UJ ε => toM g) := by
  first | exact UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM .. | (apply UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk16.isClosedEmbedding_toM <;> first | assumption | infer_instance)
instance (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (isClosedEmbedding_toM ε).locallyCompactSpace
instance (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbedding_toM ε).isInducing.secondCountableTopology
instance (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _
instance (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩
lemma Kset_mul (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hh : h ∈ Kset ε) : g * h ∈ Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]
lemma Kset_star (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    star g ∈ Kset ε := by
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  have h := congrArg star hg.2
  simp only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] at h
  simpa [Matrix.star_eq_conjTranspose] using h.symm
def KG (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | toM g ∈ Kset ε}
  mul_mem' := by
    intro g h hg hh
    show toM g * toM h ∈ Kset ε
    exact Kset_mul ε hg hh
  one_mem' := by
    show (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε
    refine ⟨Submonoid.one_mem _, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro g hg
    have h2 : toM g⁻¹ = star (toM g) :=
      Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem hg.1)
    show toM g⁻¹ ∈ Kset ε
    rw [h2]
    exact Kset_star ε hg
abbrev toMK {ε : Fin n → Bool} (k : KG ε) : Matrix (Fin n) (Fin n) ℂ := toM (k : UJ ε)
end ReciprocityTheory.ChartRestriction.DS.S7


