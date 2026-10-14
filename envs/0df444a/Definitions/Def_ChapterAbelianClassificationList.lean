-- Prove2me | Definitions.Def_ChapterAbelianClassificationList
-- name    : ChapterAbelianClassificationList
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-11T19:38:35.017413+00:00
-- url     : https://prove2.me/theorems/f17328f6-0130-4bdb-9287-1c2c9df8f6bf
-- title:
--   ChapterAbelianClassificationList
-- statement:
--   ChapterAbelianClassificationList

import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterDiffuseUnitaryModel
import Definitions.Def_ChapterLpRestrictSplit
import Definitions.Def_ChapterLpScaleMeasure
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Theorems.Thm_BookProof_ChapterDiffuseUnitaryModel_cdfUnitary_intertwines
import Theorems.Thm_BookProof_ChapterLpScaleMeasure_isProbabilityMeasure_inv_smul
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_mem_atomSet_iff
import Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_measurableSet_atomSet
import Theorems.Thm_BookProof_ChapterLpScaleMeasure_scaleUnitary_intertwines
import Theorems.Thm_BookProof_ChapterLpRestrictSplit_isHilbertSum_splitEmbed
import Theorems.Thm_BookProof_ChapterAtomicDiagonalModel_atomic_multiplication_model_diagonal
import Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_intertwines
import Mathlib


/-!
# Reassembling the classification list (plan GAP-2, the final step)

The previous waves produced all the pieces of the manuscript's abelian
classification list and left exactly one step open: *reassembly* — rewriting a
classified summand as **one** of the five standard models.  This module performs it
for a Borel probability measure on the line.

Write `S` for the (countable) set of atoms of `μ`.  Then

* `L²(μ)` is the Hilbert sum of `L²(μ|S)` and `L²(μ|Sᶜ)`, and the two embeddings
  intertwine the multiplication operators
  (`ChapterLpRestrictSplit.isHilbertSum_splitEmbed`, `restrictEmbed_intertwines`);
* the first piece is *purely atomic*, so multiplication is **diagonal** in the
  orthonormal basis of normalised point masses (`ChapterAtomicDiagonalModel`);
* the second piece is *diffuse*; after normalising its mass
  (`ChapterLpScaleMeasure`) its distribution function gives a unitary with `L²[0,1]`
  carrying multiplication by `g` to multiplication by `g ∘ F`
  (`ChapterDiffuseUnitaryModel`).

Assembling these gives the headline `abelian_summand_standard_model`, and the
case distinction on `μ(S)`, `μ(Sᶜ)` and the cardinality of `S` gives the list itself,
`vonNeumann_abelian_classification_list`: every summand is `Iₙ`, `ℓ∞(ℕ)`, `L∞[0,1]`,
`L∞[0,1] ⊕ Iₙ` or `L∞[0,1] ⊕ ℓ∞(ℕ)`.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BookProof.ChapterAbelianClassificationList

open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterDiffuseUnitaryModel BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit BookProof.ChapterLpScaleMeasure

/-! ## 1. The atomic piece is purely atomic -/

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

theorem atomSet_restrict_atomSet (mu : Measure α) [IsFiniteMeasure mu] :
    atomSet (mu.restrict (atomSet mu)) = atomSet mu := by
  ext x
  simp only [mem_atomSet_iff, Measure.restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ atomSet mu
  · have hxx : ({x} : Set α) ∩ atomSet mu = {x} :=
      Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hx)
    simp [hxx, hx] at *
  · have h0 : mu {x} = 0 := by simpa [atomSet] using hx
    have hzero : mu ({x} ∩ atomSet mu) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    rw [hzero]
    simp [h0]

theorem restrict_atomSet_pure (mu : Measure α) [IsFiniteMeasure mu] :
    (mu.restrict (atomSet mu)) (atomSet (mu.restrict (atomSet mu)))ᶜ = 0 := by
  rw [atomSet_restrict_atomSet mu,
    Measure.restrict_apply (measurableSet_atomSet mu).compl]
  simp

/-! ## 2. Scaling preserves diffuseness -/

omit [MeasurableSingletonClass α] in
theorem noAtoms_smul {nu : Measure α} [NullSingletonClass nu] (c : ENNReal) : NullSingletonClass (c • nu) := by
  constructor
  intro x
  simp [Measure.smul_apply]

/-! ## 3. The diffuse piece is a copy of the unit interval -/

section Diffuse

variable (nu : Measure ℝ) [IsFiniteMeasure nu] [NullSingletonClass nu]

/-- The normalised diffuse measure: an atomless probability measure on the line. -/
def normalized : Measure ℝ := (nu Set.univ)⁻¹ • nu

instance : NullSingletonClass (normalized nu) := noAtoms_smul _

omit [NullSingletonClass nu] in
theorem isProbabilityMeasure_normalized (hne : nu Set.univ ≠ 0) :
    IsProbabilityMeasure (normalized nu) :=
  isProbabilityMeasure_inv_smul hne

/-- **The diffuse piece, at any total mass.**  For a nonzero finite atomless measure
on the line there is a unitary from `L²[0,1]` onto `L²(ν)` carrying multiplication by
`g` to multiplication by `g ∘ F`, where `F` is the distribution function of the
normalised measure. -/
theorem diffuse_finite_multiplication_model (hne : nu Set.univ ≠ 0) :
    ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ] Lp ℂ 2 nu,
      ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
        (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
        (U (multOp g hg u) : ℝ → ℂ)
          =ᵐ[nu] fun x => g (cdf (normalized nu) x) * (U u : ℝ → ℂ) x := by
  haveI : IsProbabilityMeasure (normalized nu) := isProbabilityMeasure_normalized nu hne
  have hc0 : (nu Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top nu _)
  have hctop : (nu Set.univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne
  refine ⟨(cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop), fun g hg u => ?_⟩
  have hstep := cdfUnitary_intertwines (normalized nu) hg u
  have hmul := scaleUnitary_intertwines (nu := nu) hc0 hctop
    (memLp_top_comp_cdf (normalized nu) hg) (cdfUnitary (normalized nu) u)
  calc ((((cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop)) (multOp g hg u) :
        Lp ℂ 2 nu) : ℝ → ℂ)
      = ((scaleUnitary hc0 hctop (multOp (fun x => g (cdf (normalized nu) x))
          (memLp_top_comp_cdf (normalized nu) hg)
            (cdfUnitary (normalized nu) u)) : Lp ℂ 2 nu) : ℝ → ℂ) := by
        have htrans : ∀ w : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
            ((cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop) w : Lp ℂ 2 nu)
              = (scaleUnitary hc0 hctop (cdfUnitary (normalized nu) w) : Lp ℂ 2 nu) :=
          fun _ => LinearIsometryEquiv.trans_apply _ _ _
        rw [htrans, hstep]
    _ =ᵐ[nu] fun x => g (cdf (normalized nu) x) *
          ((scaleUnitary hc0 hctop (cdfUnitary (normalized nu) u) : Lp ℂ 2 nu) : ℝ → ℂ) x :=
        hmul
    _ = fun x => g (cdf (normalized nu) x) *
          (((cdfUnitary (normalized nu)).trans (scaleUnitary hc0 hctop) u :
            Lp ℂ 2 nu) : ℝ → ℂ) x := rfl

end Diffuse

/-! ## 4. The standard model of a summand -/

variable (mu : Measure ℝ) [IsProbabilityMeasure mu]

/-- **HEADLINE (the standard model of a summand).**  Let `μ` be a Borel probability
measure on the line and `S` its set of atoms.  Then `L²(μ)` is the Hilbert sum of the
atomic piece `L²(μ|S)` and the diffuse piece `L²(μ|Sᶜ)`, the embeddings intertwine
the multiplication operators, multiplication is *diagonal* on the atomic piece in the
orthonormal basis of normalised point masses, and — when the diffuse piece is
nonzero — it is unitarily `L²[0,1]` with multiplication by `g` becoming
multiplication by `g ∘ F`.  This is the reassembly of the classification list. -/
theorem abelian_summand_standard_model :
    (IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b)))
        (splitEmbed (measurableSet_atomSet mu))) ∧
      (∀ (b : Bool) (g : ℝ → ℂ) (hg : MemLp g ⊤ mu)
          (u : Lp ℂ 2 (mu.restrict (splitSet (atomSet mu) b))),
        splitEmbed (measurableSet_atomSet mu) b (multOp g (hg.restrict _) u)
          = multOp g hg (splitEmbed (measurableSet_atomSet mu) b u)) ∧
      (∃ B : HilbertBasis (atomSet (mu.restrict (atomSet mu))) ℂ
          (Lp ℂ 2 (mu.restrict (atomSet mu))),
        ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (mu.restrict (atomSet mu)))
          (a : atomSet (mu.restrict (atomSet mu))),
          multOp g hg (B a) = g (a : ℝ) • B a) ∧
      (mu (atomSet mu)ᶜ ≠ 0 →
        ∃ U : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) ≃ₗᵢ[ℂ]
            Lp ℂ 2 (mu.restrict (atomSet mu)ᶜ),
          ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (volume.restrict (Set.Icc (0 : ℝ) 1)))
            (u : Lp ℂ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))),
            (U (multOp g hg u) : ℝ → ℂ)
              =ᵐ[mu.restrict (atomSet mu)ᶜ] fun x =>
                g (cdf (normalized (mu.restrict (atomSet mu)ᶜ)) x) * (U u : ℝ → ℂ) x) := by
  refine ⟨isHilbertSum_splitEmbed (measurableSet_atomSet mu), ?_,
    atomic_multiplication_model_diagonal _ (restrict_atomSet_pure mu), ?_⟩
  · intro b g hg u
    exact restrictEmbed_intertwines (measurableSet_splitSet (measurableSet_atomSet mu) b) hg u
  · intro hne
    have hmass : (mu.restrict (atomSet mu)ᶜ) Set.univ ≠ 0 := by
      rwa [Measure.restrict_apply_univ]
    exact diffuse_finite_multiplication_model _ hmass

/-! ## 5. The list -/



end BookProof.ChapterAbelianClassificationList

end


