-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:05.833623+00:00
-- url     : https://prove2.me/theorems/1b0723ae-60d3-4b9b-85fa-84561a85a6b1
-- title:
--   Statements Line Degree
-- statement:
--   Definitions and structural lemmas for Statements Line Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsLineDegree.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField
open scoped ComplexOrder
noncomputable section
abbrev ProjIdx (K : Type) [Field K] [NumberField K] (i : ℕ) : Type :=
  Module.Free.ChooseBasisIndex ℤ (𝓞 K) × Fin i
abbrev projBlocks (K : Type) [Field K] [NumberField K] (i : ℕ) : Unit → Type := fun _ => ProjIdx K i
abbrev ProjField (K : Type) [Field K] (i : ℕ) : Type := FractionRing (MvPolynomial (Fin i) K)
def projSpaceCoord (K : Type) [Field K] [NumberField K] (i : ℕ) :
    (Σ _ : Unit, ProjIdx K i) → ProjField K i :=
  fun p => algebraMap (MvPolynomial (Fin i) K) (ProjField K i)
    (C (integralBasis K p.2.1) * X p.2.2)
def projSpaceIdeal (K : Type) [Field K] [NumberField K] (i : ℕ) : Ideal (MRing (projBlocks K i)) :=
  mCoordIdeal (projSpaceCoord K i)
open scoped Classical in

def embComp {K : Type} [Field K] [NumberField K] {i : ℕ} (σ : K →+* ℂ) (z : ProjIdx K i → ℂ) :
    Fin i → ℂ :=
  fun j => ∑ m, (canonicalEmbedding.latticeBasis K).repr (Pi.single σ 1) m * z (m, j)
def latticeNormSq {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i)
    (z : ProjIdx K i → ℂ) : ℝ :=
  ∑ σ : K →+* ℂ, (star (embComp σ z) ⬝ᵥ (F.metric σ *ᵥ embComp σ z)).re
theorem latticeNormSq_term_nonneg {K : Type} [Field K] [NumberField K] {i : ℕ}
    (F : HermLattice K i) (σ : K →+* ℂ) (w : Fin i → ℂ) :
    0 ≤ (star w ⬝ᵥ (F.metric σ *ᵥ w)).re := by
  by_cases hw : w = 0
  · simp [hw]
  · exact ((Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hw)).1).le
theorem embComp_smul {K : Type} [Field K] [NumberField K] {i : ℕ} (σ : K →+* ℂ) (c : ℂ)
    (z : ProjIdx K i → ℂ) : embComp σ (c • z) = c • embComp σ z := by
  funext j
  simp only [embComp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring
open scoped Classical in

theorem sum_emb_embComp {K : Type} [Field K] [NumberField K] {i : ℕ} (z : ProjIdx K i → ℂ)
    (m : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (j : Fin i) :
    ∑ σ : K →+* ℂ, σ (integralBasis K m) * embComp σ z j = z (m, j) := by
  set b := canonicalEmbedding.latticeBasis K
  have hb : b m = ∑ σ : K →+* ℂ, σ (integralBasis K m) • (Pi.single σ 1 : (K →+* ℂ) → ℂ) := by
    funext τ
    simp [b, canonicalEmbedding.latticeBasis_apply, canonicalEmbedding.apply_at, Pi.single_apply]
  have hr : ∀ m' , (if m = m' then (1 : ℂ) else 0) =
      ∑ σ : K →+* ℂ, σ (integralBasis K m) * b.repr (Pi.single σ 1) m' := by
    intro m'
    have := congrArg (fun v => b.repr v m') hb
    simp only [Module.Basis.repr_self, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at this
    rw [← this, Finsupp.single_apply]
  have hs : ∀ m', ∑ σ : K →+* ℂ, σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) =
      (if m = m' then (1 : ℂ) else 0) * z (m', j) := by
    intro m'
    rw [hr m', Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by ring
  calc ∑ σ : K →+* ℂ, σ (integralBasis K m) * embComp σ z j
      = ∑ σ : K →+* ℂ, ∑ m', σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) := by
        simp only [embComp, Finset.mul_sum]; rfl
    _ = ∑ m', ∑ σ : K →+* ℂ, σ (integralBasis K m) * (b.repr (Pi.single σ 1) m' * z (m', j)) :=
        Finset.sum_comm
    _ = ∑ m', (if m = m' then (1 : ℂ) else 0) * z (m', j) := Finset.sum_congr rfl fun m' _ => hs m'
    _ = z (m, j) := by simp
def latticeLine {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) :
    HermLine (projBlocks K i) where
  a := fun _ => 1
  h z := Real.sqrt (latticeNormSq F fun q => z ⟨(), q⟩)
  pos z hz := by
    apply Real.sqrt_pos.mpr
    obtain ⟨⟨m, j⟩, hmj⟩ := hz ()
    have hσ : ∃ σ : K →+* ℂ, embComp σ (fun q => z ⟨(), q⟩) ≠ 0 := by
      by_contra h
      push Not at h
      apply hmj
      rw [← sum_emb_embComp (fun q => z ⟨(), q⟩) m j]
      simp [h]
    obtain ⟨σ, hσ⟩ := hσ
    have hpos : 0 < (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
        (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re :=
      (Complex.lt_def.mp ((F.posDef σ).dotProduct_mulVec_pos hσ)).1
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun σ =>
      (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re)
      (fun σ _ => latticeNormSq_term_nonneg F σ _) (Finset.mem_univ σ))
  smul c z hc := by
    have hz : (fun q => (fun p : Σ _ : Unit, ProjIdx K i => c p.1 * z p) ⟨(), q⟩) =
        c () • fun q => z ⟨(), q⟩ := by
      funext q; rfl
    simp only [hz, latticeNormSq, embComp_smul, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    have : ∀ σ : K →+* ℂ, (star (c () • embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
        (F.metric σ *ᵥ (c () • embComp σ fun q => z ⟨(), q⟩))).re =
        ‖c ()‖ ^ 2 * (star (embComp σ fun q => z ⟨(), q⟩) ⬝ᵥ
          (F.metric σ *ᵥ embComp σ fun q => z ⟨(), q⟩)).re := by
      intro σ
      rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul,
        Complex.normSq_eq_norm_sq]
    simp only [this, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
def LineOfLargeDegreeFromZ.Statement : Prop :=
  SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → LineOfLargeDegree.Statement
def ProjArithVar.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ), 1 ≤ i → IsArithVar (projSpaceIdeal K i) i
def LatticeLineSemipositive.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i),
    IsSemipositiveRel ⊥ (projSpaceIdeal K i) (latticeLine F)
def LatticeLineConj.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i),
    IsConjInvariantH (latticeLine F)
def PointLineDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (II : IntersectionSystem),
    IsIntersectionSystem II → ∀ W : Ideal (MRing (projBlocks K i)), IsArithVar W 1 →
      projSpaceIdeal K i ≤ W → 0 < degC W ∧
        ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
          v ≠ 0 ∧ F.lineDegree K' v = -II Unit (projBlocks K i) W 1 ![latticeLine F] / degC W
def TopLatticeBound.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i)
    (II : IntersectionSystem), 1 ≤ i → IsIntersectionSystem II →
    II Unit (projBlocks K i) (projSpaceIdeal K i) i (fun _ => latticeLine F) ≤
      (i : ℝ) * (-F.slope + 1 / 2 * Real.log i) *
        geomDeg (projSpaceIdeal K i) (latticeLine F) (i - 1)
def GeomDegPos.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i), 1 ≤ i →
    0 < geomDeg (projSpaceIdeal K i) (latticeLine F) (i - 1)
example : HermLine (projBlocks ℚ 2) := latticeLine (HermLattice.standard ℚ 2)
example : (latticeLine (HermLattice.standard ℚ 2)).a = fun _ => 1 := rfl
end
end GroundTheory.Heights₂.Heights


