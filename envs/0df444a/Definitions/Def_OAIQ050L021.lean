-- Prove2me | Definitions.Def_OAIQ050L021
-- name    : OAIQ050L021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:12:50.052032+00:00
-- url     : https://prove2.me/theorems/9d77f84e-0844-4bba-b572-e37cec3e0163
-- title:
--   Definitions bundle OAIQ050L021 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 13 definitions and 10 theorems. The definitions and types are `OAI.Laughlin.Spin.fourBodyInclusion`, `OAI.Laughlin.Spin.fourCoupledBasis`, `OAI.Laughlin.Spin.fourCoupledDeficit`, `OAI.Laughlin.Spin.fourPairEmbedding`, `OAI.Laughlin.Spin.fourPairTargetMatrix`, `OAI.Laughlin.Spin.pairBasisAction`, `OAI.Laughlin.Spin.phasedThreeDescendant`, `OAI.Laughlin.Spin.retainedFourIndex`, `OAI.Laughlin.Spin.retainedFourIndexEquiv`, `OAI.Laughlin.Spin.retainedFourReal`, `OAI.Laughlin.Spin.threeBodySpinRepresentation`, `OAI.Laughlin.Spin.threeCoupledInclusion`, `OAI.Laughlin.Spin.wedgePairMatrix`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_FourBody_CopyOrthogonality`, `Laughlin_FourBody_CoupledBasis`, `Laughlin_FourBody_RetainedIndex`, `Laughlin_FourBody_TargetResolution`, `Laughlin_FourBody_TraceReadout`, `Laughlin_Operators_WedgePairRepresentation`, `Laughlin_Operators_WedgePairRotation`, `Laughlin_Pair_CoupledBasis`, `Laughlin_Spin_Basic`, `Laughlin_Spin_Support`, `Laughlin_ThreeBody_GroupIntertwining`, `Laughlin_ThreeBody_HaarBlocks`, `Laughlin_ThreeBody_TraceReadout`.
--
--   **Imports.** It imports the bundles `OAIQ050L016`, `OAIQ050L017`, `OAIQ050L018` and `OAIQ050L019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L022` and `OAIQ050L023`; the statements `OAI_Laughlin_Fock_fourPairEmbedding_contract`, `OAI.Laughlin.Fock.fourPairEmbedding_contract_s50`, `OAI_Laughlin_Spin_fourCoupledBasis_complex_complete`, `OAI.Laughlin.Spin.fourCoupledBasis_complex_complete_s50`, `OAI_Laughlin_Spin_fourPairEmbedding_resolution`, `OAI.Laughlin.Spin.fourPairEmbedding_resolution_s50`, `OAI_Laughlin_Spin_physical_threeBody_certificate_haar`, `OAI.Laughlin.Spin.physical_threeBody_certificate_haar_s50`, `OAI_Laughlin_Spin_physical_threeBody_haar_normalization`, `OAI.Laughlin.Spin.physical_threeBody_haar_normalization_s50`, `OAI_Laughlin_Spin_retainedFourReal_outer_trace`, `OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50`, `OAI_Laughlin_Spin_threeBody_haar_diagonal_block`, `OAI.Laughlin.Spin.threeBody_haar_diagonal_block_s50`, `OAI_Laughlin_Spin_threeBody_haar_offdiagonal_block`, `OAI.Laughlin.Spin.threeBody_haar_offdiagonal_block_s50`, `OAI_Laughlin_Spin_threeCoupledInclusion_adjoint_SU2` and `OAI.Laughlin.Spin.threeCoupledInclusion_adjoint_SU2_s50`; the proofs of `OAI_Laughlin_Fock_physicalFourCopyEnd_column`, `OAI.Laughlin.Fock.physicalFourCopyEnd_column_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_comparison_eventually`, `OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually_s50`, `OAI_Laughlin_Fock_physical_threeBody_Fock_haar_real`, `OAI.Laughlin.Fock.physical_threeBody_Fock_haar_real_s50`, `OAI_Laughlin_Fock_sourceA4Form_bessel_bound`, `OAI.Laughlin.Fock.sourceA4Form_bessel_bound_s50`, `OAI_Laughlin_Spin_physicalFourBodyMatrix_high_wedge_copy`, `OAI.Laughlin.Spin.physicalFourBodyMatrix_high_wedge_copy_s50`, `OAI_Laughlin_Spin_physical_threeBody_certificate_haar`, `OAI.Laughlin.Spin.physical_threeBody_certificate_haar_s50`, `OAI_Laughlin_Spin_physical_threeBody_haar_normalization`, `OAI.Laughlin.Spin.physical_threeBody_haar_normalization_s50`, `OAI_Laughlin_Spin_retainedFourReal_outer_trace` and `OAI.Laughlin.Spin.retainedFourReal_outer_trace_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ050L016
import Definitions.Def_OAIQ050L017
import Definitions.Def_OAIQ050L018
import Definitions.Def_OAIQ050L019

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericUnitDescendant_zero (A B z : ℕ) (hA : z ≤ A) (hB : z ≤ B) :
    genericUnitDescendant A B z hA hB 0 = genericHighest A B z hA hB := by
  simp [genericUnitDescendant,genericDescendant,genericHighest_norm]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericDescendant_off (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (i : SpinIndex A B) (hi : i.1.val+i.2.val ≠ z+n) :
    genericDescendant A B z hA hB n i = 0 := by
  induction n generalizing i with
  | zero =>
    simpa [genericDescendant,genericHighest] using
      extendWeightSlice_off A B z hA hB (fun p => highestUnit A B z p.val) i (by omega)
  | succ n ih =>
    rw [genericDescendant_succ]
    change (∑ j, totalRaise A B j i * genericDescendant A B z hA hB n j) = 0
    rw [totalRaise_transpose_apply,raiseMatrix_column,raiseMatrix_column]
    have h1 : (if h : 0 < i.1.val then
        genericDescendant A B z hA hB n (⟨i.1.val-1,by omega⟩,i.2) * ladder A (i.1.val-1) else 0) = 0 := by
      split_ifs with h
      · rw [ih _ (by dsimp; omega),zero_mul]
      · rfl
    have h2 : (if h : 0 < i.2.val then
        genericDescendant A B z hA hB n (i.1,⟨i.2.val-1,by omega⟩) * ladder B (i.2.val-1) else 0) = 0 := by
      split_ifs with h
      · rw [ih _ (by dsimp; omega),zero_mul]
      · rfl
    rw [h1,h2,add_zero]

theorem genericUnitDescendant_off (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (i : SpinIndex A B) (hi : i.1.val+i.2.val ≠ z+n) :
    genericUnitDescendant A B z hA hB n i = 0 := by
  simp only [genericUnitDescendant,Pi.smul_apply,smul_eq_mul,genericDescendant_off A B z n hA hB i hi,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CopyOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def fourBodyInclusion (Q r D : ℕ) (hr : r ≤ Q)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q)
      (Fin (genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r)+1)) ℝ :=
  tensorPairInclusion (2*Q-2) Q r hr *
    ((-1 : ℝ)^(D-r) • genericCoupledInclusion (2*Q-2) (genericCoupledWeight Q Q r) (D-r) hA hB)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem wedgePairIndex_card_real (Q : ℕ) :
    (Fintype.card (WedgePairIndex Q) : ℝ) = (Q : ℝ)*(Q+1)/2 := by
  rw [Fintype.card_congr (wedgePairEquiv Q)]
  simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [fin_sum_values]
  push_cast
  ring

theorem pairCoupledIndex_card (Q : ℕ) :
    Fintype.card (PairCoupledIndex Q) = Fintype.card (WedgePairIndex Q) := by
  have h : (Fintype.card (PairCoupledIndex Q) : ℝ) = (Fintype.card (WedgePairIndex Q) : ℝ) := by
    rw [wedgePairIndex_card_real]
    simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
    have hc (r : OddPairLabel Q) :
        ((genericCoupledWeight Q Q (oddPairDeficit r)+1 : ℕ) : ℝ) =
          2*(Q : ℝ)-1-4*(r.val : ℝ) := by
      have hr := oddPairDeficit_le r
      unfold genericCoupledWeight
      rw [Nat.cast_add,Nat.cast_sub (by omega : 2*oddPairDeficit r ≤ Q+Q)]
      simp only [oddPairDeficit,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      ring
    simp_rw [hc]
    rw [Finset.sum_sub_distrib,Finset.sum_const,← Finset.mul_sum,fin_sum_values]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hp : Q+1=2*((Q+1)/2) ∨ Q=2*((Q+1)/2) := by omega
    rcases hp with hp | hp
    · have he : (Q : ℝ)+1=2*(((Q+1)/2 : ℕ) : ℝ) := by exact_mod_cast hp
      nlinarith
    · have he : (Q : ℝ)=2*(((Q+1)/2 : ℕ) : ℝ) := by exact_mod_cast hp
      nlinarith
  exact_mod_cast h

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_CoupledBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def fourCoupledBasis (Q : ℕ) :
    Matrix (Fin (2*Q-2+1) × WedgePairIndex Q) (FourCoupledIndex Q) ℝ :=
  fun i s => fourBodyCopy Q (oddPairDeficit s.1) (oddPairDeficit s.1+s.2.1.val)
    (oddPairDeficit_le s.1) (by have := s.2.1.isLt; omega)
    (by have := s.2.1.isLt; omega) s.2.2.val i

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WedgePairRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix Kronecker

noncomputable def wedgePairMatrix (Q : ℕ) (g : SourceSU2) :
    Matrix (WedgePairIndex Q) (WedgePairIndex Q) ℂ := fun i j =>
  sourceSpinRepresentation Q g i.val.1 j.val.1 * sourceSpinRepresentation Q g i.val.2 j.val.2 -
    sourceSpinRepresentation Q g i.val.1 j.val.2 * sourceSpinRepresentation Q g i.val.2 j.val.1

theorem wedgePairMatrix_tensor (Q : ℕ) (g : SourceSU2) (f : SpinIndex Q Q → ℂ)
    (hf : ∀ i j, f (j,i) = -f (i,j)) (i : WedgePairIndex Q) :
    (wedgePairMatrix Q g *ᵥ (fun j => (Real.sqrt 2 : ℂ)*f j.val)) i =
      (Real.sqrt 2 : ℂ) *
        ((sourceSpinRepresentation Q g ⊗ₖ sourceSpinRepresentation Q g) *ᵥ f) i.val := by
  have h := antisymmetric_ordered_sum Q f
    (fun j => sourceSpinRepresentation Q g i.val.1 j.1 * sourceSpinRepresentation Q g i.val.2 j.2) hf
  simp only [Matrix.mulVec,dotProduct,Matrix.kroneckerMap,Matrix.of_apply]
  conv_rhs => rw [show (∑ j : SpinIndex Q Q,
    sourceSpinRepresentation Q g i.val.1 j.1 * sourceSpinRepresentation Q g i.val.2 j.2 * f j) =
    ∑ j : SpinIndex Q Q, f j*(sourceSpinRepresentation Q g i.val.1 j.1 *
      sourceSpinRepresentation Q g i.val.2 j.2) by apply Finset.sum_congr rfl; intro j hj; ring]
  rw [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [wedgePairMatrix]
  ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_WedgePairRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open Rotation
open scoped BigOperators Matrix

noncomputable def pairBasisAction (Q : ℕ) (g : SourceSU2) :
    Matrix (PairCoupledIndex Q) (PairCoupledIndex Q) ℂ :=
  Matrix.blockDiagonal' (fun r : OddPairLabel Q =>
    sourceSpinRepresentation (genericCoupledWeight Q Q (oddPairDeficit r)) g)

theorem pairBasisAction_one (Q : ℕ) : pairBasisAction Q 1=1 := by
  simp only [pairBasisAction,map_one]
  exact Matrix.blockDiagonal'_one

theorem pairBasisAction_mul (Q : ℕ) (g h : SourceSU2) :
    pairBasisAction Q (g*h) = pairBasisAction Q g * pairBasisAction Q h := by
  simp only [pairBasisAction,map_mul,Matrix.blockDiagonal'_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RetainedIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

def fourCoupledDeficit {Q : ℕ} (s : FourCoupledIndex Q) : ℕ :=
  oddPairDeficit s.1+s.2.1.val

def retainedFourIndex (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (n : Fin (fourSpinWeight Q D+1)) : FourCoupledIndex Q :=
  ⟨⟨r.val, by have := r.isLt; omega⟩,
    ⟨⟨D-oddPairDeficit r, by
      have := oddPairDeficit_le r
      dsimp [genericCoupledWeight,oddPairDeficit] at *
      omega⟩,
      ⟨n.val, by
        have h := four_nested_weight Q D (oddPairDeficit r) hQ (oddPairDeficit_le r)
        change n.val < genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q (oddPairDeficit r)) (D-oddPairDeficit r)+1
        rw [h]
        exact n.isLt⟩⟩⟩

theorem retainedFourIndex_deficit (Q D : ℕ) (hQ : D+2 ≤ Q)
    (r : OddPairLabel D) (n : Fin (fourSpinWeight Q D+1)) :
    fourCoupledDeficit (retainedFourIndex Q D hQ r n) = D := by
  dsimp [fourCoupledDeficit,retainedFourIndex]
  have := oddPairDeficit_le r
  dsimp [oddPairDeficit] at *
  omega

def retainedFourIndexEquiv (Q D : ℕ) (hQ : D+2 ≤ Q) :
    (OddPairLabel D × Fin (fourSpinWeight Q D+1)) ≃
      {s : FourCoupledIndex Q // fourCoupledDeficit s = D} where
  toFun x := ⟨retainedFourIndex Q D hQ x.1 x.2,retainedFourIndex_deficit Q D hQ x.1 x.2⟩
  invFun s :=
    (⟨s.val.1.val, by have := s.property; dsimp [fourCoupledDeficit,oddPairDeficit] at *; omega⟩,
     ⟨s.val.2.2.val, by
       have hd := s.property
       have hw := four_nested_weight Q D (oddPairDeficit s.val.1) hQ
         (by dsimp [fourCoupledDeficit] at hd; omega)
       have hz : D-oddPairDeficit s.val.1=s.val.2.1.val := by
         dsimp [fourCoupledDeficit] at hd; omega
       rw [hz] at hw
       rw [← hw]
       exact s.val.2.2.isLt⟩)
  left_inv x := by apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv s := by
    apply Subtype.ext
    rcases s with ⟨⟨r,⟨z,n⟩⟩,hd⟩
    dsimp [fourCoupledDeficit] at hd
    have hz : D-oddPairDeficit r=z.val := by omega
    dsimp [retainedFourIndex]
    congr 2
    · exact Fin.ext hz
    · apply (Fin.heq_ext_iff (by congr 2)).mpr
      rfl

theorem fourCoupledDeficit_pos {Q : ℕ} (s : FourCoupledIndex Q) :
    1 ≤ fourCoupledDeficit s := by dsimp [fourCoupledDeficit,oddPairDeficit]; omega

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TargetResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def fourPairEmbedding (Q r : ℕ) (hr : r ≤ Q) :
    Matrix (FourWedgeIndex Q) (SpinIndex (2*Q-2) (genericCoupledWeight Q Q r)) ℂ :=
  (1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ) ⊗ₖ
    (pairCoupledInclusion Q r hr).map Complex.ofReal

noncomputable def fourPairTargetMatrix (Q : ℕ) (hQ : 1 ≤ Q) :
    Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ :=
  fourPairEmbedding Q 1 hQ*(fourPairEmbedding Q 1 hQ)ᴴ

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def retainedFourReal (Q D : ℕ) (hQ : D+2 ≤ Q) (r : OddPairLabel D) :
    Matrix (FourWedgeIndex Q) (Fin (fourSpinWeight Q D+1)) ℝ :=
  fun i n => fourBodyCopy Q (oddPairDeficit r) D
    (by have := oddPairDeficit_le r; omega)
    (by have := oddPairDeficit_le r; omega)
    (by have := oddPairDeficit_le r; unfold genericCoupledWeight; omega) n.val i

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_GroupIntertwining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

noncomputable def threeCoupledInclusion (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    Matrix (PairOrbitalIndex Q) (Fin (coupledWeight Q z.val+1)) ℂ :=
  fun i n => (normalizedCoupledDescendant Q z.val hQ (by omega) n.val i : ℂ)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_HaarBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker
open Rotation MeasureTheory

noncomputable def threeBodySpinRepresentation (Q : ℕ) :
    SourceSU2 →* Matrix (PairOrbitalIndex Q) (PairOrbitalIndex Q) ℂ where
  toFun g := sourceSpinRepresentation (2*Q-2) g ⊗ₖ sourceSpinRepresentation Q g
  map_one' := by simp only [map_one,Matrix.one_kronecker_one]
  map_mul' g h := by simp only [map_mul,Matrix.mul_kronecker_mul]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def phasedThreeDescendant (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) (n : ℕ) :
    PairOrbitalIndex Q → ℝ :=
  (-1 : ℝ)^z.val • normalizedCoupledDescendant Q z.val hQ (by omega) n

end Laughlin.Spin

end OAI
end


