-- Prove2me | Definitions.Def_OAIQ084L043
-- name    : OAIQ084L043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:40:41.363535+00:00
-- url     : https://prove2.me/theorems/857f3bfd-bd13-442f-ba49-0ffae43292a0
-- title:
--   Definitions bundle OAIQ084L043 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinFock.thm_fock`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 19 definitions. The definitions and types are `OAI.LaughlinFock.fourSpinColumns`, `OAI.LaughlinFock.fourSpinWedge`, `OAI.LaughlinFock.fullCouplingMatrix`, `OAI.LaughlinFock.integerCompression`, `OAI.LaughlinFock.integerFourGram`, `OAI.LaughlinFock.integerFourMiddle`, `OAI.LaughlinFock.integerRowsFourTrace`, `OAI.LaughlinFock.normalizedPairGrid`, `OAI.LaughlinFock.oddPairSpinMatrix`, `OAI.LaughlinFock.pairSwapCompression`, `OAI.LaughlinFock.pairTensorEmbed`, `OAI.LaughlinFock.pairTensorProject`, `OAI.LaughlinFock.rationalFourGram`, `OAI.LaughlinFock.rawPairGrid`, `OAI.LaughlinFock.retainedFourTarget`, `OAI.LaughlinFock.tailThreeTarget`, `OAI.LaughlinFock.threeSpinColumns`, `OAI.LaughlinFock.threeSpinWedge`, `OAI.LaughlinFock.threeTraceForm`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinFock_FiniteComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/FiniteComparison.lean), [`LaughlinFock_FourBasis`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/FourBasis.lean), [`LaughlinFock_FourCopies`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/FourCopies.lean), [`LaughlinFock_FourLie`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/FourLie.lean), [`LaughlinFock_IntegerFour`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/IntegerFour.lean), [`LaughlinFock_PairDecomposition`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/PairDecomposition.lean), [`LaughlinFock_PairIdentification`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/PairIdentification.lean), [`LaughlinFock_RationalWedge`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/RationalWedge.lean), [`LaughlinFock_SquareSplitting`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/SquareSplitting.lean), [`LaughlinFock_SwapCompression`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/SwapCompression.lean), [`LaughlinFock_ThreeOrbit`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/LaughlinFock/ThreeOrbit.lean).
--
--   **Imports.** It imports the published bundle `Def_LaughlinFock`; the bundles `OAIQ084L022`, `OAIQ084L023`, `OAIQ084L024` and `OAIQ084L028` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.LaughlinFock.fourYChecked_10`, `OAI.LaughlinFock.fourYChecked_11`, `OAI.LaughlinFock.fourYChecked_12`, `OAI.LaughlinFock.fourYChecked_13`, `OAI.LaughlinFock.fourYChecked_14`, `OAI.LaughlinFock.fourYChecked_16`, `OAI.LaughlinFock.fourYChecked_17`, `OAI.LaughlinFock.fourYChecked_19`, `OAI_LaughlinFock_fourYChecked_20`, `OAI_LaughlinFock_fourYChecked_21`, `OAI_LaughlinFock_fourYChecked_22`, `OAI.LaughlinFock.fourYChecked_23`, `OAI.LaughlinFock.fourYChecked_5`, `OAI.LaughlinFock.fourYChecked_7`, `OAI.LaughlinFock.fourYChecked_8`, `OAI.LaughlinFock.fourYLower_15`, `OAI.LaughlinFock.fourYLower_9`, `OAI.LaughlinFock.integerRowsFourTrace_collected`, `OAI.LaughlinFock.integerRowsFourTrace_parts`, `OAI.LaughlinFock.integer_certificate_10`, `OAI.LaughlinFock.integer_certificate_11`, `OAI.LaughlinFock.integer_certificate_12`, `OAI.LaughlinFock.integer_certificate_13`, `OAI.LaughlinFock.integer_certificate_14`, `OAI.LaughlinFock.integer_certificate_15`, `OAI.LaughlinFock.integer_certificate_16`, `OAI.LaughlinFock.integer_certificate_17`, `OAI.LaughlinFock.integer_certificate_18`, `OAI.LaughlinFock.integer_certificate_19`, `OAI.LaughlinFock.integer_certificate_20`, `OAI.LaughlinFock.integer_certificate_21`, `OAI.LaughlinFock.integer_certificate_22`, `OAI.LaughlinFock.integer_certificate_23`, `OAI.LaughlinFock.integer_certificate_8` and `OAI.LaughlinFock.integer_certificate_9`; the proofs of `OAI.LaughlinFock.averagedRowsFour_eventual_bound`, `OAI.LaughlinFock.certificate_four`, `OAI.LaughlinFock.fockInequality_eventual_of_certificates`, `OAI.LaughlinFock.fourYChecked_10`, `OAI.LaughlinFock.fourYChecked_11`, `OAI.LaughlinFock.fourYChecked_12`, `OAI.LaughlinFock.fourYChecked_13`, `OAI.LaughlinFock.fourYChecked_14`, `OAI.LaughlinFock.fourYChecked_16`, `OAI.LaughlinFock.fourYChecked_17`, `OAI.LaughlinFock.fourYChecked_19`, `OAI_LaughlinFock_fourYChecked_20`, `OAI_LaughlinFock_fourYChecked_21`, `OAI_LaughlinFock_fourYChecked_22`, `OAI.LaughlinFock.fourYChecked_23`, `OAI.LaughlinFock.fourYChecked_5`, `OAI.LaughlinFock.fourYChecked_7`, `OAI.LaughlinFock.fourYChecked_8`, `OAI.LaughlinFock.fourYLower_15`, `OAI.LaughlinFock.fourYLower_9`, `OAI.LaughlinFock.integerRowsFourTrace_collected`, `OAI.LaughlinFock.integerRowsFourTrace_parts`, `OAI.LaughlinFock.integer_certificate_10`, `OAI.LaughlinFock.integer_certificate_11`, `OAI.LaughlinFock.integer_certificate_12`, `OAI.LaughlinFock.integer_certificate_13`, `OAI.LaughlinFock.integer_certificate_14`, `OAI.LaughlinFock.integer_certificate_15`, `OAI.LaughlinFock.integer_certificate_16`, `OAI.LaughlinFock.integer_certificate_17`, `OAI.LaughlinFock.integer_certificate_18`, `OAI.LaughlinFock.integer_certificate_19`, `OAI.LaughlinFock.integer_certificate_20`, `OAI.LaughlinFock.integer_certificate_21`, `OAI.LaughlinFock.integer_certificate_22`, `OAI.LaughlinFock.integer_certificate_23`, `OAI.LaughlinFock.integer_certificate_8` and `OAI.LaughlinFock.integer_certificate_9`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_LaughlinFock
import Definitions.Def_OAIQ084L022
import Definitions.Def_OAIQ084L023
import Definitions.Def_OAIQ084L024
import Definitions.Def_OAIQ084L028

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairIdentification
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Identification. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators



def rawPairGrid (Q p : ℕ) : GridVector := fun i j =>
  if i+j=p+1 then
    ((i:ℝ)-j) * Real.sqrt (Q.choose i : ℝ) * Real.sqrt (Q.choose j : ℝ)
  else 0


def normalizedPairGrid (Q p : ℕ) : GridVector :=
  (pairTensorNormalizer Q p)⁻¹ • rawPairGrid Q p

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SwapCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Swap Compression. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators



def pairTensorEmbed (Q : ℕ) : GridVector →ₗ[ℝ] CubeVector where
  toFun f i j k := ∑ p ∈ Finset.range (2*Q-2+1), coupledVector Q Q 1 p i j * f p k
  map_add' f g := by
    funext i j k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext i j k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring

 

def pairTensorProject (Q : ℕ) : CubeVector →ₗ[ℝ] GridVector where
  toFun f p k := gridInner Q Q (coupledVector Q Q 1 p) (fun i j => f i j k)
  map_add' f g := by
    funext p k
    simp only [gridInner, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext p k
    simp only [gridInner, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring


def pairSwapCompression (Q : ℕ) : GridVector →ₗ[ℝ] GridVector :=
  (pairTensorProject Q).comp (swap23.comp (pairTensorEmbed Q))

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FiniteComparison
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Comparison. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



def threeTraceForm {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow) (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.range 16, (rowsThreeTrace rows Q z / spinRatio Q z : ℂ) •
      threeSpinProjection Q z) * (threeWedgeMatrix Q)ᴴ)


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fullCouplingMatrix (n m : ℕ) :
    Matrix (Fin (n+1) × Fin (m+1)) (CoupledIndex n m) ℂ :=
  fun b c => coupledVector n m c.1.val c.2.val b.1.val b.2.val

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_PairDecomposition
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Decomposition. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder



def retainedFourTarget (Q L : ℕ) : Matrix (SectorOccupation Q 4) (SectorOccupation Q 4) ℂ :=
  fourCoupledWedgeMatrix Q * Matrix.diagonal
    (fun c : CoupledIndex (2*Q-2) (2*Q-2) => if c.1.val+1 ≤ L then (1 : ℂ) else 0) *
      (fourCoupledWedgeMatrix Q)ᴴ

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourLie
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def oddPairSpinMatrix (Q r : ℕ) :
    Matrix (SectorOccupation Q 2) (Fin (2*Q-2*r+1)) ℂ :=
  fun S k => wedgeCoupledCoefficient Q r k.val ((increasingPairEquiv Q).symm S)


def fourSpinWedge (Q r z : ℕ) :
    Matrix (SectorOccupation Q 4) (Fin ((2*Q-2)+(2*Q-2*r)-2*z+1)) ℂ :=
  fun S k => composedFourWedgeColumn Q r z k.val S


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_FourCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Copies. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



def fourSpinColumns (Q : ℕ) (b : FourSpinIndex Q) :
    Matrix (FourUncoupled Q)
      (Fin ((2*Q-2)+(2*Q-2*b.1.val.val)-2*b.2.val+1)) ℂ :=
  fun x k => (composedCoupledVector Q b.1.val.val b.2.val k.val x : ℂ)


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RationalWedge
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Wedge. -/

noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder


def rationalFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A : SectorOccupation 24 4,
    2 * rationalHighestEntry D r A.val * rationalHighestEntry D s A.val /
      (2^(2*D) * occupationFactorial A.val)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_IntegerFour
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def integerRowsFourTrace (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  ∑ t : Fin 8, integerFourTrace D t.val (certificateAlpha t)

def integerFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A ∈ highestFourOccupations D,
    2 * integerHighestEntry D r A * integerHighestEntry D s A /
      (2^(2*D) * occupationFactorial A)



def integerFourMiddle (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  Matrix.diagonal (fun r => ((if r.val.val=1 then 2 else 0)+3/10^6) *
    rationalCopyDiagonal D r.val.val) -
    Matrix.diagonal (fun r : CopyLabel D => rationalCopyDiagonal D r.val.val) *
      integerRowsFourTrace D * Matrix.diagonal (fun r : CopyLabel D => rationalCopyDiagonal D r.val.val)

def integerCompression (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  integerFourGram D * integerFourMiddle D * integerFourGram D

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_SquareSplitting
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Splitting. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 

def tailThreeTarget (Q : ℕ) : FockMatrix Q :=
  exteriorLift Q 3 (threeWedgeMatrix Q *
    (∑ z ∈ Finset.Ico 16 (Q+1), (gramShift Q z : ℂ) • threeSpinProjection Q z) *
      (threeWedgeMatrix Q)ᴴ)


end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_ThreeOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def threeSpinColumns (Q z : ℕ) :
    Matrix (PairLabel Q × Orbital Q) (Fin (2*Q-2+Q-2*z+1)) ℂ :=
  fun pj k => threeCoupledColumn Q z k.val pj



def threeSpinWedge (Q z : ℕ) :
    Matrix (SectorOccupation Q 3) (Fin (2*Q-2+Q-2*z+1)) ℂ :=
  threeWedgeMatrix Q * threeSpinColumns Q z



end LaughlinFock
end

end OAI
end


