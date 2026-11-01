-- Prove2me | Definitions.Def_OAIQ050L008
-- name    : OAIQ050L008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:07:51.672324+00:00
-- url     : https://prove2.me/theorems/87c92cf7-f4a6-4a34-856e-421a99725eae
-- title:
--   Definitions bundle OAIQ050L008 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 23 definitions and 13 theorems. The definitions and types are `OAI.Laughlin.Rotation.rectangularIntegral`, `OAI.Laughlin.Rotation.rectangularOrbit`, `OAI.Laughlin.Rotation.spinBinomialWeight`, `OAI.Laughlin.Rotation.spinSeparatingRoot`, `OAI.Laughlin.Rotation.upperSpinCurve`, `OAI.Laughlin.Spin.EmbeddedLocalFourIndex`, `OAI.Laughlin.Spin.alphaRadical`, `OAI.Laughlin.Spin.fourBodyRadical`, `OAI.Laughlin.Spin.oscillatorArray`, `OAI.Laughlin.Spin.oscillatorHighest`, `OAI.Laughlin.Spin.oscillatorRelative`, `OAI.Laughlin.Spin.oscillatorRelativeNorm`, `OAI.Laughlin.Spin.sourceYFactor`, `OAI.Laughlin.Spin.threeBodyDimensionRatio`, `OAI.Laughlin.Spin.threeBodyRadical`, `OAI.Laughlin.Spin.weightMatrix`, `OAI.Laughlin.deltaFormula`, `OAI.Laughlin.deltaTerm`, `OAI.Laughlin.fallingRatio`, `OAI.Laughlin.gramEigenvalueFormula`, `OAI.Laughlin.pairNormalization`, `OAI.Laughlin.raisePair`, `OAI.Laughlin.tailWeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `Laughlin_Asymptotics_Bound`, `Laughlin_Asymptotics_Convergence`, `Laughlin_Asymptotics_UpperSpinCurve`, `Laughlin_FourBody_RadicalCancellation`, `Laughlin_FourBody_RadicalCoefficient`, `Laughlin_Operators_LocalFourIndexEquiv`, `Laughlin_Operators_WedgePairRepresentation`, `Laughlin_Pair_CoupledParity`, `Laughlin_Pair_NormalizedLadder`, `Laughlin_Pair_PolynomialRaising`, `Laughlin_Spin_ArrayLimit`, `Laughlin_Spin_Basis`, `Laughlin_Spin_BinomialWeights`, `Laughlin_Spin_Highest2`, `Laughlin_Spin_OscillatorHighest`, `Laughlin_Spin_OscillatorHighestNormalization`, `Laughlin_Spin_RectangularAverage`, `Laughlin_Spin_Schur`, `Laughlin_Spin_Sl2DescendantNorm`, `Laughlin_Spin_Sl2Matrix`, `Laughlin_Spin_Sl2Orthogonal`, `Laughlin_ThreeBody_Radical`, `Laughlin_ThreeBody_TraceComparison`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ050L013`, `OAIQ050L014` and `OAIQ050L015`; the statements `OAI_Laughlin_Fock_complexThreeGram_sub_one_spectral`, `OAI.Laughlin.Fock.complexThreeGram_sub_one_spectral_s50`, `OAI_Laughlin_Fock_physical_threeBody_budget_eventually`, `OAI_Laughlin_Fock_physical_threeBody_tail_sum`, `OAI_Laughlin_Rotation_source_unequal_spin_haar_zero`, `OAI.Laughlin.Rotation.source_unequal_spin_haar_zero_s50`, `OAI_Laughlin_Spin_coupledBasis_eigen`, `OAI_Laughlin_Spin_normalizedCoupledDescendant_eigen`, `OAI.Laughlin.Spin.normalizedCoupledDescendant_eigen_s50`, `OAI_Laughlin_Spin_oscillatorArray_polynomial`, `OAI.Laughlin.Spin.oscillatorArray_polynomial_s50`, `OAI_Laughlin_Spin_source_fourBody_radical_coefficient`, `OAI_Laughlin_Spin_source_highest_coupling_tendsto`, `OAI.Laughlin.Spin.source_highest_coupling_tendsto_s50`, `OAI_Laughlin_deltaTerm_tendsto`, `OAI.Laughlin.deltaTerm_tendsto_s50`, `OAI_Laughlin_sharp_scalar_budget` and `OAI.Laughlin.sharp_scalar_budget_s50`; the proofs of `OAI_Laughlin_Fock_finiteFourMiddle_tendsto`, `OAI_Laughlin_Fock_fockInclusion_normSq`, `OAI.Laughlin.Fock.fockInclusion_normSq_s50`, `OAI_Laughlin_Fock_physicalLimitError_eq`, `OAI_Laughlin_Fock_physicalLimitGram_eq`, `OAI.Laughlin.Fock.physicalLimitGram_eq_s50`, `OAI_Laughlin_Fock_physicalWedgeColumns_gram`, `OAI.Laughlin.Fock.physicalWedgeColumns_gram_s50`, `OAI_Laughlin_Fock_physical_threeBody_budget_eventually`, `OAI_Laughlin_Fock_physical_threeBody_tail_sum`, `OAI_Laughlin_Fock_sourceFockEnergy_fockInclusion`, `OAI.Laughlin.Fock.sourceFockEnergy_fockInclusion_s50`, `OAI_Laughlin_Fock_sourceFockHamiltonian_fockInclusion`, `OAI.Laughlin.Fock.sourceFockHamiltonian_fockInclusion_s50`, `OAI_Laughlin_Spin_coupledBasis_eigen`, `OAI_Laughlin_Spin_oscillatorArray_polynomial`, `OAI.Laughlin.Spin.oscillatorArray_polynomial_s50`, `OAI_Laughlin_Spin_source_fourBody_error_matrix`, `OAI.Laughlin.Spin.source_fourBody_error_matrix_s50`, `OAI_Laughlin_Spin_source_fourBody_radical_coefficient`, `OAI_Laughlin_deltaTerm_tendsto`, `OAI.Laughlin.deltaTerm_tendsto_s50`, `OAI_Laughlin_sharp_scalar_budget` and `OAI.Laughlin.sharp_scalar_budget_s50`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ050_Laughlin.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Bound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
noncomputable section
open scoped BigOperators

def fallingRatio (Q z : ℕ) : ℝ :=
  (Q.descFactorial z : ℝ) / ((2*Q-2).descFactorial z : ℝ)

def gramEigenvalueFormula (Q z : ℕ) : ℝ :=
  (-1 : ℝ)^z * fallingRatio Q z *
    (3*(z : ℝ)-1-(z : ℝ)*((z : ℝ)+1)/(Q : ℝ))

def tailWeight (Q z : ℕ) : ℝ :=
  ((3*(Q : ℝ)-1-2*(z : ℝ))/(2*(Q : ℝ)-1)) *
    |gramEigenvalueFormula Q z| * ((z : ℝ)+1)

end
end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_Convergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin
open scoped BigOperators Topology
open Filter
noncomputable section

def deltaTerm (Q m : ℕ) : ℝ :=
  if 17+2*m ≤ Q then tailWeight Q (17+2*m) else 0

def deltaFormula (Q : ℕ) : ℝ := ∑' m, deltaTerm Q m

end
end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Highest2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem choose_step_real (A p : ℕ) (hp : p ≤ A) :
    ((p : ℝ)+1)*(A.choose (p+1) : ℝ) =
      (A-p : ℕ)*(A.choose p : ℝ) := by
  have h := Nat.choose_succ_right_eq A p
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hp,mul_comm] using
    congrArg (fun n : ℕ => (n : ℝ)) h

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_BinomialWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators

noncomputable def spinBinomialWeight (Q : ℕ) (p : Fin (Q+1)) : ℂ :=
  (Real.sqrt (Q.choose p.val : ℝ) : ℂ)

theorem spinBinomialWeight_ne_zero (Q : ℕ) (p : Fin (Q+1)) : spinBinomialWeight Q p ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ p.isLt)

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Asymptotics_UpperSpinCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open Polynomial
open scoped BigOperators Matrix

noncomputable def upperSpinCurve (Q : ℕ) :
    Matrix (Fin (Q+1)) (Fin (Q+1)) (Polynomial ℂ) := fun p q =>
  monomial (q.val-p.val) (spinBinomialWeight Q q / spinBinomialWeight Q p *
    (q.val.choose p.val : ℂ))

theorem upperSpinCurve_derivative_zero (Q : ℕ) (p : Fin (Q+1)) :
    (upperSpinCurve Q p 0).derivative = 0 := by
  simp [upperSpinCurve]

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sl2DescendantNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem matrix_transpose_pairing (L : Matrix I I ℝ) (v w : I → ℝ) :
    (∑ i, (L *ᵥ v) i*w i) = ∑ i, v i*((Lᵀ) *ᵥ w) i := by
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem descendant_weight (H L : Matrix I I ℝ) (v : I → ℝ) (μ : ℝ)
    (hHL : H*L=L*H-(2 : ℝ) • L) (hv : H *ᵥ v=μ • v) (n : ℕ) :
    H *ᵥ (L^n *ᵥ v) = (μ-2*(n : ℝ)) • (L^n *ᵥ v) := by
  have hs (n : ℕ) : L^(n+1) *ᵥ v = L *ᵥ (L^n *ᵥ v) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [hs,Matrix.mulVec_mulVec,hHL,Matrix.sub_mulVec,Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec,ih,Matrix.mulVec_smul]
    funext i
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem descendant_raising (R H L : Matrix I I ℝ) (v : I → ℝ) (μ : ℝ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L)
    (hv : H *ᵥ v=μ • v) (hr : R *ᵥ v=0) (n : ℕ) :
    R *ᵥ (L^(n+1) *ᵥ v) = (((n : ℝ)+1)*(μ-n)) • (L^n *ᵥ v) := by
  have hs (n : ℕ) : L^(n+1) *ᵥ v = L *ᵥ (L^n *ᵥ v) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  induction n with
  | zero =>
    simp only [pow_one,pow_zero,Matrix.one_mulVec,Nat.cast_zero,zero_add,sub_zero,one_mul]
    rw [Matrix.mulVec_mulVec,hRL,Matrix.add_mulVec,← Matrix.mulVec_mulVec,hr,
      Matrix.mulVec_zero,zero_add,hv]
  | succ n ih =>
    rw [hs (n+1),Matrix.mulVec_mulVec,hRL,Matrix.add_mulVec,← Matrix.mulVec_mulVec,
      ih,Matrix.mulVec_smul,descendant_weight H L v μ hHL hv (n+1),hs n]
    funext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one]
    ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sl2Matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

noncomputable def weightMatrix (A : ℕ) : Matrix (Fin (A+1)) (Fin (A+1)) ℝ :=
  Matrix.diagonal (fun i => (A : ℝ)-2*i.val)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_NormalizedLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

noncomputable def pairNormalization (Q p : ℕ) : ℝ :=
  Real.sqrt (2*(Q : ℝ)*((2*Q-2).choose p : ℝ))

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_PolynomialRaising
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

noncomputable def raisePair (f : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ((i : ℝ)+1)*f (i+1) j + ((j : ℝ)+1)*f i (j+1)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_CoupledParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem sign_reverse (r p : ℕ) (hp : p ≤ r) :
    (-1 : ℝ)^(r-p) = (-1 : ℝ)^r * (-1 : ℝ)^p := by
  have h : (-1 : ℝ)^p * (-1 : ℝ)^p = 1 := by
    rw [← mul_pow]; norm_num
  calc
    _ = (-1 : ℝ)^(r-p) * ((-1 : ℝ)^p * (-1 : ℝ)^p) := by rw [h,mul_one]
    _ = _ := by rw [← mul_assoc,← pow_add,Nat.sub_add_cancel hp]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Sl2Orthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem descendants_orthogonal (R H L : Matrix I I ℝ) (v w : I → ℝ) (ν : ℝ)
    (hRL : R*L=L*R+H) (hHL : H*L=L*H-(2 : ℝ) • L) (ht : Lᵀ=R)
    (hw : H *ᵥ w=ν • w) (hvR : R *ᵥ v=0) (hwR : R *ᵥ w=0)
    (n m : ℕ) (h : (∑ i, v i*w i)=0 ∨ n ≠ m) :
    (∑ i, (L^n *ᵥ v) i*(L^m *ᵥ w) i) = 0 := by
  have hs (k : ℕ) (u : I → ℝ) : L^(k+1) *ᵥ u = L *ᵥ (L^k *ᵥ u) := by
    rw [Matrix.mulVec_mulVec,pow_succ']
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using h.resolve_right (by simp)
    | succ m =>
      simp only [pow_zero,Matrix.one_mulVec]
      calc
        _ = ∑ i, (L *ᵥ (L^m *ᵥ w)) i*v i := by
          rw [hs m w]
          apply Finset.sum_congr rfl; intro i hi; ring
        _ = ∑ i, (L^m *ᵥ w) i*(R *ᵥ v) i := by rw [matrix_transpose_pairing,ht]
        _ = 0 := by rw [hvR]; simp
  | succ n ih =>
    cases m with
    | zero =>
      simp only [pow_zero,Matrix.one_mulVec]
      rw [hs n v,matrix_transpose_pairing,ht,hwR]
      simp
    | succ m =>
      rw [hs n v,matrix_transpose_pairing,ht,descendant_raising R H L w ν hRL hHL hw hwR m]
      have hp : (∑ i, v i*w i)=0 ∨ n ≠ m := by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      calc
        _ = (((m : ℝ)+1)*(ν-m))*(∑ i, (L^n *ᵥ v) i*(L^m *ᵥ w) i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i hi
          simp only [Pi.smul_apply,smul_eq_mul]; ring
        _ = 0 := by rw [ih m hp,mul_zero]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_OscillatorHighest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def oscillatorHighest (u v : ℝ) (z p : ℕ) : ℝ :=
  (-1 : ℝ)^(z-p) * Real.sqrt (z.choose p : ℝ) * u^p * v^(z-p)

noncomputable def oscillatorRelative (t : ℝ) (z p : ℕ) : ℝ :=
  (-1 : ℝ)^p * Real.sqrt (z.choose p : ℝ) * t^p

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_OscillatorHighestNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

noncomputable def oscillatorRelativeNorm (t : ℝ) (z : ℕ) : ℝ :=
  Real.sqrt (∑ p ∈ Finset.range (z+1), (oscillatorRelative t z p)^2)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_ArrayLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Topology
open Filter

noncomputable def oscillatorArray (b : ℝ) (z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => oscillatorHighest (Real.sqrt b) (Real.sqrt (1-b)) z p
  | n+1, p =>
      (if p=0 then 0 else Real.sqrt ((((p-1 : ℕ)+1 : ℝ)*(1-b))/((n : ℝ)+1))*
        oscillatorArray b z n (p-1)) +
      (if p ≤ z+n then Real.sqrt ((((z+n-p : ℕ)+1 : ℝ)*b)/((n : ℝ)+1))*
        oscillatorArray b z n p else 0)

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RadicalCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def fourBodyRadical (r D T p j k : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ)^((1 : ℤ)-(j : ℤ)-k-T+r) *
    ((j.factorial : ℝ)*(k.factorial : ℝ)*(p.factorial : ℝ) /
      ((r.factorial : ℝ)*((D-r).factorial : ℝ)*((T-D).factorial : ℝ))))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_RadicalCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def alphaRadical (t p j : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ)^((p : ℤ)-t) * ((t.factorial : ℝ)*((p+j-t).factorial : ℝ) /
    ((p.factorial : ℝ)*(j.factorial : ℝ))))
noncomputable def sourceYFactor (D r s t p j q l : ℕ) : ℝ :=
  let i := p+j-t
  let k := q+l-t
  let T := p+j+k
  (2 : ℝ)^((1 : ℤ)-2*T+p+q-t+((r+s)/2 : ℕ)) *
    ((i.factorial : ℝ)*(k.factorial : ℝ)*(t.factorial : ℝ) / ((T-D).factorial : ℝ))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Operators_LocalFourIndexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

abbrev EmbeddedLocalFourIndex (Q D : ℕ) :=
  {b : Fin (D+1) × Fin (Q+1) × Fin (Q+1) // b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1<b.2.2}

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Basis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem fin_sum_values (n : ℕ) : (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ)*(n-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.cast_zero,zero_add,Fin.val_succ,Nat.cast_add,Nat.cast_one,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,ih]
    ring

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators Matrix

noncomputable def spinSeparatingRoot (Q : ℕ) : ℂ := Complex.exp (2*Real.pi*Complex.I/(2*Q+1 : ℕ))

end Laughlin.Rotation

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

theorem real_matrix_inverse_complex {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (A : Matrix I J ℝ) (B : Matrix J I ℝ) (h : A*B=1) :
    A.map Complex.ofReal * B.map Complex.ofReal = 1 := by
  ext i j
  have he := congrArg Complex.ofReal (congrFun (congrFun h i) j)
  simpa only [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum,Complex.ofReal_mul,
    Matrix.one_apply,apply_ite,Complex.ofReal_one,Complex.ofReal_zero] using he

theorem real_matrix_adjoint {I J : Type*} (A : Matrix I J ℝ) :
    (A.map Complex.ofReal)ᴴ = Aᵀ.map Complex.ofReal := by
  ext i j
  simp [Matrix.conjTranspose_apply,Matrix.transpose_apply]

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Spin_RectangularAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Rotation
open scoped BigOperators
open MeasureTheory MeasureTheory.Measure
variable {G I J : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def rectangularIntegral (μ : Measure G) (f : G → Matrix I J ℂ) : Matrix I J ℂ :=
  fun i j => ∫ g, f g i j ∂μ
noncomputable def rectangularOrbit (ρ : G →* Matrix I I ℂ) (σ : G →* Matrix J J ℂ)
    (M : Matrix I J ℂ) (g : G) : Matrix I J ℂ := ρ g*M*σ g⁻¹

end Laughlin.Rotation

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_Radical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin

noncomputable def threeBodyRadical (z T p : ℕ) : ℝ :=
  Real.sqrt ((2 : ℝ)^((z : ℤ)-p) *
    ((p.factorial : ℝ)*((T-p).factorial : ℝ) /
      ((3 : ℝ)^T * (z.factorial : ℝ)*((T-z).factorial : ℝ))))

end Laughlin.Spin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_ThreeBody_TraceComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def threeBodyDimensionRatio (Q z : ℕ) : ℝ :=
  (3*(Q : ℝ)-1-2*z)/(2*(Q : ℝ)-1)

end Laughlin.Spin

end OAI
end


