-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P46
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P46
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T05:26:30.741506+00:00
-- url     : https://prove2.me/theorems/f1de41af-211a-4e1f-b308-7215f50c67b0
-- title:
--   Definitions for Monotonicity of the Quantum Relative Entropy Under Positive Maps
-- statement:
--   The objects the formalized statements of *Monotonicity of the Quantum Relative Entropy Under Positive Maps* (arXiv:1512.06117) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TraceLinearOperationBetween`: PDF p.2, Notation: a complex-linear map from the full trace-class space T(H) to T(K). Its ambient values off trace class impose no restriction.
--   - `traceClassImage`: PDF p.2: restrict the output of a trace-class operation to its actual domain.
--   - `PositiveTracePreservingBetween`: PDF p.2, Notation and Theorem 1: positivity and trace preservation are required on every positive trace-class input, not only on the displayed pair.
--   - `PositiveTraceNonincreasingBetween`: PDF pp.2–3, Notation and Theorem 1': positivity and trace nonincrease on the entire positive trace-class cone, between possibly different spaces.
--   - `literalTraceClassRelativeEntropy`: PDF pp.1–2, (1) and Notation: literal unnormalized relative entropy in nats. On positive trace-class pairs, the accepted corrected extended divergence is D(rho||sigma)+tr(sigma-rho). Subtract ONLY this finite real trace correction. The ENNReal-to-EReal embedding retains infinity; finite negative D is allowed. No two potentially infinite entropy terms are subtracted.
--   - `PositiveMatrixTraceNonincreasing`: PDF p.3, (4)–(5): positive finite-dimensional maps with trace nonincrease on every PSD matrix. Complex linearity is in the map type.
--   - `finiteLiteralRelativeEntropy`: PDF pp.1–3, (1): finite-dimensional literal Umegaki entropy in nats, including support failure. This direct formula also accepts subnormalized outputs.
--   - `traceDecreaseMap`: PDF p.3, counterexample: discard off-diagonal entries and halve the first entry.
--   - `counterexampleRho`: PDF p.3, counterexample: the first normalized input state.
--   - `counterexampleSigma`: PDF p.3, counterexample: the second normalized input state.
-- source:
--   Monotonicity of the Quantum Relative Entropy Under Positive Maps, arXiv:1512.06117v3, https://arxiv.org/abs/1512.06117v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

/-!
Müller-Hermes–Reeb, arXiv:1512.06117v3, PDF pp.1–7.
All new definitions are local to this paper. Arbitrary countable Hilbert bases
represent separable complex Hilbert spaces; they need not diagonalize either
operator. Nuclear trace class and the corrected extended divergence are accepted
Dependency50.P13 definitions. Only the finite trace correction is removed here.
Theorem 3 (PDF p.4) is recorded as accepted-library reuse, without a duplicate.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P46

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms
open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass TraceClass IsPositive operatorTrace)
open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)
open QAlgorithms.Papers.Independent.Bridge50.P49 (beigiSandwichedDivergence)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- PDF p.2, Notation: a complex-linear map from the full trace-class space
T(H) to T(K). Its ambient values off trace class impose no restriction. -/
def TraceLinearOperationBetween
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop :=
  (∀ A, IsTraceClass A → IsTraceClass (Phi A)) ∧
  (∀ A B, IsTraceClass A → IsTraceClass B → Phi (A + B) = Phi A + Phi B) ∧
  (∀ (z : ℂ) A, IsTraceClass A → Phi (z • A) = z • Phi A)

example : TraceLinearOperationBetween (id : (H →L[ℂ] H) → (H →L[ℂ] H)) := by
  exact ⟨fun A hA => hA, fun A B hA hB => rfl, fun z A hA => rfl⟩

/-- PDF p.2: restrict the output of a trace-class operation to its actual domain. -/
def traceClassImage (Phi : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hPhi : TraceLinearOperationBetween Phi) (A : TraceClass H) : TraceClass K :=
  ⟨Phi A.val, hPhi.1 A.val A.property⟩

example (Phi : (H →L[ℂ] H) → (K →L[ℂ] K))
    (hPhi : TraceLinearOperationBetween Phi) (A : TraceClass H) :
    (traceClassImage Phi hPhi A).val = Phi A.val := rfl

/-- PDF p.2, Notation and Theorem 1: positivity and trace preservation are
required on every positive trace-class input, not only on the displayed pair. -/
def PositiveTracePreservingBetween {I J : Type*}
    (b : HilbertBasis I ℂ H) (c : HilbertBasis J ℂ K)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop :=
  TraceLinearOperationBetween Phi ∧ ∀ A, IsTraceClass A → IsPositive A →
    IsPositive (Phi A) ∧ operatorTrace c (Phi A) = operatorTrace b A

example {I : Type*} (b : HilbertBasis I ℂ H) :
    PositiveTracePreservingBetween b b (id : (H →L[ℂ] H) → (H →L[ℂ] H)) := by
  exact ⟨⟨fun A hA => hA, fun A B hA hB => rfl, fun z A hA => rfl⟩,
    fun A hA hp => ⟨hp, rfl⟩⟩

/-- PDF pp.2–3, Notation and Theorem 1': positivity and trace nonincrease
on the entire positive trace-class cone, between possibly different spaces. -/
def PositiveTraceNonincreasingBetween {I J : Type*}
    (b : HilbertBasis I ℂ H) (c : HilbertBasis J ℂ K)
    (Phi : (H →L[ℂ] H) → (K →L[ℂ] K)) : Prop :=
  TraceLinearOperationBetween Phi ∧ ∀ A, IsTraceClass A → IsPositive A →
    IsPositive (Phi A) ∧ (operatorTrace c (Phi A)).re ≤ (operatorTrace b A).re

example {I : Type*} (b : HilbertBasis I ℂ H) :
    PositiveTraceNonincreasingBetween b b (id : (H →L[ℂ] H) → (H →L[ℂ] H)) := by
  exact ⟨⟨fun A hA => hA, fun A B hA hB => rfl, fun z A hA => rfl⟩,
    fun A hA hp => ⟨hp, le_rfl⟩⟩

/-- PDF pp.1–2, (1) and Notation: literal unnormalized relative entropy in nats.
On positive trace-class pairs, the accepted corrected extended divergence is
D(rho||sigma)+tr(sigma-rho). Subtract ONLY this finite real trace correction.
The ENNReal-to-EReal embedding retains infinity; finite negative D is allowed.
No two potentially infinite entropy terms are subtracted. -/
def literalTraceClassRelativeEntropy {I : Type*} (b : HilbertBasis I ℂ H)
    (rho sigma : TraceClass H) : EReal :=
  (QAlgorithms.Papers.Independent.Dependency50.P13.relativeEntropy rho sigma : EReal) -
    (((operatorTrace b sigma.val).re - (operatorTrace b rho.val).re : ℝ) : EReal)

example {I : Type*} (b : HilbertBasis I ℂ H) (rho sigma : TraceClass H)
    (h : operatorTrace b sigma.val = operatorTrace b rho.val) :
    literalTraceClassRelativeEntropy b rho sigma =
      (QAlgorithms.Papers.Independent.Dependency50.P13.relativeEntropy rho sigma : EReal) := by
  simp [literalTraceClassRelativeEntropy, h]

/-- PDF p.3, (4)–(5): positive finite-dimensional maps with trace nonincrease
on every PSD matrix. Complex linearity is in the map type. -/
def PositiveMatrixTraceNonincreasing {d e : ℕ}
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin e) (Fin e) ℂ) : Prop :=
  ∀ A, A.PosSemidef → (Phi A).PosSemidef ∧ (Phi A).trace.re ≤ A.trace.re

example (d : ℕ) : PositiveMatrixTraceNonincreasing
    (LinearMap.id : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) := by
  intro A hA
  exact ⟨hA, le_rfl⟩

/-- PDF pp.1–3, (1): finite-dimensional literal Umegaki entropy in nats,
including support failure. This direct formula also accepts subnormalized outputs. -/
def finiteLiteralRelativeEntropy {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : EReal :=
  if Dominates sigma rho then
    (((cfc (fun x : ℝ => x * Real.log x) rho -
      rho * cfc Real.log sigma).trace.re : ℝ) : EReal)
  else ⊤

example {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (h : ¬ Dominates sigma rho) :
    finiteLiteralRelativeEntropy rho sigma = ⊤ := by
  simp [finiteLiteralRelativeEntropy, h]

/-- PDF p.3, counterexample: discard off-diagonal entries and halve the first entry. -/
def traceDecreaseMap : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := !![X 0 0 / 2, 0; 0, X 1 1]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_div]
  map_smul' z X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul, mul_div_assoc]

example (X : Matrix (Fin 2) (Fin 2) ℂ) : traceDecreaseMap X 0 0 = X 0 0 / 2 := rfl

/-- PDF p.3, counterexample: the first normalized input state. -/
def counterexampleRho : Matrix (Fin 2) (Fin 2) ℂ := !![(1 / 3 : ℂ), 0; 0, 2 / 3]

/-- PDF p.3, counterexample: the second normalized input state. -/
def counterexampleSigma : Matrix (Fin 2) (Fin 2) ℂ := !![(2 / 3 : ℂ), 0; 0, 1 / 3]

example : counterexampleRho 0 0 = (1 / 3 : ℂ) := rfl

example : counterexampleSigma 1 1 = (1 / 3 : ℂ) := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P46


