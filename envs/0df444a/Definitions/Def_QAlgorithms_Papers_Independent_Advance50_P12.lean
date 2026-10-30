-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P12
-- name    : QAlgorithms_Papers_Independent_Advance50_P12
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:09:58.835118+00:00
-- url     : https://prove2.me/theorems/149a69b6-418a-46eb-a123-a0b8e30a6fe5
-- title:
--   Definitions for The operational meaning of min- and max-entropy
-- statement:
--   The objects the formalized statements of *The operational meaning of min- and max-entropy* (arXiv:0807.1338) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `purificationComplement`: PDF p.2, Definition 2: the AC marginal of the canonical purification with C=A times B and coefficients (sqrt rho)((a,b),c). The AB marginal is rho for a density matrix. The conjugation and the traced-out B are explicit.
--   - `purificationMaxEntropy`: PDF p.2, (6): conditional max entropy by purification duality, without using Theorem 3's fidelity formula. The frozen Support50.P21.hMax instead denotes unconditional log-rank entropy, which the source distinguishes in footnote 7.
--   - `completelyMixedDensity`: PDF pp.6,10: mixed density I_A/d_A; positive dimension is imposed at use. Distinct from the frozen QAlgorithms.uniformState, a pure uniform ket.
--   - `entangledKet`: PDF p.7, (28): a maximally entangled unit vector on A and an isomorphic copy A'.
--   - `targetOverlap`: PDF p.9, Theorem 2 and Remark 1: optimal SQUARED root fidelity with a specified pure target; optimization is over all CPTP maps B to A'.
--   - `qCorr`: PDF p.9, Theorem 2: dimension-scaled maximal achievable singlet fraction. The output register is A', not B, so no comparison of input dimensions is needed.
--   - `qDecpl`: PDF pp.6,10, (22): dimension-scaled decoupling accuracy, optimized over all normalized reference states, rather than just the actual B marginal.
--   - `pSecr`: PDF p.5, before (19): the independent classical ensemble expression for secrecy, max_sigma (sum_x sqrt(p_x) F(rho_x,sigma)) squared. It is dimension-scaled and can exceed one.
--   - `ClassicalOnFirst`: PDF pp.7–8: Hermitian operator classical in the fixed first-register basis. The same coordinate basis is used for rho and for the restricted dual optimizer.
--   - `EntropyPrimalFeasible`: PDF p.8, (29): the primal operator is PSD and not trace-normalized. The frozen SDP.PrimalFeasible models scalar trace-inequality constraints, not this operator-valued entropy constraint.
--   - `EntropyDualFeasible`: PDF p.8, (29): the dual partial trace is equality to the identity. The frozen SDP.DualFeasible instead models a vector of nonnegative scalar multipliers for a different SDP; it is not this operator constraint.
--   - `UnitalCP`: PDF p.7: unital CP maps on the entire operator algebra. The existential linear map bundles complex linearity; positivity covers every finite ancilla.
-- source:
--   The operational meaning of min-and max-entropy, arXiv:0807.1338v2, https://arxiv.org/abs/0807.1338v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P23

/-! Koenig, Renner and Schaffner, arXiv:0807.1338v2.
All page numbers are PDF pages; logarithms are binary. Finite nonempty index
sets are arbitrary chosen orthonormal bases, with no qubit restriction.
Compilation is pending the separate mechanical handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P12

open QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P07 (CQData cqDensity)
open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative elog marginalAB)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)
open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)
open QAlgorithms.Papers.Independent.Support50.P23 (exp2Extended independentProduct)

variable {A B C D X : Type}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D] [DecidableEq X]

/-- PDF p.2, Definition 2: the AC marginal of the canonical purification
with C=A times B and coefficients (sqrt rho)((a,b),c). The AB marginal is rho
for a density matrix. The conjugation and the traced-out B are explicit. -/
def purificationComplement (rho : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × (A × B)) (A × (A × B)) ℂ :=
  fun x y => ∑ b, (cfc Real.sqrt rho) (x.1, b) x.2 *
    conj ((cfc Real.sqrt rho) (y.1, b) y.2)

/-- PDF p.2, (6): conditional max entropy by purification duality, without using
Theorem 3's fidelity formula. The frozen Support50.P21.hMax instead denotes
unconditional log-rank entropy, which the source distinguishes in footnote 7. -/
def purificationMaxEntropy (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  -conditionalMinEntropy (purificationComplement rho)

/-- PDF pp.6,10: mixed density I_A/d_A; positive dimension is imposed at use.
Distinct from the frozen QAlgorithms.uniformState, a pure uniform ket. -/
def completelyMixedDensity (A : Type) [Fintype A] [DecidableEq A] : Matrix A A ℂ :=
  (Fintype.card A : ℂ)⁻¹ • 1

/-- PDF p.7, (28): a maximally entangled unit vector on A and an isomorphic copy A'. -/
def entangledKet (A : Type) [Fintype A] [DecidableEq A] : EuclideanSpace ℂ (A × A) :=
  WithLp.toLp 2 fun x => if x.1 = x.2 then
    ((Real.sqrt (Fintype.card A : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.9, Theorem 2 and Remark 1: optimal SQUARED root fidelity with a
specified pure target; optimization is over all CPTP maps B to A'. -/
def targetOverlap (rho : Matrix (A × B) (A × B) ℂ)
    (psi : EuclideanSpace ℂ (A × A)) : ℝ :=
  sSup {v : ℝ | ∃ f : Superop B A, IsChannel f ∧
    v = rootFidelity (idTensorSuperop f rho) (pureDensity psi) ^ 2}

/-- PDF p.9, Theorem 2: dimension-scaled maximal achievable singlet fraction.
The output register is A', not B, so no comparison of input dimensions is needed. -/
def qCorr (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  (Fintype.card A : ℝ) * targetOverlap rho (entangledKet A)

/-- PDF pp.6,10, (22): dimension-scaled decoupling accuracy, optimized over
all normalized reference states, rather than just the actual B marginal. -/
def qDecpl (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  (Fintype.card A : ℝ) * sSup {v : ℝ | ∃ sigma : Matrix B B ℂ,
    IsDensityMatrix sigma ∧
    v = rootFidelity rho (Matrix.kronecker (completelyMixedDensity A) sigma) ^ 2}

/-- PDF p.5, before (19): the independent classical ensemble expression for
secrecy, max_sigma (sum_x sqrt(p_x) F(rho_x,sigma)) squared.
It is dimension-scaled and can exceed one. -/
def pSecr (e : CQData X B) : ℝ :=
  sSup {v : ℝ | ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
    v = (∑ x, Real.sqrt (e.prob x) * rootFidelity (e.state x) sigma) ^ 2}

/-- PDF pp.7–8: Hermitian operator classical in the fixed first-register basis.
The same coordinate basis is used for rho and for the restricted dual optimizer. -/
def ClassicalOnFirst (rho : Matrix (A × B) (A × B) ℂ) : Prop :=
  rho.IsHermitian ∧ ∀ a a2 b b2, a ≠ a2 → rho (a, b) (a2, b2) = 0

/-- PDF p.8, (29): the primal operator is PSD and not trace-normalized.
The frozen SDP.PrimalFeasible models scalar trace-inequality constraints,
not this operator-valued entropy constraint. -/
def EntropyPrimalFeasible (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix B B ℂ) : Prop :=
  sigma.PosSemidef ∧ (Matrix.kronecker (1 : Matrix A A ℂ) sigma - rho).PosSemidef

/-- PDF p.8, (29): the dual partial trace is equality to the identity.
The frozen SDP.DualFeasible instead models a vector of nonnegative scalar
multipliers for a different SDP; it is not this operator constraint. -/
def EntropyDualFeasible (e : Matrix (A × B) (A × B) ℂ) : Prop :=
  e.PosSemidef ∧ traceLeft e = 1

/-- PDF p.7: unital CP maps on the entire operator algebra. The existential
linear map bundles complex linearity; positivity covers every finite ancilla. -/
def UnitalCP (f : Superop A B) : Prop :=
  ∃ g : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ,
    (∀ z, f z = g z) ∧ Entanglement.IsCompletelyPositive g ∧ g 1 = 1

/-! Sanity examples for the local substrate. -/

example : completelyMixedDensity Unit = (1 : Matrix Unit Unit ℂ) := by
  simp [completelyMixedDensity]

example : entangledKet Unit ((), ()) = 1 := by
  simp [entangledKet]

example : purificationComplement (1 : Matrix (Unit × Unit) (Unit × Unit) ℂ) = 1 := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  simp [purificationComplement, cfc_one, Matrix.one_apply]

example (rho : Matrix (A × B) (A × B) ℂ) (a a2 : A) (c c2 : A × B) :
    purificationComplement rho (a, c) (a2, c2) =
      ∑ b, (cfc Real.sqrt rho) (a, b) c * conj ((cfc Real.sqrt rho) (a2, b) c2) := rfl

example : ClassicalOnFirst (0 : Matrix (A × B) (A × B) ℂ) := by
  exact ⟨Matrix.isHermitian_zero, by intros; rfl⟩

example (rho : Matrix (A × B) (A × B) ℂ) :
    purificationMaxEntropy rho = -conditionalMinEntropy (purificationComplement rho) := rfl

end QAlgorithms.Papers.Independent.Advance50.P12


