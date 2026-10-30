-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07
-- name    : QAlgorithms_Papers_Independent_Advance50_P07
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:30:39.030998+00:00
-- url     : https://prove2.me/theorems/6f2885d0-c7b8-4a70-b38a-9f469af7a536
-- title:
--   Definitions for The quantum capacity of channels with arbitrarily correlated noise
-- statement:
--   The objects the formalized statements of *The quantum capacity of channels with arbitrarily correlated noise* (arXiv:0902.0158) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Frame`: Nonzero subspace with an arbitrary orthonormal frame, PDF p.4, (16). Columns span the subspace; computational-coordinate subspaces are not privileged.
--   - `Ref`: Full reference copy of the input with fixed coordinate basis, PDF p.4.
--   - `framePsi`: Eq. (16), in the FULL reference and input registers, PDF p.4.
--   - `frameOutput`: Computed RB marginal of (17), PDF p.4. Applying id tensor Phi equals tracing the environment of any actual Stinespring realization. No unrelated output state or reduction equality is supplied as data.
--   - `codeOverlap`: Squared overlap for an actual subspace and decoder, (15), PDF p.3.
--   - `MinCode`: Minimum-fidelity code condition, PDF p.4, Definition 4. Every input vector is normalized; the decoder is chosen before that vector.
--   - `EntRate`: Epsilon-achievable entanglement rates, PDF p.4, Definitions 2–3. Use existence of an optimizing subspace and decoder directly (the finite- dimensional optimization in (15) is attained). No general CPTP encoder is added.
--   - `MinRate`: Epsilon-achievable minimum-output-fidelity rates, PDF p.4, (19).
--   - `qEnt`: Qent, PDF p.4, Definition 3. On lawful channels and eps>=0 the rank-one code ensures nonemptiness; finite rank bounds ensure boundedness and attainment.
--   - `qMin`: Qmin, PDF p.4, (19), with its separate operational definition.
--   - `Accept`: Acceptance neighborhood p(rho;delta), PDF p.3, (14).
--   - `zeroQuasi`: Explicit zero-order quasi-entropy (10), PDF p.3. Zero overlap gives +infinity.
--   - `zeroConditional`: Inner normalized-comparison minimum in (12), PDF p.3.
--   - `operatorCoherent`: Operator-smoothed zero coherent information (12), (30), PDF pp.3,7. Extended extrema retain +infinity when zero is an admissible effect.
--   - `OperatorAttained`: Explicit attainment of both optimizations in (12), PDF pp.3,10,13.
--   - `stateCoherentBits`: Ordinary coherent information S(B)-S(AB), PDF p.6, (24). Information100.P59.coherent is instead a Hamiltonian commutator.
--   - `quasiMoment`: Trace before the logarithm in quasiLogMoment, PDF p.6, VI.B.2.
--   - `quasiLogMoment`: Log moment, PDF p.6; used only with positive quasiMoment. Unlike Dependency50.P28.psi, this is the P-filtered Petz moment in bits.
--   - `effectFilteredState`: Filter sqrt(P) rho sqrt(P), PDF p.12, (39). Support50.P19.filtered filters a CHANNEL; here the object is a state.
--   - `filterDenom`: Denominator of the explicit ratio (28), PDF pp.7,12.
--   - `filteredOne`: Displayed filtered logarithmic-derivative ratio (28), PDF p.7. This definition does not identify the ratio with an alpha-to-one limit.
--   - `capacityRate`: Inner normalized capacity liminf, PDF p.11, before (36).
--   - `subspaceAsymptoticCapacity`: Operational subspace Q_x^infinity, PDF p.11. The frozen capacity names concern different channels or coding criteria. The one-sided outer limit is represented by its liminf; statements assert convergence when using the source limit.
--   - `positivePartMass`: Positive-part trace in spectral divergence (49), PDF p.13. Claimed50.P46.positiveTrace is a trace on a supplied infinite-dimensional model, not the positive part of a finite Hermitian difference operator.
--   - `variableRegisterInfDivergence`: Spectral INF divergence (49), PDF p.13, with extended endpoints. General finite register families are needed for Ref(A^n) times B^n; the frozen Support50.P21.spectralInf requires the literal basis Fin(n) -> I.
--   - `comparisonInf`: Spectral divergence against a SINGLE comparison-state sequence, (52), p.13.
--   - `infCoherent`: Inf-coherent information (52), PDF p.13. Minimizer existence is a conclusion of Theorem 3 and Lemma 16, never an assumption.
--   - `smoothRate`: Normalized effect-smoothed liminf on Lemma 16's left, PDF p.13.
--   - `memoryless`: Positive-block memoryless sequence, PDF p.11, Theorem 2.
--   - `bestCoherent`: Subspace coherent-information maximum, (37), PDF p.11. Theorem 2 includes actual finite-block maximizers.
--   - `scalarFrame`: Full-rank frame in one complex dimension.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, https://arxiv.org/abs/0902.0158v5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

/-! arXiv:0902.0158v5, Buscemi and Datta. Page numbers are PDF pages.
All logarithms are base two. Local definitions implement this paper's subspace
code model. Dependency50 imports are frozen accepted libraries.
Explicit source corrections and deferrals are recorded in the accompanying artifacts.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology
open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)
open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)
open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Nonzero subspace with an arbitrary orthonormal frame, PDF p.4, (16).
Columns span the subspace; computational-coordinate subspaces are not privileged. -/
structure Frame (A : Type) [Fintype A] where
  rank : ℕ
  positive : 0 < rank
  bound : rank ≤ Fintype.card A
  matrix : Matrix A (Fin rank) ℂ
  isometry : matrixᴴ * matrix = 1

/-- Full reference copy of the input with fixed coordinate basis, PDF p.4. -/
abbrev Ref (A : Type) [Fintype A] := Fin (Fintype.card A)

/-- Eq. (16), in the FULL reference and input registers, PDF p.4. -/
def framePsi {A : Type} [Fintype A] (S : Frame A) : EuclideanSpace ℂ (Ref A × A) :=
  WithLp.toLp 2 fun p =>
    if h : p.1.val < S.rank then
      ((Real.sqrt (S.rank : ℝ))⁻¹ : ℂ) * S.matrix p.2 ⟨p.1.val,h⟩
    else 0

/-- Computed RB marginal of (17), PDF p.4. Applying id tensor Phi equals
tracing the environment of any actual Stinespring realization. No unrelated
output state or reduction equality is supplied as data. -/
def frameOutput {A B : Type} [Fintype A] (Phi : Superop A B) (S : Frame A) :
    Mat (Ref A × B) :=
  idTensorSuperop Phi (pureDensity (framePsi S))

/-- Squared overlap for an actual subspace and decoder, (15), PDF p.3. -/
def codeOverlap {A B : Type} [Fintype A] (Phi : Superop A B) (S : Frame A)
    (D : Superop B A) : ℝ :=
  effectProb (pureDensity (framePsi S)) (idTensorSuperop D (frameOutput Phi S))

/-- Minimum-fidelity code condition, PDF p.4, Definition 4.
Every input vector is normalized; the decoder is chosen before that vector. -/
def MinCode {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : Superop A B) (S : Frame A) (D : Superop B A) (eps : ℝ) : Prop :=
  IsChannel D ∧ ∀ v : EuclideanSpace ℂ (Fin S.rank), ‖v‖ = 1 →
    let w : EuclideanSpace ℂ A := WithLp.toLp 2 (S.matrix.mulVec v)
    1 - eps ≤ effectProb (pureDensity w) (D (Phi (pureDensity w)))

/-- Epsilon-achievable entanglement rates, PDF p.4, Definitions 2–3.
Use existence of an optimizing subspace and decoder directly (the finite-
dimensional optimization in (15) is attained). No general CPTP encoder is added. -/
def EntRate {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : Superop A B) (eps r : ℝ) : Prop :=
  ∃ S : Frame A, r = Real.logb 2 S.rank ∧
    ∃ D : Superop B A, IsChannel D ∧ 1 - eps ≤ codeOverlap Phi S D

/-- Epsilon-achievable minimum-output-fidelity rates, PDF p.4, (19). -/
def MinRate {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : Superop A B) (eps r : ℝ) : Prop :=
  ∃ S : Frame A, r = Real.logb 2 S.rank ∧ ∃ D : Superop B A, MinCode Phi S D eps

/-- Qent, PDF p.4, Definition 3. On lawful channels and eps>=0 the rank-one
code ensures nonemptiness; finite rank bounds ensure boundedness and attainment. -/
def qEnt {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : Superop A B) (eps : ℝ) : ℝ := sSup {r | EntRate Phi eps r}

/-- Qmin, PDF p.4, (19), with its separate operational definition. -/
def qMin {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : Superop A B) (eps : ℝ) : ℝ := sSup {r | MinRate Phi eps r}

/-- Acceptance neighborhood p(rho;delta), PDF p.3, (14). -/
def Accept {I : Type} [Fintype I] [DecidableEq I]
    (rho P : Mat I) (delta : ℝ) : Prop :=
  IsEffect P ∧ 1 - delta ≤ effectProb P rho

/-- Explicit zero-order quasi-entropy (10), PDF p.3. Zero overlap gives +infinity. -/
def zeroQuasi {I : Type} [Fintype I] [DecidableEq I] (rho sigma P : Mat I) : EReal :=
  -elog ((cfc Real.sqrt P * supportPower rho 0 * cfc Real.sqrt P * sigma).trace.re)

/-- Inner normalized-comparison minimum in (12), PDF p.3. -/
def zeroConditional {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho P : Mat (A × B)) : EReal :=
  ⨅ sigma : {tau : Mat B // Density tau}, zeroQuasi rho (Matrix.kronecker (1 : Mat A) sigma.1) P

/-- Operator-smoothed zero coherent information (12), (30), PDF pp.3,7.
Extended extrema retain +infinity when zero is an admissible effect. -/
def operatorCoherent {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Mat (A × B)) (delta : ℝ) : EReal :=
  ⨆ P : {P : Mat (A × B) // Accept rho P delta}, zeroConditional rho P.1

/-- Explicit attainment of both optimizations in (12), PDF pp.3,10,13. -/
def OperatorAttained {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Mat (A × B)) (delta : ℝ) : Prop :=
  ∃ P : Mat (A × B), Accept rho P delta ∧
    operatorCoherent rho delta = zeroConditional rho P ∧
    ∃ sigma : {tau : Mat B // Density tau},
      zeroConditional rho P = zeroQuasi rho (Matrix.kronecker (1 : Mat A) sigma.1) P

/-- Ordinary coherent information S(B)-S(AB), PDF p.6, (24).
Information100.P59.coherent is instead a Hamiltonian commutator. -/
def stateCoherentBits {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Mat (A × B)) : ℝ :=
  -(traceLeft rho * cfc (Real.logb 2) (traceLeft rho)).trace.re +
    (rho * cfc (Real.logb 2) rho).trace.re

/-- Trace before the logarithm in quasiLogMoment, PDF p.6, VI.B.2. -/
def quasiMoment {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma P : Mat I) (alpha : ℝ) : ℝ :=
  (cfc Real.sqrt P * supportPower rho alpha * cfc Real.sqrt P *
    supportPower sigma (1-alpha)).trace.re

/-- Log moment, PDF p.6; used only with positive quasiMoment.
Unlike Dependency50.P28.psi, this is the P-filtered Petz moment in bits. -/
def quasiLogMoment {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma P : Mat I) (alpha : ℝ) : ℝ := Real.logb 2 (quasiMoment rho sigma P alpha)

/-- Filter sqrt(P) rho sqrt(P), PDF p.12, (39).
Support50.P19.filtered filters a CHANNEL; here the object is a state. -/
def effectFilteredState {I : Type} [Fintype I] [DecidableEq I] (rho P : Mat I) : Mat I :=
  cfc Real.sqrt P * rho * cfc Real.sqrt P

/-- Denominator of the explicit ratio (28), PDF pp.7,12. -/
def filterDenom {I : Type} [Fintype I] [DecidableEq I] (rho sigma P : Mat I) : ℝ :=
  (effectFilteredState rho P * supportPower sigma 0).trace.re

/-- Displayed filtered logarithmic-derivative ratio (28), PDF p.7.
This definition does not identify the ratio with an alpha-to-one limit. -/
def filteredOne {I : Type} [Fintype I] [DecidableEq I] (rho sigma P : Mat I) : ℝ :=
  (cfc Real.sqrt P * rho * cfc (Real.logb 2) rho * cfc Real.sqrt P * supportPower sigma 0 -
    effectFilteredState rho P * cfc (Real.logb 2) sigma).trace.re / filterDenom rho sigma P

/-- Inner normalized capacity liminf, PDF p.11, before (36). -/
def capacityRate {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : (k : ℕ) → Superop (PositiveTensorBasis A k) (PositiveTensorBasis B k)) (minimum : Bool) (eps : ℝ) : EReal :=
  Filter.liminf (fun k : ℕ =>
    (((if minimum then qMin (Phi k) eps else qEnt (Phi k) eps) / (k+1 : ℕ) : ℝ) : EReal)) atTop

/-- Operational subspace Q_x^infinity, PDF p.11.
The frozen capacity names concern different channels or coding criteria. The one-sided outer limit is represented by
its liminf; statements assert convergence when using the source limit. -/
def subspaceAsymptoticCapacity {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : (k : ℕ) → Superop (PositiveTensorBasis A k) (PositiveTensorBasis B k)) (minimum : Bool) : EReal :=
  Filter.liminf (capacityRate Phi minimum) (𝓝[>] (0 : ℝ))

/-- Positive-part trace in spectral divergence (49), PDF p.13.
Claimed50.P46.positiveTrace is a trace on a supplied infinite-dimensional model,
not the positive part of a finite Hermitian difference operator. -/
def positivePartMass {I : Type} [Fintype I] [DecidableEq I] (X : Mat I) : ℝ :=
  (cfc (fun t : ℝ => max t 0) X).trace.re

/-- Spectral INF divergence (49), PDF p.13, with extended endpoints.
General finite register families are needed for Ref(A^n) times B^n; the frozen
Support50.P21.spectralInf requires the literal basis Fin(n) -> I. -/
def variableRegisterInfDivergence {I : ℕ → Type} [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]
    (rho sigma : (k : ℕ) → Mat (I k)) : EReal :=
  sSup {v : EReal | ∃ gamma : ℝ, v = (gamma : EReal) ∧
    Filter.liminf (fun k : ℕ => positivePartMass (rho k -
      (((2 : ℝ) ^ ((k+1 : ℕ) * gamma) : ℝ) : ℂ) • sigma k)) atTop = 1}

/-- Spectral divergence against a SINGLE comparison-state sequence, (52), p.13. -/
def comparisonInf {R B : ℕ → Type} [∀ k, Fintype (R k)] [∀ k, Fintype (B k)]
    [∀ k, DecidableEq (R k)] [∀ k, DecidableEq (B k)]
    (rho : (k : ℕ) → Mat (R k × B k)) (sigma : (k : ℕ) → {tau : Mat (B k) // Density tau}) : EReal :=
  variableRegisterInfDivergence rho (fun k => Matrix.kronecker (1 : Mat (R k)) (sigma k).1)

/-- Inf-coherent information (52), PDF p.13. Minimizer existence is a
conclusion of Theorem 3 and Lemma 16, never an assumption. -/
def infCoherent {R B : ℕ → Type} [∀ k, Fintype (R k)] [∀ k, Fintype (B k)]
    [∀ k, DecidableEq (R k)] [∀ k, DecidableEq (B k)]
    (rho : (k : ℕ) → Mat (R k × B k)) : EReal :=
  ⨅ sigma : (k : ℕ) → {tau : Mat (B k) // Density tau}, comparisonInf rho sigma

/-- Normalized effect-smoothed liminf on Lemma 16's left, PDF p.13. -/
def smoothRate {R B : ℕ → Type} [∀ k, Fintype (R k)] [∀ k, Fintype (B k)]
    [∀ k, DecidableEq (R k)] [∀ k, DecidableEq (B k)]
    (rho : (k : ℕ) → Mat (R k × B k)) (delta : ℝ) : EReal :=
  Filter.liminf (fun k : ℕ =>
    (((1 / (k+1 : ℕ) : ℝ) : EReal) * operatorCoherent (rho k) delta)) atTop

/-- Positive-block memoryless sequence, PDF p.11, Theorem 2. -/
def memoryless {A B : Type} [Fintype A] [DecidableEq A] (Phi : Superop A B) :
    (k : ℕ) → Superop (PositiveTensorBasis A k) (PositiveTensorBasis B k) :=
  fun k => piSuperop (fun _ : Fin (k+1) => Phi)

/-- Subspace coherent-information maximum, (37), PDF p.11.
Theorem 2 includes actual finite-block maximizers. -/
def bestCoherent {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (Phi : Superop A B) : ℝ :=
  sSup {x | ∃ S : Frame A, x = stateCoherentBits (frameOutput Phi S)}

/-! Small sanity examples for local definitions, not proofs of paper results. -/

/-- Full-rank frame in one complex dimension. -/
def scalarFrame : Frame (Fin 1) where
  rank := 1
  positive := by decide
  bound := by simp
  matrix := 1
  isometry := by simp

example : framePsi scalarFrame (0,0) = 1 := by
  simp [framePsi, scalarFrame, Matrix.one_apply]

example {A B : Type} [Fintype B] : traceRight (0 : Mat (A × B)) = 0 := by
  ext a b
  simp [traceRight]

example {I : Type} [Fintype I] [DecidableEq I] (rho : Mat I) :
    Accept rho 0 1 := by
  refine ⟨⟨Matrix.PosSemidef.zero, ?_⟩, ?_⟩
  · simpa using (Matrix.PosSemidef.one : (1 : Mat I).PosSemidef)
  · simp [effectProb]

example : elog 0 = ⊥ := by simp [elog]

example {I : Type} [Fintype I] [DecidableEq I] (rho : Mat I) :
    effectFilteredState rho (0 : Mat I) = 0 := by
  simp [effectFilteredState, cfc_zero]

end QAlgorithms.Papers.Independent.Advance50.P07


