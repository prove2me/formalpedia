-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P15
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P15
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T00:55:05.2755+00:00
-- url     : https://prove2.me/theorems/1ab94c95-a52e-4202-94f8-6ae9c2095a0a
-- title:
--   Definitions for Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity
-- statement:
--   The objects the formalized statements of *Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity* (arXiv:1310.7028) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `expBits`: The extended value 2^x; PDF p.13, (6.1). No infinite value is sent through toReal.
--   - `eaChoiOutput`: Canonical output with reference marginal rho; actual input marginal rho^T; PDF p.7, (3.8). All reference square roots have explicit output identities.
--   - `stateInfo`: State mutual-information optimization over all B states; PDF pp.7,14, (3.3),(6.3).
--   - `inputInfo`: Fixed-reference input objective; PDF pp.4,7, (2.4)--(2.9),(3.5)--(3.8).
--   - `channelInfo`: Channel information, sup input then inf comparison; all states, including singular and block-correlated states, are admitted. Attainment is a theorem conclusion below.
--   - `choiObjective`: The norm in (5.8), with the support convention inherited from (3.2), PDF pp.10--11. A pseudoinverse without this outer guard is incorrect for singular comparisons.
--   - `convexStateMix`: Convex combination of matrices, PDF p.11, (5.13).
--   - `unbundledTensorMap`: Heterogeneous tensor product from matrix units, including correlated inputs; PDF pp.8,12--13. This is not a rule restricted to product densities.
--   - `ParallelEACode`: A parallel EA classical code, PDF pp.7--8, §4. Shared state is message independent; encoders are local CPTP maps, followed by a single joint POVM. There is no feedback. All positive finite ancilla and message dimensions are allowed.
--   - `codeOutput`: Actual message-conditioned output in wire order B^n,T_B; PDF p.8, (4.8)--(4.11).
--   - `parallelEASuccess`: Uniform-message average success, PDF p.8, (4.10)--(4.11).
--   - `parallelEARate`: Integer-message rate, used only for n>=1; PDF p.7, §4.
--   - `sibsonK`: Sibson's positive partial trace K, symmetrized as in the proof; PDF p.14, (6.8). Partial-trace cyclicity equates this with Tr_A(rho_A^(1-alpha) rho_AB^alpha).
--   - `sibsonZ`: Positive normalization Z=Tr K^(1/alpha), PDF p.14, (6.8).
--   - `sibsonState`: Constructed Sibson optimizer; positivity of Z is a conclusion, never an assumption; PDF p.14, (6.8). The formula is used only for densities and alpha>1.
--   - `logTrace`: The real log-trace function differentiated in Lemma 9, PDF pp.15--16.
--   - `ordinaryStateInfo`: Ordinary state mutual information in bits, with the actual two marginals; PDF p.15.
--   - `cbOneAlpha`: The positive-Choi CB 1-to-alpha quantity (not the p-to-p norm), PDF p.3, (2.1). Used for complex-linear CP maps, without a trace-preserving condition.
-- source:
--   Multiplicativity of completely bounded $p$-norms implies a strong converse for entanglement-assisted capacity, arXiv:1310.7028v3, https://arxiv.org/abs/1310.7028v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P43
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71

/-!
Gupta--Wilde, arXiv:1310.7028v3. Citations use PDF pages; logarithms use bits.
Imports include only Mathlib, frozen Defs modules and pinned accepted paper libraries,
as authorized by the independent-paper workflow. Exact accepted primitives are opened
selectively below; no frozen module is edited. The PSD Schatten expression is used only
on positive operators. Distinct parallel-code packaging and unbundled tensor action
remain paper-local. Proposition 2 and unrestricted printed (6.6) remain deferred.
Compilation is pending the explicitly requested batch handoff.
-/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Topology
open Filter

namespace QAlgorithms.Papers.Independent.Intakenext100.P15

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

-- These are pinned accepted definitions, not other chunks from the current run.
open QAlgorithms.Papers.Independent.Bridge50.P43 (NormalizedDensity payoff)
open QAlgorithms.Papers.Independent.Dependency50.P09 (Divergence logExt sandwichedD petzD)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Information100.P63 (schatten)
open QAlgorithms.Papers.Independent.Information100.P71
  (supportPower SupportIncluded stateRelative channelPower diamond)

/-- The extended value 2^x; PDF p.13, (6.1). No infinite value is sent through toReal. -/
def expBits (x : EReal) : ENNReal :=
  if x = ⊤ then ⊤ else if x = ⊥ then 0 else ENNReal.ofReal (Real.rpow 2 x.toReal)

/-- Canonical output with reference marginal rho; actual input marginal rho^T;
PDF p.7, (3.8). All reference square roots have explicit output identities. -/
def eaChoiOutput {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (rho : Matrix A A ℂ) : Matrix (A × B) (A × B) ℂ :=
  let S := Matrix.kronecker (supportPower rho (1 / 2 : ℝ)) (1 : Matrix B B ℂ)
  S * choi N * S

/-- State mutual-information optimization over all B states; PDF pp.7,14, (3.3),(6.3). -/
def stateInfo {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (D : Divergence) (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  ⨅ sigma : NormalizedDensity B, D rho (Matrix.kronecker (traceRight rho) sigma.1)

/-- Fixed-reference input objective; PDF pp.4,7, (2.4)--(2.9),(3.5)--(3.8). -/
def inputInfo {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (D : Divergence) (N : Superop A B) (rho : NormalizedDensity A) : EReal :=
  ⨅ sigma : NormalizedDensity B, D (eaChoiOutput N rho.1) (Matrix.kronecker rho.1 sigma.1)

/-- Channel information, sup input then inf comparison; all states, including singular
and block-correlated states, are admitted. Attainment is a theorem conclusion below. -/
def channelInfo {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (D : Divergence) (N : Superop A B) : EReal :=
  ⨆ rho : NormalizedDensity A, inputInfo D N rho

/-- The norm in (5.8), with the support convention inherited from (3.2), PDF pp.10--11.
A pseudoinverse without this outer guard is incorrect for singular comparisons. -/
def choiObjective {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (alpha : ℝ) (N : Superop A B) (rho : Matrix A A ℂ) (sigma : Matrix B B ℂ) : EReal :=
  if SupportIncluded (eaChoiOutput N rho) (Matrix.kronecker rho sigma) then
    let G := supportPower (choi N) (1 / 2 : ℝ)
    (schatten alpha (G * Matrix.kronecker (supportPower rho (1 / alpha))
      (supportPower sigma ((1 - alpha) / alpha)) * G) : EReal)
  else ⊤

/-- Convex combination of matrices, PDF p.11, (5.13). -/
def convexStateMix {I : Type} (t : ℝ) (X Y : Matrix I I ℂ) : Matrix I I ℂ :=
  (t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y

/-- Heterogeneous tensor product from matrix units, including correlated inputs;
PDF pp.8,12--13. This is not a rule restricted to product densities. -/
def unbundledTensorMap {A B C D : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E : Superop A C) (F : Superop B D) : Superop (A × B) (C × D) :=
  fun X p q => ∑ a, ∑ aa, ∑ b, ∑ bb,
    X (a,b) (aa,bb) * E (Matrix.single a aa 1) p.1 q.1 *
      F (Matrix.single b bb 1) p.2 q.2

/-- A parallel EA classical code, PDF pp.7--8, §4. Shared state is message independent;
encoders are local CPTP maps, followed by a single joint POVM. There is no feedback.
All positive finite ancilla and message dimensions are allowed. -/
structure ParallelEACode (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  protocol : QAlgorithms.Papers.Independent.Dependency50.P23.EACode
    (Fin n → A) (Fin n → B) messages

/-- Actual message-conditioned output in wire order B^n,T_B; PDF p.8, (4.8)--(4.11). -/
def codeOutput {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (N : Superop A B) (C : ParallelEACode A B n) (m : Fin C.messages) :
    Matrix ((Fin n → B) × Fin C.protocol.bDim) ((Fin n → B) × Fin C.protocol.bDim) ℂ :=
  unbundledTensorMap (channelPower N n) (fun X => X)
    (unbundledTensorMap (C.protocol.encode m) (fun X => X) C.protocol.shared)

/-- Uniform-message average success, PDF p.8, (4.10)--(4.11). -/
def parallelEASuccess {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (N : Superop A B) (C : ParallelEACode A B n) : ℝ :=
  QAlgorithms.Papers.Independent.Dependency50.P23.eaCodeSuccess (channelPower N n) C.protocol

/-- Integer-message rate, used only for n>=1; PDF p.7, §4. -/
def parallelEARate {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (C : ParallelEACode A B n) : ℝ := Real.logb 2 C.messages / n

/-- Sibson's positive partial trace K, symmetrized as in the proof; PDF p.14, (6.8).
Partial-trace cyclicity equates this with Tr_A(rho_A^(1-alpha) rho_AB^alpha). -/
def sibsonK {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (alpha : ℝ) (rho : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  let S := Matrix.kronecker (supportPower (traceRight rho) ((1 - alpha) / 2))
    (1 : Matrix B B ℂ)
  traceLeft (S * supportPower rho alpha * S)

/-- Positive normalization Z=Tr K^(1/alpha), PDF p.14, (6.8). -/
def sibsonZ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (alpha : ℝ) (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  (supportPower (sibsonK alpha rho) (1 / alpha)).trace.re

/-- Constructed Sibson optimizer; positivity of Z is a conclusion, never an assumption;
PDF p.14, (6.8). The formula is used only for densities and alpha>1. -/
def sibsonState {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (alpha : ℝ) (rho : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  ((sibsonZ alpha rho)⁻¹ : ℂ) • supportPower (sibsonK alpha rho) (1 / alpha)

/-- The real log-trace function differentiated in Lemma 9, PDF pp.15--16. -/
def logTrace {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (alpha : ℝ) : ℝ :=
  Real.logb 2 (sibsonZ alpha rho)

/-- Ordinary state mutual information in bits, with the actual two marginals; PDF p.15. -/
def ordinaryStateInfo {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (traceRight rho) + vnEntropy (traceLeft rho) - vnEntropy rho

/-- The positive-Choi CB 1-to-alpha quantity (not the p-to-p norm), PDF p.3, (2.1).
Used for complex-linear CP maps, without a trace-preserving condition. -/
def cbOneAlpha {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (alpha : ℝ) (M : Superop A B) : EReal :=
  ⨆ rho : NormalizedDensity A,
    let S := Matrix.kronecker (supportPower rho.1 (1 / (2 * alpha))) (1 : Matrix B B ℂ)
    (schatten alpha (S * choi M * S) : EReal)

/-- Endpoint sanity: zero success has zero exponential bound at negative infinity. -/
example : expBits ⊥ = 0 := by simp [expBits]

/-- Endpoint sanity: logarithm of zero is minus infinity, not a real default zero. -/
example : logExt 0 = ⊥ := by simp [logExt]

/-- The imported unnormalized Choi matrix of the identity has unit diagonal-pair entry. -/
example {A : Type} [DecidableEq A] (a : A) :
    choi (fun X : Matrix A A ℂ => X) (a,a) (a,a) = 1 := by
  simp [choi, Matrix.single_apply]

/-- Support failure is never erased by a zero-valued pseudoinverse. -/
example {I : Type} [Fintype I] [DecidableEq I] (alpha : ℝ) (ha : 1 < alpha)
    (rho sigma : Matrix I I ℂ) (h : ¬ SupportIncluded rho sigma) :
    sandwichedD alpha rho sigma = ⊤ := by simp [sandwichedD, ha, h]

end QAlgorithms.Papers.Independent.Intakenext100.P15


