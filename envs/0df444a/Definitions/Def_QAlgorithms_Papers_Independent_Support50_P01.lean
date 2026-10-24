-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01
-- name    : QAlgorithms_Papers_Independent_Support50_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T18:05:57.126386+00:00
-- url     : https://prove2.me/theorems/8ba685b0-818d-4bf1-b1b3-cea2903991f1
-- title:
--   Definitions for Conjugate Degradability and the Quantum Capacity of Cloning Channels
-- statement:
--   The objects the formalized statements of *Conjugate Degradability and the Quantum Capacity of Cloning Channels* (arXiv:0909.3297) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ConjugateDegradable`: PDF p.4, Eq.(2): a single CPTP witness, on all input operators. Transpose is the complex-linear extension of conjugation on density matrices.
--   - `ConjugateAntidegradable`: PDF p.4, Eq.(3): one CPTP antidegrading witness, independent of the input.
--   - `blockCoherentInformation`: PDF p.3, Eq.(1): n-use coherent information from the full tensor dilation.
--   - `partialTransposeOutput`: PDF p.5: partial transpose of the channel output (reference is first).
--   - `ConjugateAntiChannel`: PDF pp.13–14: channel-level conjugate antidegradability. Each channel may have its own environment dimension and witness. This includes CPTP, via its dilation.
--   - `cloningCoefficient`: PDF p.10, Eq.(22): squared occupation-basis cloning amplitude. All uses carry 1 ≤ N ≤ M and indices in their stated ranges.
--   - `clonerDilation`: PDF p.10, Eqs.(21),(22): the specified optimal universal qubit cloner, on the complete normalized occupation basis of Sym^N(C²), with symmetric receiver and minimal environment coordinates. No property of an arbitrary equal-marginal map is substituted for this concrete construction.
--   - `cloningAlpha`: PDF pp.16–17, Eqs.(47),(50): alpha is the squared amplitude, padded by zero ONLY outside 0,...,M-N. This also sets alpha_(M-N+1)=0 as prescribed.
--   - `cloningBeta`: PDF p.17, Eq.(50): scalar beta coefficients; no inconsistent physical ket from Eq.(46) is used to define these vectors.
--   - `CloningMajorizes`: PDF p.17: ordinary majorization for already decreasing vectors: prefix inequalities AND equal total sums, here with both probability normalizations.
--   - `unruhWeight`: PDF p.7, Eqs.(11)–(13): the fixed probability of sector k.
--   - `unruhSectorDilation`: PDF p.7, Eq.(12), and p.10, Eqs.(21),(22) with N=1,M=k+1: common normalized sector isometry, receiver dimension k+2, environment k+1. The positive square roots fix the occupation-basis phases.
--   - `unruhBlockDilation`: PDF p.7: full positive-block-length sector dilation. Sector labels are independent of the input, and the input can be entangled across every use.
--   - `unruhBlockWeight`: PDF p.7, Eq.(11): product of the fixed sector weights for memoryless uses.
--   - `unruhReceiverBlock`: PDF p.7: subnormalized receiver block of the full flagged channel, with all off-diagonal input matrix entries retained.
--   - `unruhEnvironmentBlock`: PDF p.7: genuine complement blocks from the very same sector isometries and weights. Both parties receive the common classical sector flag.
--   - `UnruhReceiverIndex`: PDF p.7: countable receiver direct sum, not a truncated register.
--   - `UnruhEnvironmentIndex`: PDF p.7: countable environment direct sum.
--   - `unruhDilation`: PDF pp.2–3,7: the COMMON countable Stinespring dilation, in coordinates. Both sector flags agree. Its coefficient is sqrt(product weight) times the sector tensor isometry; 0<z<1 ensures summability and normalization.
--   - `unruhReceiver`: PDF p.7, Eq.(11): full receiver matrix on the countable direct sum. Different sector flags have zero coherence, without removing input coherence.
--   - `unruhComplement`: PDF p.7: full complementary matrix, with the same countable flag.
--   - `unruhReceiverEntropy`: PDF p.7: entropy of the full receiver direct sum, from subnormalized finite blocks; includes the sector Shannon entropy. Convergence is a conclusion.
--   - `unruhEnvironmentEntropy`: PDF p.7: entropy of the true full complement, including its flags.
--   - `unruhCoherentInformation`: PDF pp.3,7: full infinite-output block coherent information.
--   - `unruhCapacity`: PDF pp.3,7: full regularized optimized information, over arbitrary entangled density matrices at every positive block length. No energy bound or finite-cutoff replacement. For 0<z<1 the entropy sums converge and rates are bounded.
--   - `unruhSeriesTerm`: PDF p.7: capacity series in bits, before the printed polylogarithm formula.
--   - `unruhMixedInput`: PDF p.7: I/2 on one use, in the tensor-coordinate convention.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, https://arxiv.org/abs/0909.3297v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P40

/-!
Statements from Bradler–Dutil–Hayden–Muhammad, arXiv:0909.3297v1.
Page numbers below are PDF pages. All entropies are in bits.
The three source-level deferrals are recorded in the unit HARD.md.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)
open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)
open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)
open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF p.4, Eq.(2): a single CPTP witness, on all input operators.
Transpose is the complex-linear extension of conjugation on density matrices. -/
def ConjugateDegradable (U : Matrix (Fin b × Fin e) (Fin a) ℂ) : Prop :=
  Uᴴ * U = 1 ∧ ∃ D : Superop (Fin b) (Fin e), IsChannel D ∧
    ∀ X, D (receiverChannel U X) = (complementaryChannel U X)ᵀ

/-- PDF p.4, Eq.(3): one CPTP antidegrading witness, independent of the input. -/
def ConjugateAntidegradable (U : Matrix (Fin b × Fin e) (Fin a) ℂ) : Prop :=
  Uᴴ * U = 1 ∧ ∃ D : Superop (Fin e) (Fin b), IsChannel D ∧
    ∀ X, D (complementaryChannel U X) = (receiverChannel U X)ᵀ

/-- PDF p.3, Eq.(1): n-use coherent information from the full tensor dilation. -/
def blockCoherentInformation (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (n : ℕ)
    (rho : Matrix (Fin n → Fin a) (Fin n → Fin a) ℂ) : ℝ :=
  let tau := dilationPower U n * rho * (dilationPower U n)ᴴ
  vnEntropy (traceRight tau) - vnEntropy (traceLeft tau)

/-- PDF p.5: partial transpose of the channel output (reference is first). -/
def partialTransposeOutput {r d : ℕ}
    (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) :
    Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ :=
  fun p q => X (p.1,q.2) (q.1,p.2)

/-- PDF pp.13–14: channel-level conjugate antidegradability. Each channel may have
its own environment dimension and witness. This includes CPTP, via its dilation. -/
def ConjugateAntiChannel (Phi : Superop (Fin a) (Fin b)) : Prop :=
  ∃ e : ℕ, 0 < e ∧ ∃ U : Matrix (Fin b × Fin e) (Fin a) ℂ,
    ConjugateAntidegradable U ∧ receiverChannel U = Phi

/-- PDF p.10, Eq.(22): squared occupation-basis cloning amplitude.
All uses carry 1 ≤ N ≤ M and indices in their stated ranges. -/
def cloningCoefficient (N M k j : ℕ) : ℝ :=
  ((Nat.factorial (M-N) : ℝ) * Nat.factorial (N+1) *
    Nat.factorial (k+j) * Nat.factorial (M-k-j)) /
  ((Nat.factorial k : ℝ) * Nat.factorial (N-k) * Nat.factorial (M+1) *
    Nat.factorial j * Nat.factorial (M-N-j))

/-- PDF p.10, Eqs.(21),(22): the specified optimal universal qubit cloner,
on the complete normalized occupation basis of Sym^N(C²), with symmetric receiver
and minimal environment coordinates. No property of an arbitrary equal-marginal map
is substituted for this concrete construction. -/
def clonerDilation (N M : ℕ) :
    Matrix (Fin (M+1) × Fin (M-N+1)) (Fin (N+1)) ℂ :=
  fun bj k => if bj.1.val = k.val + bj.2.val then
    (Real.sqrt (cloningCoefficient N M k.val bj.2.val) : ℂ) else 0

/-- PDF pp.16–17, Eqs.(47),(50): alpha is the squared amplitude, padded by zero
ONLY outside 0,...,M-N. This also sets alpha_(M-N+1)=0 as prescribed. -/
def cloningAlpha (N M j : ℕ) : ℝ :=
  if j ≤ M-N then
    ((N+1 : ℕ) : ℝ) / (M+1) *
      ((Nat.factorial (M-N) : ℝ) * Nat.factorial (M-j)) /
      ((Nat.factorial (M-N-j) : ℝ) * Nat.factorial M)
  else 0

/-- PDF p.17, Eq.(50): scalar beta coefficients; no inconsistent physical ket
from Eq.(46) is used to define these vectors. -/
def cloningBeta (N M j : ℕ) : ℝ :=
  cloningAlpha N M j * ((M-j : ℕ) : ℝ) / M + cloningAlpha N M (j+1) * (j+1) / M

/-- PDF p.17: ordinary majorization for already decreasing vectors: prefix
inequalities AND equal total sums, here with both probability normalizations. -/
def CloningMajorizes (N M : ℕ) : Prop :=
  (∀ j ≤ M-N, 0 ≤ cloningAlpha N M j ∧ 0 ≤ cloningBeta N M j) ∧
  (∀ j < M-N, cloningAlpha N M (j+1) ≤ cloningAlpha N M j ∧
    cloningBeta N M (j+1) ≤ cloningBeta N M j) ∧
  (∀ k ≤ M-N+1,
    (∑ j ∈ Finset.range k, cloningAlpha N M j) ≤ ∑ j ∈ Finset.range k, cloningBeta N M j) ∧
  (∑ j ∈ Finset.range (M-N+1), cloningAlpha N M j) = 1 ∧
  (∑ j ∈ Finset.range (M-N+1), cloningBeta N M j) = 1

/-- PDF p.7, Eqs.(11)–(13): the fixed probability of sector k. -/
def unruhWeight (z : ℝ) (k : ℕ) : ℝ :=
  (1-z)^3 * z^k * (k+1) * (k+2) / 2

/-- PDF p.7, Eq.(12), and p.10, Eqs.(21),(22) with N=1,M=k+1:
common normalized sector isometry, receiver dimension k+2, environment k+1.
The positive square roots fix the occupation-basis phases. -/
def unruhSectorDilation (k : ℕ) :
    Matrix (Fin (k+2) × Fin (k+1)) (Fin 2) ℂ :=
  fun bj x => if bj.1.val = x.val + bj.2.val then
    (Real.sqrt (2 * (if x.val = 0 then ((k+1-bj.2.val : ℕ) : ℝ)
      else (bj.2.val+1 : ℕ)) / ((k+1 : ℝ)*(k+2))) : ℂ) else 0

/-- PDF p.7: full positive-block-length sector dilation. Sector labels are
independent of the input, and the input can be entangled across every use. -/
def unruhBlockDilation {n : ℕ} (ks : Fin n → ℕ) :
    Matrix (((i : Fin n) → Fin (ks i+2)) × ((i : Fin n) → Fin (ks i+1)))
      (Fin n → Fin 2) ℂ :=
  fun bj x => ∏ i, unruhSectorDilation (ks i) (bj.1 i,bj.2 i) (x i)

/-- PDF p.7, Eq.(11): product of the fixed sector weights for memoryless uses. -/
def unruhBlockWeight {n : ℕ} (z : ℝ) (ks : Fin n → ℕ) : ℝ :=
  ∏ i, unruhWeight z (ks i)

/-- PDF p.7: subnormalized receiver block of the full flagged channel, with
all off-diagonal input matrix entries retained. -/
def unruhReceiverBlock {n : ℕ} (z : ℝ) (ks : Fin n → ℕ)
    (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix ((i : Fin n) → Fin (ks i+2)) ((i : Fin n) → Fin (ks i+2)) ℂ :=
  (unruhBlockWeight z ks : ℂ) •
    traceRight (unruhBlockDilation ks * rho * (unruhBlockDilation ks)ᴴ)

/-- PDF p.7: genuine complement blocks from the very same sector isometries
and weights. Both parties receive the common classical sector flag. -/
def unruhEnvironmentBlock {n : ℕ} (z : ℝ) (ks : Fin n → ℕ)
    (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix ((i : Fin n) → Fin (ks i+1)) ((i : Fin n) → Fin (ks i+1)) ℂ :=
  (unruhBlockWeight z ks : ℂ) •
    traceLeft (unruhBlockDilation ks * rho * (unruhBlockDilation ks)ᴴ)

/-- PDF p.7: countable receiver direct sum, not a truncated register. -/
abbrev UnruhReceiverIndex (n : ℕ) :=
  Sigma fun ks : Fin n → ℕ => (i : Fin n) → Fin (ks i+2)

/-- PDF p.7: countable environment direct sum. -/
abbrev UnruhEnvironmentIndex (n : ℕ) :=
  Sigma fun ks : Fin n → ℕ => (i : Fin n) → Fin (ks i+1)

/-- PDF pp.2–3,7: the COMMON countable Stinespring dilation, in coordinates.
Both sector flags agree. Its coefficient is sqrt(product weight) times the
sector tensor isometry; 0<z<1 ensures summability and normalization. -/
def unruhDilation (z : ℝ) (n : ℕ) :
    Matrix (UnruhReceiverIndex n × UnruhEnvironmentIndex n) (Fin n → Fin 2) ℂ :=
  fun be x => if h : be.1.1 = be.2.1 then
    (Real.sqrt (unruhBlockWeight z be.1.1) : ℂ) *
      unruhBlockDilation be.1.1 (be.1.2, h.symm ▸ be.2.2) x else 0

/-- PDF p.7, Eq.(11): full receiver matrix on the countable direct sum.
Different sector flags have zero coherence, without removing input coherence. -/
def unruhReceiver {n : ℕ} (z : ℝ)
    (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (UnruhReceiverIndex n) (UnruhReceiverIndex n) ℂ :=
  fun p q => if h : p.1 = q.1 then
    unruhReceiverBlock z p.1 rho p.2 (h.symm ▸ q.2) else 0

/-- PDF p.7: full complementary matrix, with the same countable flag. -/
def unruhComplement {n : ℕ} (z : ℝ)
    (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Matrix (UnruhEnvironmentIndex n) (UnruhEnvironmentIndex n) ℂ :=
  fun p q => if h : p.1 = q.1 then
    unruhEnvironmentBlock z p.1 rho p.2 (h.symm ▸ q.2) else 0

/-- PDF p.7: entropy of the full receiver direct sum, from subnormalized
finite blocks; includes the sector Shannon entropy. Convergence is a conclusion. -/
def unruhReceiverEntropy {n : ℕ} (z : ℝ)
    (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  ∑' ks : Fin n → ℕ, vnEntropy (unruhReceiverBlock z ks rho)

/-- PDF p.7: entropy of the true full complement, including its flags. -/
def unruhEnvironmentEntropy {n : ℕ} (z : ℝ)
    (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  ∑' ks : Fin n → ℕ, vnEntropy (unruhEnvironmentBlock z ks rho)

/-- PDF pp.3,7: full infinite-output block coherent information. -/
def unruhCoherentInformation {n : ℕ} (z : ℝ)
    (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  unruhReceiverEntropy z rho - unruhEnvironmentEntropy z rho

/-- PDF pp.3,7: full regularized optimized information, over arbitrary
entangled density matrices at every positive block length. No energy bound or
finite-cutoff replacement. For 0<z<1 the entropy sums converge and rates are bounded. -/
def unruhCapacity (z : ℝ) : ℝ :=
  sSup {v | ∃ n : ℕ, 0 < n ∧
    ∃ rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      IsDensityMatrix rho ∧ v = unruhCoherentInformation z rho / (n : ℝ)}

/-- PDF p.7: capacity series in bits, before the printed polylogarithm formula. -/
def unruhSeriesTerm (z : ℝ) (k : ℕ) : ℝ :=
  unruhWeight z k * (Real.logb 2 (k+2) - Real.logb 2 (k+1))

/-- PDF p.7: I/2 on one use, in the tensor-coordinate convention. -/
def unruhMixedInput : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  (2 : ℂ)⁻¹ • 1

/-- Occupation coefficients pin the 1→2 normalization, PDF pp.10,16–17. -/
example : cloningCoefficient 1 2 0 0 = 2/3 ∧ cloningAlpha 1 2 0 = 2/3 ∧
    cloningBeta 1 2 0 = 5/6 := by
  norm_num [cloningCoefficient, cloningAlpha, cloningBeta, Nat.factorial]

/-- Identity-cloner boundary, PDF pp.8–10; N=M=1 has no adjacent coefficient pair. -/
example : cloningCoefficient 1 1 0 0 = 1 ∧ cloningAlpha 1 1 0 = 1 ∧ cloningBeta 1 1 0 = 1 := by
  norm_num [cloningCoefficient, cloningAlpha, cloningBeta, Nat.factorial]

/-- At z=0 the sector weights have only the k=0 identity sector, PDF p.7. -/
example : unruhWeight 0 0 = 1 ∧ unruhWeight 0 1 = 0 := by
  norm_num [unruhWeight]

/-- The k=0 sector transmits the computational basis state 0 exactly, PDF p.7. -/
example : unruhSectorDilation 0 (0,0) 0 = 1 := by
  norm_num [unruhSectorDilation]

/-- Partial transpose is an involution, PDF p.5. -/
example {r d : ℕ} (X : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) :
    partialTransposeOutput (partialTransposeOutput X) = X := rfl

/-- The common-dilation maps are linear at zero, PDF pp.2–3. Zero is not a state. -/
example (U : Matrix (Fin b × Fin e) (Fin a) ℂ) :
    receiverChannel U 0 = 0 ∧ complementaryChannel U 0 = 0 := by
  constructor <;> ext i j <;>
    simp [receiverChannel, complementaryChannel, traceRight, traceLeft]

/-- The one-dimensional maximally mixed state is the identity, PDF pp.10–11. -/
example : maximallyMixed 1 = 1 := by
  simp [maximallyMixed]

/-- The empty tensor convention is one; zero-length blocks are excluded from rates, PDF p.3. -/
example (z : ℝ) : unruhBlockWeight (n := 0) z Fin.elim0 = 1 := by
  simp [unruhBlockWeight]

/-- Distinct sector flags are incoherent in the full receiver, PDF p.7, Eq.(11). -/
example {n : ℕ} (z : ℝ) (rho : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (p q : UnruhReceiverIndex n) (h : p.1 ≠ q.1) :
    unruhReceiver z rho p q = 0 := by
  simp [unruhReceiver, h]

/-- The full common dilation requires both parties to have the same flag, PDF p.7. -/
example (z : ℝ) (n : ℕ) (be : UnruhReceiverIndex n × UnruhEnvironmentIndex n)
    (x : Fin n → Fin 2) (h : be.1.1 ≠ be.2.1) :
    unruhDilation z n be x = 0 := by
  simp [unruhDilation, h]

end QAlgorithms.Papers.Independent.Support50.P01


