-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07
-- name    : QAlgorithms_Papers_Independent_Support50_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-23T18:39:13.5857+00:00
-- url     : https://prove2.me/theorems/3a3f4ff2-dced-4f65-8f72-f646561e8351
-- title:
--   Definitions for The private classical capacity with a symmetric side channel and its application to quantum cryptography
-- statement:
--   The objects the formalized statements of *The private classical capacity with a symmetric side channel and its application to quantum cryptography* (arXiv:0705.3838) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `KeyCode`: PDF p.3: one-use code data for any block channel; arbitrary mixed messages and a POVM.
--   - `decodedJoint`: PDF p.3: joint uniform message, decoded classical message and full environment. The contraction Tr(M_j rho) is applied only to the receiverChannel block.
--   - `keyError`: PDF p.3: strict FULL trace norm, with the ACTUAL environment marginal and no factor 1/2.
--   - `FullTracePrivateAchievable`: PDF p.3: nonnegative unassisted achievable rates, all sufficiently large positive n, arbitrarily small errors and rate slacks. No public feedback or preshared resource. This full-trace-norm criterion differs from the accepted fidelity and leakage criteria.
--   - `fullTracePrivateCapacity`: PDF p.3: operational private capacity. On finite nonempty isometric channels the rate set contains zero and is bounded; no entropy formula is used in this definition. Distinct from Information100.P67.privateCapacity, whose error is infidelity.
--   - `assistedDilation`: PDF p.3: identity on two auxiliary factors, regrouped as BF and EG.
--   - `SymmetricSupport`: PDF p.3: support in A tensor the +1 SWAP eigenspace. Separate row and column invariance excludes the antisymmetric subspace (conjugation invariance alone would not).
--   - `SSPrivateAchievable`: PDF p.3: one arbitrary positive-dimensional free symmetric channel per block. Its mixed input states are represented after its isometric embedding into symmetric FG. Every density operator with this support is an allowed input to A_d, and conversely.
--   - `ssPrivateCapacity`: PDF p.3: operational ss-private capacity, with no charge for auxiliary dimension. For physical finite nonempty channels the rate set is nonempty and bounded independently of d.
--   - `ProcessedEnsemble`: PDF p.2: all finite normalized pure-signal ensembles and classical X-to-T channels. The alphabets and stochastic map are optimized, not quantum auxiliary registers.
--   - `processedState`: PDF p.2: the cq state of the processed classical variable T and a quantum output.
--   - `privateInformationValue`: PDF p.2: I(T;B)-I(T;E) for a particular ensemble and classical processing.
--   - `processedPrivateInformation`: PDF p.2: one-letter private information, optimized over ALL finite pure ensembles and stochastic postprocessings. Nonempty and bounded on physical nonzero systems. Distinct from Dependency50.P48.privateInformation U rho, a fixed-input quantity.
--   - `purificationCoherentInformation`: Theorem 2, PDF p.2: the equivalent pure-PURIFICATION variational expression. A reference copy of A suffices by Schmidt decomposition; this is not a pure-input restriction.
--   - `ssInformationValues`: Equation (3), PDF p.3: all symmetric pure AFG ensembles, unrestricted positive d.
--   - `ssPrivateInformation`: Equation (3), PDF p.3: C^(1)_(p,ss) as a variational quantity. Although the auxiliary dimension is unbounded, the value set is bounded for a fixed finite channel.
--   - `SymmetricInput`: PDF p.3: a basis label for the d(d+1)/2-dimensional symmetric input space.
--   - `symmetricSubspaceEmbedding`: PDF p.3: canonical isometry onto the symmetric subspace; diagonal basis vectors map to |ii>, off-diagonal ones to (|ij>+|ji>)/sqrt(2). Information100.P67.symmetricDilation instead composes two supplied dilations.
--   - `degradableMixingCosts`: Definition 10, PDF p.5: all costs of finite degradable/antidegradable mixtures, INCLUDING branchwise CPTP postprocessors and arbitrary positive intermediate dimensions.
--   - `degradableMixingCost`: Definition 10, PDF p.5: infimum cost. The identity branch followed by N makes the set nonempty, and each Q^(1) is nonnegative; hence no empty/unbounded infimum default.
--   - `pauliMatrices`: PDF pp.6–7: Pauli matrices in the computational basis, including the identity branch.
--   - `qubitPauliProbabilityChannel`: Theorem 12, PDF p.7: actual Pauli receiverChannel map; arguments are probabilities, not Kraus amplitudes. Validity is imposed by the theorem's full-simplex hypotheses. The frozen Frontier18.P17.pauliChannel takes a full Weyl probability array instead.
--   - `twoKrausChannel`: Section IV.A, PDF p.6: two-Kraus qubit family, with physical parameters in [0,1].
--   - `amplitudeDampingChannel`: Section IV.B, PDF p.6: standard amplitude damping, excited |1> decays to |0>.
--   - `qubitPhaseFlipChannel`: Section IV.A, PDF pp.6–7 and note [28]: Z dephasing with error probability p. Dependency50.P11.dephasingChannel fixes the fair p=1/2 channel, so cannot supply this family.
--   - `erasureMap`: Section IV.A, PDF p.6: genuine orthogonal erasure flag, linear on ALL operators.
--   - `independentPauliChannel`: Section IV.B, PDF p.6: independent X/Z-error probabilities; Y has probability q^2.
--   - `depolarizingChannel`: Section IV.C, PDF pp.6–7: depolarizing error probability is TOTAL Pauli error, so QBER = 2p/3.
--   - `twoKrausValue`: Section IV.A, PDF p.6: diagonal-input coherent information for the two-Kraus family.
--   - `dampingBound`: Section IV.B, PDF p.6: amplitude-damping scalar optimized on the compact interval. It includes t=0 with value zero. The capacity theorem also asserts attainment.
--   - `depolarizingDampingParameter`: Section IV.C, PDF p.6, checked on rendered page: only 1-p is under each square root.
--   - `depolarizingEnvelope`: Section IV.C, PDF pp.6,8: lower convex envelope on the physical depolarizing parameter interval [0,1]. Affinity of the receiverChannel map in p justifies this interpolation.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, https://arxiv.org/abs/0705.3838v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Support50.P07

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
    dilationPower idealJoint maximumCoherentInformation)
open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)
open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

/-! Source-specific definitions below are local to Smith, arXiv:0705.3838v1.
Accepted dilation and information primitives are imported. Private capacities
are operational suprema, not definitions by the formulas asserted as theorems.
Finite index types are used throughout; theorems require nonempty registers. -/

variable {A B E C D F : Type}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]
variable [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

/-- PDF p.3: one-use code data for any block channel; arbitrary mixed messages and a POVM. -/
structure KeyCode (I O : Type*) [Fintype I] [Fintype O] [DecidableEq O] where
  messages : ℕ
  positive : 0 < messages
  inputs : Fin messages → Matrix I I ℂ
  normalized : ∀ m, IsDensityMatrix (inputs m)
  measurement : Fin messages → Matrix O O ℂ
  povm : IsPOVM measurement

/-- PDF p.3: joint uniform message, decoded classical message and full environment.
The contraction Tr(M_j rho) is applied only to the receiverChannel block. -/
def decodedJoint (U : Matrix (B × E) A ℂ) (code : KeyCode A B) :
    Matrix (Fin code.messages × (Fin code.messages × E))
      (Fin code.messages × (Fin code.messages × E)) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.1 = j.2.1 then
    (code.messages : ℂ)⁻¹ *
      ∑ b, ∑ c, code.measurement i.2.1 c b *
        (U * code.inputs i.1 * Uᴴ) (b, i.2.2) (c, j.2.2)
    else 0

/-- PDF p.3: strict FULL trace norm, with the ACTUAL environment marginal and no factor 1/2. -/
def keyError (U : Matrix (B × E) A ℂ) (code : KeyCode A B) : ℝ :=
  let omega := decodedJoint U code
  traceNorm (omega - idealJoint code.messages (traceLeft (traceLeft omega)))

/-- PDF p.3: nonnegative unassisted achievable rates, all sufficiently large positive n,
arbitrarily small errors and rate slacks. No public feedback or preshared resource.
This full-trace-norm criterion differs from the accepted fidelity and leakage criteria. -/
def FullTracePrivateAchievable (U : Matrix (B × E) A ℂ) (rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∀ eps : ℝ, 0 < eps → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∃ code : KeyCode (Fin n → A) (Fin n → B),
        keyError (dilationPower U n) code < eps ∧
        rate - slack ≤ Real.logb 2 code.messages / (n : ℝ)

/-- PDF p.3: operational private capacity. On finite nonempty isometric channels the
rate set contains zero and is bounded; no entropy formula is used in this definition.
Distinct from Information100.P67.privateCapacity, whose error is infidelity. -/
def fullTracePrivateCapacity (U : Matrix (B × E) A ℂ) : ℝ :=
  sSup {r | FullTracePrivateAchievable U r}

/-- PDF p.3: identity on two auxiliary factors, regrouped as BF and EG. -/
def assistedDilation (U : Matrix (B × E) A ℂ) (d : ℕ) :
    Matrix ((B × Fin d) × (E × Fin d)) (A × (Fin d × Fin d)) ℂ :=
  fun be a => U (be.1.1, be.2.1) a.1 *
    if be.1.2 = a.2.1 ∧ be.2.2 = a.2.2 then 1 else 0

/-- PDF p.3: support in A tensor the +1 SWAP eigenspace. Separate row and column
invariance excludes the antisymmetric subspace (conjugation invariance alone would not). -/
def SymmetricSupport {d : ℕ}
    (rho : Matrix (A × (Fin d × Fin d)) (A × (Fin d × Fin d)) ℂ) : Prop :=
  (∀ a f g j, rho (a, (f, g)) j = rho (a, (g, f)) j) ∧
  (∀ i a f g, rho i (a, (f, g)) = rho i (a, (g, f)))

/-- PDF p.3: one arbitrary positive-dimensional free symmetric channel per block.
Its mixed input states are represented after its isometric embedding into symmetric FG.
Every density operator with this support is an allowed input to A_d, and conversely. -/
def SSPrivateAchievable (U : Matrix (B × E) A ℂ) (rate : ℝ) : Prop :=
  0 ≤ rate ∧ ∀ eps : ℝ, 0 < eps → ∀ slack : ℝ, 0 < slack →
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∃ d : ℕ, 0 < d ∧
      ∃ code : KeyCode ((Fin n → A) × (Fin d × Fin d)) ((Fin n → B) × Fin d),
        (∀ m, SymmetricSupport (code.inputs m)) ∧
        keyError (assistedDilation (dilationPower U n) d) code < eps ∧
        rate - slack ≤ Real.logb 2 code.messages / (n : ℝ)

/-- PDF p.3: operational ss-private capacity, with no charge for auxiliary dimension.
For physical finite nonempty channels the rate set is nonempty and bounded independently of d. -/
def ssPrivateCapacity (U : Matrix (B × E) A ℂ) : ℝ :=
  sSup {r | SSPrivateAchievable U r}

/-- PDF p.2: all finite normalized pure-signal ensembles and classical X-to-T channels.
The alphabets and stochastic map are optimized, not quantum auxiliary registers. -/
structure ProcessedEnsemble (I : Type*) [Fintype I] where
  xsize : ℕ
  tsize : ℕ
  xpositive : 0 < xsize
  tpositive : 0 < tsize
  weight : Fin xsize → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1
  signal : Fin xsize → EuclideanSpace ℂ I
  unit : ∀ x, ‖signal x‖ = 1
  processing : Fin xsize → Fin tsize → ℝ
  stochasticNonnegative : ∀ x t, 0 ≤ processing x t
  stochasticTotal : ∀ x, ∑ t, processing x t = 1

/-- PDF p.2: the cq state of the processed classical variable T and a quantum output. -/
def processedState (ens : ProcessedEnsemble A) (channel : Superop A B) :
    Matrix (Fin ens.tsize × B) (Fin ens.tsize × B) ℂ :=
  fun i j => if i.1 = j.1 then
    ∑ x, ((ens.weight x * ens.processing x i.1 : ℝ) : ℂ) *
      channel (pureDensity (ens.signal x)) i.2 j.2 else 0

/-- PDF p.2: I(T;B)-I(T;E) for a particular ensemble and classical processing. -/
def privateInformationValue (U : Matrix (B × E) A ℂ) (ens : ProcessedEnsemble A) : ℝ :=
  mutualInformation (processedState ens (receiverChannel U)) -
    mutualInformation (processedState ens (complementaryChannel U))

/-- PDF p.2: one-letter private information, optimized over ALL finite pure ensembles
and stochastic postprocessings. Nonempty and bounded on physical nonzero systems.
Distinct from Dependency50.P48.privateInformation U rho, a fixed-input quantity. -/
def processedPrivateInformation (U : Matrix (B × E) A ℂ) : ℝ :=
  sSup {r | ∃ ens : ProcessedEnsemble A, r = privateInformationValue U ens}

/-- Theorem 2, PDF p.2: the equivalent pure-PURIFICATION variational expression.
A reference copy of A suffices by Schmidt decomposition; this is not a pure-input restriction. -/
def purificationCoherentInformation (U : Matrix (B × E) A ℂ) : ℝ :=
  sSup {r | ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧
    let rho := idTensorSuperop (R := A) (receiverChannel U) (pureDensity psi)
    r = vnEntropy (traceLeft rho) - vnEntropy rho}

/-- Equation (3), PDF p.3: all symmetric pure AFG ensembles, unrestricted positive d. -/
def ssInformationValues (U : Matrix (B × E) A ℂ) : Set ℝ :=
  {r | ∃ d : ℕ, 0 < d ∧ ∃ ens : ProcessedEnsemble (A × (Fin d × Fin d)),
    (∀ x a f g, ens.signal x (a, (f, g)) = ens.signal x (a, (g, f))) ∧
    r = privateInformationValue (assistedDilation U d) ens}

/-- Equation (3), PDF p.3: C^(1)_(p,ss) as a variational quantity. Although the
auxiliary dimension is unbounded, the value set is bounded for a fixed finite channel. -/
def ssPrivateInformation (U : Matrix (B × E) A ℂ) : ℝ :=
  sSup (ssInformationValues U)

/-- PDF p.3: a basis label for the d(d+1)/2-dimensional symmetric input space. -/
abbrev SymmetricInput (d : ℕ) := {ij : Fin d × Fin d // ij.1 ≤ ij.2}

/-- PDF p.3: canonical isometry onto the symmetric subspace; diagonal basis vectors
map to |ii>, off-diagonal ones to (|ij>+|ji>)/sqrt(2).
Information100.P67.symmetricDilation instead composes two supplied dilations. -/
def symmetricSubspaceEmbedding (d : ℕ) : Matrix (Fin d × Fin d) (SymmetricInput d) ℂ :=
  fun fg ij => if ij.val.1 = ij.val.2 then
    if fg = ij.val then 1 else 0
  else if fg = ij.val ∨ fg = (ij.val.2, ij.val.1) then
    ((Real.sqrt 2)⁻¹ : ℝ) else 0

/-- Definition 10, PDF p.5: all costs of finite degradable/antidegradable mixtures,
INCLUDING branchwise CPTP postprocessors and arbitrary positive intermediate dimensions. -/
def degradableMixingCosts (U : Matrix (B × E) A ℂ) : Set ℝ :=
  {r | ∃ k : ℕ, 0 < k ∧ ∃ p : Fin k → ℝ,
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
    ∃ bo eo : Fin k → ℕ, (∀ i, 0 < bo i ∧ 0 < eo i) ∧
    ∃ v : (i : Fin k) → Matrix (Fin (bo i) × Fin (eo i)) A ℂ,
    ∃ post : (i : Fin k) → Superop (Fin (bo i)) B,
    (∀ i, IsIsometry (v i) ∧ (IsDegradable (v i) ∨ IsAntidegradable (v i)) ∧
      IsChannel (post i)) ∧
    (∀ rho, receiverChannel U rho = ∑ i, (p i : ℂ) • post i (receiverChannel (v i) rho)) ∧
    r = ∑ i, p i * maximumCoherentInformation (v i)}

/-- Definition 10, PDF p.5: infimum cost. The identity branch followed by N makes the
set nonempty, and each Q^(1) is nonnegative; hence no empty/unbounded infimum default. -/
def degradableMixingCost (U : Matrix (B × E) A ℂ) : ℝ :=
  sInf (degradableMixingCosts U)

/-- PDF pp.6–7: Pauli matrices in the computational basis, including the identity branch. -/
def pauliMatrices : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- Theorem 12, PDF p.7: actual Pauli receiverChannel map; arguments are probabilities,
not Kraus amplitudes. Validity is imposed by the theorem's full-simplex hypotheses.
The frozen Frontier18.P17.pauliChannel takes a full Weyl probability array instead. -/
def qubitPauliProbabilityChannel (p : Fin 3 → ℝ) : Superop (Fin 2) (Fin 2) :=
  fun rho => ((1 - ∑ i, p i : ℝ) : ℂ) • rho +
    ∑ i : Fin 3, (p i : ℂ) •
      (pauliMatrices (Fin.succ i) * rho * (pauliMatrices (Fin.succ i))ᴴ)

/-- Section IV.A, PDF p.6: two-Kraus qubit family, with physical parameters in [0,1]. -/
def twoKrausChannel (gamma delta : ℝ) : Superop (Fin 2) (Fin 2) :=
  krausApply ![!![(Real.sqrt (1 - gamma) : ℂ), 0; 0, (Real.sqrt (1 - delta) : ℂ)],
    !![0, (Real.sqrt delta : ℂ); (Real.sqrt gamma : ℂ), 0]]

/-- Section IV.B, PDF p.6: standard amplitude damping, excited |1> decays to |0>. -/
def amplitudeDampingChannel (gamma : ℝ) : Superop (Fin 2) (Fin 2) :=
  twoKrausChannel 0 gamma

/-- Section IV.A, PDF pp.6–7 and note [28]: Z dephasing with error probability p.
Dependency50.P11.dephasingChannel fixes the fair p=1/2 channel, so cannot supply this family. -/
def qubitPhaseFlipChannel (p : ℝ) : Superop (Fin 2) (Fin 2) :=
  fun rho => ((1 - p : ℝ) : ℂ) • rho + (p : ℂ) •
    (pauliMatrices 3 * rho * (pauliMatrices 3)ᴴ)

/-- Section IV.A, PDF p.6: genuine orthogonal erasure flag, linear on ALL operators. -/
def erasureMap (d : ℕ) (p : ℝ) : Superop (Fin d) (Option (Fin d)) :=
  fun rho i j => match i, j with
    | some a, some b => ((1 - p : ℝ) : ℂ) * rho a b
    | none, none => (p : ℂ) * rho.trace
    | _, _ => 0

/-- Section IV.B, PDF p.6: independent X/Z-error probabilities; Y has probability q^2. -/
def independentPauliChannel (q : ℝ) : Superop (Fin 2) (Fin 2) :=
  qubitPauliProbabilityChannel ![q * (1 - q), q ^ 2, q * (1 - q)]

/-- Section IV.C, PDF pp.6–7: depolarizing error probability is TOTAL Pauli error,
so QBER = 2p/3. -/
def depolarizingChannel (p : ℝ) : Superop (Fin 2) (Fin 2) :=
  qubitPauliProbabilityChannel (fun _ => p / 3)

/-- Section IV.A, PDF p.6: diagonal-input coherent information for the two-Kraus family. -/
def twoKrausValue (gamma delta t : ℝ) : ℝ :=
  binEntropy2 (t * (1 - gamma) + (1 - t) * delta) -
    binEntropy2 (t * gamma + (1 - t) * delta)

/-- Section IV.B, PDF p.6: amplitude-damping scalar optimized on the compact interval.
It includes t=0 with value zero. The capacity theorem also asserts attainment. -/
def dampingBound (gamma : ℝ) : ℝ :=
  sSup {r | ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧
    r = binEntropy2 (t * (1 - gamma)) - binEntropy2 (t * gamma)}

/-- Section IV.C, PDF p.6, checked on rendered page: only 1-p is under each square root. -/
def depolarizingDampingParameter (p : ℝ) : ℝ :=
  4 * Real.sqrt (1 - p) * (1 - Real.sqrt (1 - p))

/-- Section IV.C, PDF pp.6,8: lower convex envelope on the physical depolarizing
parameter interval [0,1]. Affinity of the receiverChannel map in p justifies this interpolation. -/
def depolarizingEnvelope (p : ℝ) : ℝ :=
  sInf {r | ∃ k : ℕ, 0 < k ∧ ∃ w x : Fin k → ℝ,
    (∀ i, 0 ≤ w i ∧ x i ∈ Set.Icc 0 1) ∧ (∑ i, w i = 1) ∧
    (∑ i, w i * x i = p) ∧
    r = ∑ i, w i * min (1 - binEntropy2 (x i))
      (min (dampingBound (depolarizingDampingParameter (x i))) (max (1 - 4 * x i) 0))}

/-! Sanity checks of local conventions; these are not proofs of the paper's results. -/

example (U : Matrix (B × E) A ℂ) (be : (Fin 0 → B) × (Fin 0 → E))
    (a : Fin 0 → A) : dilationPower U 0 be a = 1 := by
  simp [dilationPower]

example (U : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) :
    receiverChannel U rho = traceRight (U * rho * Uᴴ) := rfl

example (U : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) :
    complementaryChannel U rho = traceLeft (U * rho * Uᴴ) := rfl

example (m : ℕ) (sigma : Matrix E E ℂ) (i : Fin m) (e f : E) :
    idealJoint m sigma (i, (i, e)) (i, (i, f)) = (m : ℂ)⁻¹ * sigma e f := by
  simp [idealJoint]

example : symmetricSubspaceEmbedding 1 (0, 0) ⟨(0, 0), le_refl _⟩ = 1 := by
  simp [symmetricSubspaceEmbedding]

example : depolarizingDampingParameter 0 = 0 := by
  norm_num [depolarizingDampingParameter]

example : pauliMatrices 1 0 1 = 1 ∧ pauliMatrices 2 0 1 = -Complex.I := by
  constructor <;> rfl

example (q : ℝ) : independentPauliChannel q =
    qubitPauliProbabilityChannel ![q * (1 - q), q ^ 2, q * (1 - q)] := rfl

end QAlgorithms.Papers.Independent.Support50.P07


