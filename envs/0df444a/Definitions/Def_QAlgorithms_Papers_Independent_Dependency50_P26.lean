-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
-- name    : QAlgorithms_Papers_Independent_Dependency50_P26
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:24:58.42431+00:00
-- url     : https://prove2.me/theorems/7194fd7c-7438-49f7-867b-d814b16f2324
-- title:
--   Definitions for Theoretical framework for quantum networks
-- statement:
--   The objects the formalized statements of *Theoretical framework for quantum networks* (arXiv:0904.4483) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `outputFirstChoi`: PDF pp.2–3, Eq.(2): transport the accepted unnormalized Choi operator from input-first to output-first wire order; no normalization change.
--   - `TracePreserving`: PDF p.2: trace preservation on all operators, without a positivity assumption.
--   - `HermitianPreserving`: PDF p.2: Hermitian preservation on every Hermitian operator.
--   - `channelLink`: PDF p.3, Eqs.(12)–(13): link of two channel-shaped operators through their common wire.
--   - `Signature`: PDF pp.5–7: ordered pairs of external input and output wires, all of positive dimension.
--   - `Basis`: PDF pp.6–7: the restricted prefix tensor space, ordered newest output/input first.
--   - `Normalized`: PDF p.7, Eq.(25): recursive positive normalized prefixes; the scalar prefix is 1.
--   - `AffineNormalized`: PDF p.12: the affine trace constraints, independently of the positive cone.
--   - `slots`: PDF pp.10–11: the inner slot of an (N+1)-comb has wire roles shifted by one.
--   - `insertEndpoints`: PDF p.11, Eq.(42): place external endpoints around an inner-slot basis vector.
--   - `slotAction`: PDF p.11, Eq.(42), and p.16, Eq.(64): contraction with the transposed inner comb.
--   - `ChannelChoi`: PDF p.4, Eq.(18): positive, trace-preserving Choi operators.
--   - `Deterministic`: PDF pp.10–11, Definitions 3–4: deterministic combs defined by their action on inner combs. The base is a channel. Positivity is the CP Choi condition of Lemma 3, not a normalization hypothesis. This predicate is independent of Normalized. Order zero is excluded.
--   - `Probabilistic`: PDF p.10, Definition 4: a probabilistic comb is positive and PSD-dominated by a normalized deterministic comb. Normalized is the equivalent Eq.(40) presentation.
--   - `rankOne`: PDF pp.2,16: an unnormalized rank-one Choi operator. Zero vectors are allowed.
--   - `MemoryNetwork`: PDF pp.5–7: a sequential memory network of finite-dimensional CPTP channels. Only the first N vertices are used at order N. Each vertex has its own label.
--   - `MemoryNetwork.retained`: PDF p.6, Eq.(21): explicit circuit contraction, retaining the current internal memory.
--   - `MemoryNetwork.choi`: PDF p.6, Eq.(21): the Choi operator after discarding the last memory.
--   - `IsometricNetwork`: PDF p.7, Fig.3: a sequence of isometries, with one-dimensional initial memory.
--   - `IsometricNetwork.amplitude`: PDF p.7: amplitudes of the contracted isometries before tracing the final memory.
--   - `IsometricNetwork.choi`: PDF p.7, Fig.3: final memory is traced, rather than postselected.
--   - `MeasuredRealization`: PDF p.8, Theorem 4: a common isometric realization with a k-dimensional measured factor. The residual memory dimension r is unrestricted and is discarded. The equivalence fixes the computational measurement basis; arbitrary bases can be absorbed in the last interaction.
--   - `CombInstrument`: PDF p.16, Definition 10: finite-outcome generalized comb instrument. This is a predicate on multi-tooth Choi branches, distinct from a one-use Kraus instrument.
--   - `OperationChoi`: PDF pp.4,16: quantum-operation Choi operators, with a CPTP completion.
--   - `CombTester`: PDF p.17, Definition 11: positivity and pointwise normalization on every deterministic comb. This multi-outcome comb tester is distinct from a parallel channel tester with one effect.
--   - `ThetaNormalized`: PDF p.17, Eq.(67), corrected using Lemma 8 and Eq.(25): Θ has the last input and all previous teeth. Trace out that last input, then recurse; the final scalar trace is 1.
--   - `InformationallyComplete`: PDF p.19, Definition 13: spanning the full complex operator space, with transposed effects.
--   - `DeterministicSpan`: PDF p.20, Definition 14: D is the actual complex span of deterministic combs. The erroneous printed single-trace characterization of D is not used.
--   - `CompleteForDeterministic`: PDF p.20, Definition 14: completeness on D, rather than the whole operator space.
--   - `POVM`: PDF pp.4,17: a finite nonempty POVM on the displayed space.
--   - `spectral`: PDF pp.17–20: spectral functional calculus on a Hermitian operator. The fallback is used only off the stated PSD/Hermitian domains.
--   - `matrixSqrt`: PDF p.17, Eqs.(68)–(69): positive spectral square root.
--   - `inputDimension`: PDF p.19, Eq.(89): in zero-based wire labels the denominator is the input-dimension product.
--   - `externalProbability`: PDF p.9, Eq.(38): fully contract an external experiment with a network's Choi operator, including a probabilistic branch. This entrywise tensor contraction is independent of the trace-form Born definition.
--   - `multiTimeVector`: PDF p.20, Eq.(92): the multiple-time vector in the fixed wire order. prep j is |Ψ_j⟩ and post j is |Φ_(j+1)⟩; postselection is complex conjugated. This tensor product is unrelated to the Dyson ODE history-state construction.
--   - `conditionalBorn`: PDF p.20, Eqs.(93)–(94): conditional probability, only asserted with positive total weight.
--   - `partialLink`: PDF p.3, Eq.(14): general link after grouping exclusive and common wire factors. X and Y are the exclusive tensor factors and J is the entire common tensor factor. An empty group of wire labels is represented by a one-dimensional type.
--   - `regroup`: PDF p.3: regroup tensor factors through the displayed basis map.
--   - `linkRightNested`: PDF p.3, Theorem 2(2): M1*(M2*M3), grouped onto A⊗B⊗C. AB, AC and BC label the three pairwise intersections; there is no triple intersection.
--   - `linkLeftNested`: PDF p.3, Theorem 2(2): (M1*M2)*M3, with exactly the same external factor order.
--   - `TotalNormalized`: PDF p.19, Eq.(82): the full feasible normalization set, with every recursive constraint.
--   - `coherentSandwich`: PDF pp.17,19, Eqs.(68),(81): transposed-root sandwich, in the fixed complex basis.
--   - `combDistance`: PDF p.19, Eq.(82): half the maximal trace norm over causally normalized testers. The source's finite-dimensional feasible set is nonempty and compact at positive order.
--   - `cbDistance`: PDF p.19, Eq.(83): cb/diamond distance with the source's factor 1/2 and arbitrary positive finite ancilla dimension. This is not identified with the library's unhalved norm.
--   - `InputBasis`: PDF p.7, Eq.(26): basis for all external input wires.
--   - `OutputBasis`: PDF p.7, Eq.(26): basis for all external output wires.
--   - `interleave`: PDF p.7, Eq.(26): interleave the parallel input/output registers into the comb basis.
--   - `parallelMap`: PDF pp.2,7: the multipartite map constructed from its Choi operator, Eq.(3).
--   - `discriminationError`: PDF p.18, Eq.(77): average error with both possible zero priors permitted.
--   - `pseudoInverse`: PDF pp.17–18: Moore–Penrose inverse, with eigenvalue zero mapped to zero.
--   - `oneInputLift`: PDF p.18: I_out tensor A_in on the one-tooth comb basis, including the scalar prefix.
--   - `onePurifiedOutput`: PDF p.18, Eq.(76): (C⊗id)(|sqrt σ⟩⟩⟨⟨sqrt σ|), computed from C's Choi matrix. The vectorization has first-system marginal σ. The final reference index is the input wire.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, https://arxiv.org/abs/0904.4483v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

/-!
Statements from Chiribella, D'Ariano and Perinotti, arXiv:0904.4483v2.
All physical spaces have positive finite dimension and their displayed coordinate bases.
Tensor factors are ordered output first, newest tooth first. Order zero below is only
an auxiliary scalar prefix, never a physical 0-comb. The infinite dimension sequences
are padding: an order-N object uses only the first N pairs.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF pp.2–3, Eq.(2): transport the accepted unnormalized Choi operator
from input-first to output-first wire order; no normalization change. -/
def outputFirstChoi {I O : Type*} [Fintype I]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Matrix (O × I) (O × I) ℂ :=
  fun a b => QAlgorithms.Papers.Independent.Information100.P34.choi
    M.toFun (Prod.swap a) (Prod.swap b)

/-- PDF p.2: trace preservation on all operators, without a positivity assumption. -/
def TracePreserving {I O : Type*} [Fintype I] [Fintype O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ X, (M X).trace = X.trace

/-- PDF p.2: Hermitian preservation on every Hermitian operator. -/
def HermitianPreserving {I O : Type*}
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) : Prop :=
  ∀ X, X.IsHermitian → (M X).IsHermitian

/-- PDF p.3, Eqs.(12)–(13): link of two channel-shaped operators through their common wire. -/
def channelLink {I J O : Type*} [Fintype J]
    (B : Matrix (O × J) (O × J) ℂ) (A : Matrix (J × I) (J × I) ℂ) :
    Matrix (O × I) (O × I) ℂ :=
  fun a b => ∑ u, ∑ v, B (a.1,u) (b.1,v) * A (u,a.2) (v,b.2)

/-- PDF p.2: the Choi map does not normalize by the input dimension. -/
example : outputFirstChoi (LinearMap.id : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ]
    Matrix (Fin 1) (Fin 1) ℂ) (0,0) (0,0) = 1 := by
  simp [outputFirstChoi, QAlgorithms.Papers.Independent.Information100.P34.choi, Matrix.single]

/-- PDF pp.5–7: ordered pairs of external input and output wires, all of positive dimension. -/
structure Signature where
  input : ℕ → ℕ
  output : ℕ → ℕ
  input_pos : ∀ j, 0 < input j
  output_pos : ∀ j, 0 < output j

/-- PDF pp.6–7: the restricted prefix tensor space, ordered newest output/input first. -/
def Basis (s : Signature) : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin (s.output n) × (Fin (s.input n) × Basis s n)

/-- PDF pp.6–7: finite coordinate basis of each restricted prefix. -/
instance basisFintype (s : Signature) : (n : ℕ) → Fintype (Basis s n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := basisFintype s n
             inferInstanceAs (Fintype (Fin (s.output n) × (Fin (s.input n) × Basis s n)))

/-- PDF pp.2,6–7: positive wire dimensions make each restricted prefix nonempty. -/
instance basisNonempty (s : Signature) : (n : ℕ) → Nonempty (Basis s n)
  | 0 => ⟨()⟩
  | n + 1 => letI := basisNonempty s n
             ⟨(⟨0,s.output_pos n⟩, ⟨0,s.input_pos n⟩, Classical.choice inferInstance)⟩

/-- PDF p.7, Eq.(25): recursive positive normalized prefixes; the scalar prefix is 1. -/
def Normalized (s : Signature) : (n : ℕ) → Matrix (Basis s n) (Basis s n) ℂ → Prop
  | 0, R => R = 1
  | n + 1, R => R.PosSemidef ∧ ∃ Q : Matrix (Basis s n) (Basis s n) ℂ,
      Normalized s n Q ∧ traceLeft R = Matrix.kronecker (1 : Matrix (Fin (s.input n)) _ ℂ) Q

/-- PDF p.12: the affine trace constraints, independently of the positive cone. -/
def AffineNormalized (s : Signature) :
    (n : ℕ) → Matrix (Basis s n) (Basis s n) ℂ → Prop
  | 0, R => R = 1
  | n + 1, R => ∃ Q : Matrix (Basis s n) (Basis s n) ℂ,
      AffineNormalized s n Q ∧
        traceLeft R = Matrix.kronecker (1 : Matrix (Fin (s.input n)) _ ℂ) Q

/-- PDF pp.10–11: the inner slot of an (N+1)-comb has wire roles shifted by one. -/
def slots (s : Signature) : Signature where
  input j := s.output j
  output j := s.input (j+1)
  input_pos := s.output_pos
  output_pos j := s.input_pos (j+1)

/-- PDF p.11, Eq.(42): place external endpoints around an inner-slot basis vector. -/
def insertEndpoints (s : Signature) : (n : ℕ) →
    Fin (s.output n) → Fin (s.input 0) → Basis (slots s) n → Basis s (n+1)
  | 0, o, i, _ => (o,i,())
  | n+1, o, i, x => (o,x.1,insertEndpoints s n x.2.1 i x.2.2)

/-- PDF p.11, Eq.(42), and p.16, Eq.(64): contraction with the transposed inner comb. -/
def slotAction (s : Signature) (n : ℕ)
    (S : Matrix (Basis s (n+1)) (Basis s (n+1)) ℂ)
    (R : Matrix (Basis (slots s) n) (Basis (slots s) n) ℂ) :
    Matrix (Fin (s.output n) × Fin (s.input 0))
      (Fin (s.output n) × Fin (s.input 0)) ℂ :=
  fun a b => ∑ u, ∑ v,
    S (insertEndpoints s n a.1 a.2 u) (insertEndpoints s n b.1 b.2 v) * R u v

/-- PDF p.4, Eq.(18): positive, trace-preserving Choi operators. -/
def ChannelChoi {I O : Type*} [Fintype I] [Fintype O]
    (C : Matrix (O × I) (O × I) ℂ) : Prop :=
  C.PosSemidef ∧ traceLeft C = 1

/-- PDF pp.10–11, Definitions 3–4: deterministic combs defined by their action on inner combs.
The base is a channel. Positivity is the CP Choi condition of Lemma 3, not a normalization
hypothesis. This predicate is independent of Normalized. Order zero is excluded. -/
def Deterministic : (n : ℕ) → (s : Signature) →
    Matrix (Basis s n) (Basis s n) ℂ → Prop
  | 0, _, _ => False
  | 1, s, R => R.PosSemidef ∧
      traceLeft R = Matrix.kronecker (1 : Matrix (Fin (s.input 0)) _ ℂ)
        (1 : Matrix Unit Unit ℂ)
  | n+2, s, R => R.PosSemidef ∧
      ∀ T : Matrix (Basis (slots s) (n+1)) (Basis (slots s) (n+1)) ℂ,
        Deterministic (n+1) (slots s) T → ChannelChoi (slotAction s (n+1) R T)

/-- PDF p.10, Definition 4: a probabilistic comb is positive and PSD-dominated by a
normalized deterministic comb. Normalized is the equivalent Eq.(40) presentation. -/
def Probabilistic (s : Signature) (n : ℕ)
    (R : Matrix (Basis s n) (Basis s n) ℂ) : Prop :=
  0 < n ∧ R.PosSemidef ∧ ∃ S, Normalized s n S ∧ (S-R).PosSemidef

/-- PDF pp.2,16: an unnormalized rank-one Choi operator. Zero vectors are allowed. -/
def rankOne {I : Type*} (v : I → ℂ) : Matrix I I ℂ :=
  fun a b => v a * conj (v b)

/-- PDF pp.5–7: a sequential memory network of finite-dimensional CPTP channels.
Only the first N vertices are used at order N. Each vertex has its own label. -/
structure MemoryNetwork (s : Signature) where
  memory : ℕ → ℕ
  memory_pos : ∀ j, 0 < memory j
  initial_memory : memory 0 = 1
  krausCount : ℕ → ℕ
  kraus : (j : ℕ) → Fin (krausCount j) →
    Matrix (Fin (s.output j) × Fin (memory (j+1)))
      (Fin (s.input j) × Fin (memory j)) ℂ
  trace_preserving : ∀ j, ∑ a, (kraus j a)ᴴ * kraus j a = 1

/-- PDF p.6, Eq.(21): explicit circuit contraction, retaining the current internal memory. -/
def MemoryNetwork.retained {s : Signature} (net : MemoryNetwork s) : (n : ℕ) →
    Matrix (Fin (net.memory n) × Basis s n) (Fin (net.memory n) × Basis s n) ℂ
  | 0 => fun a b => if a.1.val = 0 ∧ b.1.val = 0 then 1 else 0
  | n+1 => fun a b => ∑ e, ∑ u : Fin (net.memory n), ∑ v : Fin (net.memory n),
      net.kraus n e (a.2.1,a.1) (a.2.2.1,u) *
      net.retained n (u,a.2.2.2) (v,b.2.2.2) *
      conj (net.kraus n e (b.2.1,b.1) (b.2.2.1,v))

/-- PDF p.6, Eq.(21): the Choi operator after discarding the last memory. -/
def MemoryNetwork.choi {s : Signature} (net : MemoryNetwork s) (n : ℕ) :
    Matrix (Basis s n) (Basis s n) ℂ := traceLeft (net.retained n)

/-- PDF p.7, Fig.3: a sequence of isometries, with one-dimensional initial memory. -/
structure IsometricNetwork (s : Signature) where
  memory : ℕ → ℕ
  memory_pos : ∀ j, 0 < memory j
  initial_memory : memory 0 = 1
  interaction : (j : ℕ) →
    Matrix (Fin (s.output j) × Fin (memory (j+1)))
      (Fin (s.input j) × Fin (memory j)) ℂ
  isometry : ∀ j, (interaction j)ᴴ * interaction j = 1

/-- PDF p.7: amplitudes of the contracted isometries before tracing the final memory. -/
def IsometricNetwork.amplitude {s : Signature} (net : IsometricNetwork s) : (n : ℕ) →
    Fin (net.memory n) → Basis s n → ℂ
  | 0, a, _ => if a.val = 0 then 1 else 0
  | n+1, a, x => ∑ b : Fin (net.memory n),
      net.interaction n (x.1,a) (x.2.1,b) * net.amplitude n b x.2.2

/-- PDF p.7, Fig.3: final memory is traced, rather than postselected. -/
def IsometricNetwork.choi {s : Signature} (net : IsometricNetwork s) (n : ℕ) :
    Matrix (Basis s n) (Basis s n) ℂ := ∑ a, rankOne (net.amplitude n a)

/-- PDF p.8, Theorem 4: a common isometric realization with a k-dimensional measured factor.
The residual memory dimension r is unrestricted and is discarded. The equivalence fixes the
computational measurement basis; arbitrary bases can be absorbed in the last interaction. -/
def MeasuredRealization (s : Signature) (n k : ℕ)
    (R : Fin k → Matrix (Basis s n) (Basis s n) ℂ) : Prop :=
  ∃ net : IsometricNetwork s, ∃ r : ℕ, 0 < r ∧
    ∃ e : (Fin k × Fin r) ≃ Fin (net.memory n),
      ∀ i, R i = ∑ a, rankOne (net.amplitude n (e (i,a)))

/-- PDF p.16, Definition 10: finite-outcome generalized comb instrument.
This is a predicate on multi-tooth Choi branches, distinct from a one-use Kraus instrument. -/
def CombInstrument (s : Signature) (n k : ℕ)
    (R : Fin k → Matrix (Basis s n) (Basis s n) ℂ) : Prop :=
  0 < n ∧ 0 < k ∧ (∀ i, (R i).PosSemidef) ∧ Normalized s n (∑ i, R i)

/-- PDF p.7: the base prefix is an actual scalar, with no ignored later coordinates. -/
example (s : Signature) : Normalized s 0 (1 : Matrix (Basis s 0) _ ℂ) := rfl

/-- PDF p.7: normalization at one tooth contains the input identity and a scalar prefix. -/
example (s : Signature) (R : Matrix (Basis s 1) _ ℂ) :
    Normalized s 1 R ↔ R.PosSemidef ∧
      ∃ Q : Matrix (Basis s 0) (Basis s 0) ℂ, Q = 1 ∧
        traceLeft R = Matrix.kronecker (1 : Matrix (Fin (s.input 0)) _ ℂ) Q := by
  simp only [Normalized]

/-- PDF pp.4,16: quantum-operation Choi operators, with a CPTP completion. -/
def OperationChoi {I O : Type*} [Fintype I] [Fintype O]
    (R : Matrix (O × I) (O × I) ℂ) : Prop :=
  R.PosSemidef ∧ ∃ C, ChannelChoi C ∧ (C-R).PosSemidef

/-- PDF p.17, Definition 11: positivity and pointwise normalization on every deterministic comb.
This multi-outcome comb tester is distinct from a parallel channel tester with one effect. -/
def CombTester (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s n) (Basis s n) ℂ) : Prop :=
  0 < n ∧ 0 < k ∧ (∀ i, (P i).PosSemidef) ∧
    ∀ R, Normalized s n R → (∀ i, 0 ≤ QAlgorithms.effectProb (P i).transpose R) ∧ (∑ i, QAlgorithms.effectProb (P i).transpose R) = 1

/-- PDF p.17, Eq.(67), corrected using Lemma 8 and Eq.(25): Θ has the last input and all
previous teeth. Trace out that last input, then recurse; the final scalar trace is 1. -/
def ThetaNormalized (s : Signature) : (n : ℕ) →
    Matrix (Fin (s.input n) × Basis s n) (Fin (s.input n) × Basis s n) ℂ → Prop
  | 0, T => T.PosSemidef ∧ T.trace = 1
  | n+1, T => T.PosSemidef ∧
      ∃ Q : Matrix (Fin (s.input n) × Basis s n) _ ℂ,
        ThetaNormalized s n Q ∧
          traceLeft T = Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) Q

/-- PDF p.19, Definition 13: spanning the full complex operator space, with transposed effects. -/
def InformationallyComplete {I : Type*} [Fintype I] {k : ℕ}
    (P : Fin k → Matrix I I ℂ) : Prop :=
  ∀ X : Matrix I I ℂ, ∃ c : Fin k → ℂ, X = ∑ i, c i • (P i).transpose

/-- PDF p.20, Definition 14: D is the actual complex span of deterministic combs.
The erroneous printed single-trace characterization of D is not used. -/
def DeterministicSpan (s : Signature) (n : ℕ) :
    Submodule ℂ (Matrix (Basis s n) (Basis s n) ℂ) :=
  Submodule.span ℂ {R | Normalized s n R}

/-- PDF p.20, Definition 14: completeness on D, rather than the whole operator space. -/
def CompleteForDeterministic (s : Signature) (n k : ℕ)
    (P : Fin k → Matrix (Basis s n) (Basis s n) ℂ) : Prop :=
  ∀ X ∈ DeterministicSpan s n, ∃ c : Fin k → ℂ, X = ∑ i, c i • (P i).transpose

/-- PDF pp.4,17: a finite nonempty POVM on the displayed space. -/
def POVM {I : Type*} [Fintype I] {k : ℕ} (P : Fin k → Matrix I I ℂ) : Prop :=
  0 < k ∧ (∀ i, (P i).PosSemidef) ∧ ∑ i, P i = 1

/-- PDF pp.17–20: spectral functional calculus on a Hermitian operator.
The fallback is used only off the stated PSD/Hermitian domains. -/
def spectral {I : Type*} [Fintype I] (A : Matrix I I ℂ) (f : ℝ → ℝ) : Matrix I I ℂ :=
  if h : A.IsHermitian then h.cfc f else 0

/-- PDF p.17, Eqs.(68)–(69): positive spectral square root. -/
def matrixSqrt {I : Type*} [Fintype I] (A : Matrix I I ℂ) : Matrix I I ℂ :=
  spectral A Real.sqrt

/-- PDF p.19, Eq.(89): in zero-based wire labels the denominator is the input-dimension product. -/
def inputDimension (s : Signature) (n : ℕ) : ℕ := ∏ j ∈ Finset.range n, s.input j

/-- PDF p.9, Eq.(38): fully contract an external experiment with a network's Choi
operator, including a probabilistic branch. This entrywise tensor contraction is
independent of the trace-form Born definition. -/
def externalProbability (s : Signature) (n : ℕ)
    (R P : Matrix (Basis s n) (Basis s n) ℂ) : ℝ :=
  (∑ a, ∑ b, R a b * P a b).re

/-- PDF p.20, Eq.(92): the multiple-time vector in the fixed wire order.
prep j is |Ψ_j⟩ and post j is |Φ_(j+1)⟩; postselection is complex conjugated.
This tensor product is unrelated to the Dyson ODE history-state construction. -/
def multiTimeVector (s : Signature)
    (prep : (j : ℕ) → Fin (s.input j) → ℂ)
    (post : (j : ℕ) → Fin (s.output j) → ℂ) : (n : ℕ) → Basis s n → ℂ
  | 0, _ => 1
  | n+1, x => conj (post n x.1) * prep n x.2.1 * multiTimeVector s prep post n x.2.2

/-- PDF p.20, Eqs.(93)–(94): conditional probability, only asserted with positive total weight. -/
def conditionalBorn {I : Type*} [Fintype I] {k : ℕ}
    (R : Fin k → Matrix I I ℂ) (S : Matrix I I ℂ) (i : Fin k) : ℝ :=
  QAlgorithms.effectProb (R i).transpose S / ∑ j, QAlgorithms.effectProb (R j).transpose S

/-- PDF p.20: the zero history is a zero branch, not a normalized pure state. -/
example {I : Type*} : rankOne (fun _ : I => 0) = 0 := by
  funext a b
  simp [rankOne]

/-- PDF p.20, Eq.(92): at one time the postselection factor is conjugated. -/
example (s : Signature) (prep : (j : ℕ) → Fin (s.input j) → ℂ)
    (post : (j : ℕ) → Fin (s.output j) → ℂ) (o : Fin (s.output 0))
    (i : Fin (s.input 0)) :
    multiTimeVector s prep post 1 (o,i,()) = conj (post 0 o) * prep 0 i := by
  simp [multiTimeVector]

/-- PDF p.3, Eq.(14): general link after grouping exclusive and common wire factors.
X and Y are the exclusive tensor factors and J is the entire common tensor factor.
An empty group of wire labels is represented by a one-dimensional type. -/
def partialLink {X Y J : Type*} [Fintype J]
    (M : Matrix (X × J) (X × J) ℂ) (N : Matrix (Y × J) (Y × J) ℂ) :
    Matrix (X × Y) (X × Y) ℂ :=
  fun a b => ∑ u, ∑ v, M (a.1,u) (b.1,v) * N (a.2,u) (b.2,v)

/-- PDF p.3: regroup tensor factors through the displayed basis map. -/
def regroup {X Y : Type*} (f : X → Y) (M : Matrix Y Y ℂ) : Matrix X X ℂ :=
  fun a b => M (f a) (f b)

/-- PDF p.3, Theorem 2(2): M1*(M2*M3), grouped onto A⊗B⊗C.
AB, AC and BC label the three pairwise intersections; there is no triple intersection. -/
def linkRightNested {A B C AB AC BC : Type*}
    [Fintype AB] [Fintype AC] [Fintype BC]
    (M1 : Matrix (A × (AB × AC)) (A × (AB × AC)) ℂ)
    (M2 : Matrix (B × (AB × BC)) (B × (AB × BC)) ℂ)
    (M3 : Matrix (C × (AC × BC)) (C × (AC × BC)) ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  partialLink M1
    (regroup (fun x : (B × C) × (AB × AC) => ((x.1.1,x.2.1),(x.1.2,x.2.2)))
      (partialLink
        (regroup (fun x : (B × AB) × BC => (x.1.1,(x.1.2,x.2))) M2)
        (regroup (fun x : (C × AC) × BC => (x.1.1,(x.1.2,x.2))) M3)))

/-- PDF p.3, Theorem 2(2): (M1*M2)*M3, with exactly the same external factor order. -/
def linkLeftNested {A B C AB AC BC : Type*}
    [Fintype AB] [Fintype AC] [Fintype BC]
    (M1 : Matrix (A × (AB × AC)) (A × (AB × AC)) ℂ)
    (M2 : Matrix (B × (AB × BC)) (B × (AB × BC)) ℂ)
    (M3 : Matrix (C × (AC × BC)) (C × (AC × BC)) ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  regroup (fun x : A × (B × C) => ((x.1,x.2.1),x.2.2))
    (partialLink
      (regroup (fun x : (A × B) × (AC × BC) => ((x.1.1,x.2.1),(x.1.2,x.2.2)))
        (partialLink
          (regroup (fun x : (A × AC) × AB => (x.1.1,(x.2,x.1.2))) M1)
          (regroup (fun x : (B × BC) × AB => (x.1.1,(x.2,x.1.2))) M2))) M3)

/-- PDF p.3, Eq.(15): with no common wires the grouped link is the tensor product. -/
example {X Y : Type*} (M : Matrix X X ℂ) (N : Matrix Y Y ℂ) :
    partialLink (fun a b : X × Unit => M a.1 b.1)
      (fun a b : Y × Unit => N a.1 b.1) = Matrix.kronecker M N := by
  funext a b
  simp [partialLink, Matrix.kronecker]

/-- PDF p.19, Eq.(82): the full feasible normalization set, with every recursive constraint. -/
def TotalNormalized (s : Signature) : (n : ℕ) →
    Matrix (Basis s n) (Basis s n) ℂ → Prop
  | 0, _ => False
  | n+1, T => ∃ Q : Matrix (Fin (s.input n) × Basis s n) _ ℂ,
      ThetaNormalized s n Q ∧ T = Matrix.kronecker (1 : Matrix (Fin (s.output n)) _ ℂ) Q

/-- PDF pp.17,19, Eqs.(68),(81): transposed-root sandwich, in the fixed complex basis. -/
def coherentSandwich {I : Type*} [Fintype I] (T R : Matrix I I ℂ) : Matrix I I ℂ :=
  (matrixSqrt T).transpose * R * (matrixSqrt T).transpose

/-- PDF p.19, Eq.(82): half the maximal trace norm over causally normalized testers.
The source's finite-dimensional feasible set is nonempty and compact at positive order. -/
def combDistance (s : Signature) (n : ℕ)
    (R S : Matrix (Basis s n) (Basis s n) ℂ) : ℝ :=
  sSup {z : ℝ | ∃ T, TotalNormalized s n T ∧ z = traceNorm (coherentSandwich T (R-S)) / 2}

/-- PDF p.19, Eq.(83): cb/diamond distance with the source's factor 1/2 and arbitrary
positive finite ancilla dimension. This is not identified with the library's unhalved norm. -/
def cbDistance {I O : Type*} [Fintype I] [Fintype O]
    (M N : Matrix I I ℂ → Matrix O O ℂ) : ℝ :=
  sSup {z : ℝ | ∃ r : ℕ, 0 < r ∧ ∃ rho : Matrix (Fin r × I) (Fin r × I) ℂ,
    IsDensityMatrix rho ∧
      z = traceNorm (idTensorSuperop (fun X => M X - N X) rho) / 2}

/-- PDF p.7, Eq.(26): basis for all external input wires. -/
def InputBasis (s : Signature) : ℕ → Type
  | 0 => Unit
  | n+1 => Fin (s.input n) × InputBasis s n

/-- PDF p.7, Eq.(26): basis for all external output wires. -/
def OutputBasis (s : Signature) : ℕ → Type
  | 0 => Unit
  | n+1 => Fin (s.output n) × OutputBasis s n

/-- PDF p.7, Eq.(26): finite tensor basis of all external input wires. -/
instance inputBasisFintype (s : Signature) : (n : ℕ) → Fintype (InputBasis s n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := inputBasisFintype s n
           inferInstanceAs (Fintype (Fin (s.input n) × InputBasis s n))

/-- PDF p.7, Eq.(26): finite tensor basis of all external output wires. -/
instance outputBasisFintype (s : Signature) : (n : ℕ) → Fintype (OutputBasis s n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := outputBasisFintype s n
           inferInstanceAs (Fintype (Fin (s.output n) × OutputBasis s n))

/-- PDF p.7, Eq.(26): interleave the parallel input/output registers into the comb basis. -/
def interleave (s : Signature) : (n : ℕ) → OutputBasis s n → InputBasis s n → Basis s n
  | 0, _, _ => ()
  | n+1, o, i => (o.1,i.1,interleave s n o.2 i.2)

/-- PDF pp.2,7: the multipartite map constructed from its Choi operator, Eq.(3). -/
def parallelMap (s : Signature) (n : ℕ) (R : Matrix (Basis s n) (Basis s n) ℂ)
    (X : Matrix (InputBasis s n) (InputBasis s n) ℂ) :
    Matrix (OutputBasis s n) (OutputBasis s n) ℂ :=
  fun a b => ∑ u, ∑ v, R (interleave s n a u) (interleave s n b v) * X u v

/-- PDF p.18, Eq.(77): average error with both possible zero priors permitted. -/
def discriminationError (s : Signature) (n : ℕ)
    (R0 R1 : Matrix (Basis s n) (Basis s n) ℂ) (p0 p1 : ℝ)
    (P : Fin 2 → Matrix (Basis s n) (Basis s n) ℂ) : ℝ :=
  p0 * QAlgorithms.effectProb (P 1).transpose R0 + p1 * QAlgorithms.effectProb (P 0).transpose R1

/-- PDF p.19: a zero difference gives zero cb-distance integrands, including entangled inputs. -/
example {I O : Type*} [Fintype I] [Fintype O] (r : ℕ)
    (rho : Matrix (Fin r × I) (Fin r × I) ℂ) (M : Matrix I I ℂ → Matrix O O ℂ) :
    idTensorSuperop (fun X => M X - M X) rho = 0 := by
  funext a b
  simp [idTensorSuperop]

/-- PDF pp.17–18: Moore–Penrose inverse, with eigenvalue zero mapped to zero. -/
def pseudoInverse {I : Type*} [Fintype I] (A : Matrix I I ℂ) : Matrix I I ℂ :=
  spectral A (fun x => x⁻¹)

/-- PDF p.18: I_out tensor A_in on the one-tooth comb basis, including the scalar prefix. -/
def oneInputLift (s : Signature) (A : Matrix (Fin (s.input 0)) (Fin (s.input 0)) ℂ) :
    Matrix (Basis s 1) (Basis s 1) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin (s.output 0)) _ ℂ)
    (regroup (fun x : Fin (s.input 0) × Unit => x.1) A)

/-- PDF p.18, Eq.(76): (C⊗id)(|sqrt σ⟩⟩⟨⟨sqrt σ|), computed from C's Choi matrix.
The vectorization has first-system marginal σ. The final reference index is the input wire. -/
def onePurifiedOutput (s : Signature) (C : Matrix (Basis s 1) (Basis s 1) ℂ)
    (sigma : Matrix (Fin (s.input 0)) (Fin (s.input 0)) ℂ) :
    Matrix (Basis s 1) (Basis s 1) ℂ :=
  fun a b => ∑ u, ∑ v,
    C (a.1,u,()) (b.1,v,()) *
      matrixSqrt sigma u a.2.1 * conj (matrixSqrt sigma v b.2.1)

/-- PDF p.7: the initial pure memory amplitude equals one, before any circuit use. -/
example (s : Signature) (net : IsometricNetwork s) :
    net.amplitude 0 ⟨0,net.memory_pos 0⟩ () = 1 := by
  simp [IsometricNetwork.amplitude]

/-- PDF p.17: on a Hermitian operator the spectral root uses that operator's spectral calculus. -/
example {I : Type*} [Fintype I] (A : Matrix I I ℂ) (h : A.IsHermitian) :
    matrixSqrt A = h.cfc Real.sqrt := by
  simp [matrixSqrt, spectral, h]

/-- PDF p.10: slot inputs are the previous output wires, not the external input wires. -/
example (s : Signature) (n : ℕ) :
    (slots s).input n = s.output n ∧ (slots s).output n = s.input (n+1) := ⟨rfl,rfl⟩

end QAlgorithms.Papers.Independent.Dependency50.P26


