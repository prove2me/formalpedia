-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
-- name    : QAlgorithms_Papers_Independent_Information100_P71
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T17:42:37.986504+00:00
-- url     : https://prove2.me/theorems/0b0c7606-2c18-4e74-8149-7ab4de289f18
-- title:
--   Definitions for Continuity of Regularized Channel Rényi Divergences
-- statement:
--   The objects the formalized statements of *Continuity of Regularized Channel Rényi Divergences* (arXiv:2609.28635) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CPLe`: PDF p.2, (1.6): CP order. The witness ensures the difference is complex-linear.
--   - `mapMaxRelative`: PDF p.2, (1.7): map max-relative entropy; infimum of the empty set is +infinity. EReal also preserves negative values and minus infinity for a zero numerator.
--   - `stateRelative`: PDF p.2, (1.2): frozen Umegaki entropy converted from nats to bits. Invalid density arguments are assigned +infinity; channel outputs below are densities.
--   - `SupportIncluded`: PDF pp.2–3: support inclusion of positive matrices is reversed kernel inclusion.
--   - `supportPower`: PDF p.2, (1.3): spectral power set to zero on the kernel, including negative powers. Every function on a finite spectrum is continuous on that spectrum.
--   - `sandwichedTrace`: PDF p.2, (1.3): sandwiched trace functional.
--   - `stateRenyi`: PDF pp.2–3, (1.3): sandwiched divergence in bits, on density matrices and orders alpha >= 1/2 other than 1. Support mismatch above 1 and zero trace below 1 give +infinity.
--   - `channelRelative`: PDF p.2, (1.4): stabilized relative entropy, reference isomorphic to input.
--   - `channelRenyi`: PDF p.2, (1.4): stabilized sandwiched divergence on all normalized pure inputs.
--   - `channelPower`: PDF p.2, (1.5): tensor power on all matrix units, including entangled inputs.
--   - `regularize`: PDF p.2, (1.5): positive-block supremum; index k denotes block length k+1. This defines regularization without assuming a limit and preserves infinite values.
--   - `relativeReg`: PDF p.2, (1.5): regularized stabilized relative entropy.
--   - `renyiReg`: PDF p.2, (1.5): regularized stabilized sandwiched divergence.
--   - `hockeyStick`: PDF p.4, (2.3)–(2.4): maximum testing payoff, written as suprema. For channels, nonempty input spaces and lambda >= 1, both suprema range over nonempty bounded sets: zero effect attains zero, and every payoff lies in [-lambda,1].
--   - `dilationMap`: PDF p.3, (1.8): induced map of an arbitrary dilation operator.
--   - `IsStinespring`: PDF p.3: Stinespring isometry in the prescribed environment.
--   - `IsSubchannel`: PDF p.9, §3.2: complex-linear CP map, trace nonincreasing on every positive input; trace preservation is not required.
--   - `diamond`: PDF p.9, footnote 7: unhalved diamond norm. Reference dimension equals input dimension; this suffices also for rectangular complex-linear maps. The trace-norm unit ball is compact and contains zero, so the real supremum is meaningful on the linear maps used here.
--   - `smoothMax`: PDF p.9, (3.4): extended-real infimum over nearby subchannels, with no attainment assumed.
--   - `AdaptiveTest`: PDF p.8, §3.1: n-use adaptive test with arbitrary finite retained memory. Initial state, interleavings and effect are common to the hypotheses. Different finite memories at different rounds embed into their maximum dimension. Only interleavings 0,...,n-2 are used.
--   - `adaptiveInput`: PDF p.8: input after k completed calls and interleavings.
--   - `adaptiveAccept`: PDF p.8: acceptance under the supplied channel. Exactly n calls for n>0; the unused n=0 term is explicitly zero.
--   - `adaptiveBeta`: PDF pp.8–9, (3.3): fixed-error adaptive type-II infimum. For n>0 and epsilon in (0,1), the always-accept test is feasible and errors lie in [0,1]. Finite Dmax bounds the infimum strictly away from zero at each fixed positive n. No minimum is asserted.
--   - `ParallelTest`: PDF pp.8–9: parallel test with normalized pure block input and reference isomorphic to the whole input block. Purification and Schmidt compression give the full testing region.
--   - `parallelAccept`: PDF p.9: acceptance after n parallel channel calls.
--   - `parallelBeta`: PDF p.9: fixed-error infimum restricted to parallel tests.
-- source:
--   Continuity of Regularized Channel Rényi Divergences, arXiv:2609.28635v1, https://arxiv.org/abs/2609.28635v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement

/-! Statements from Wang and Yang, arXiv:2609.28635v1.
All page citations refer to PDF pages; all logarithms are base two.
New interfaces are local to this paper and extend the frozen accepted library. -/

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate
open Filter

namespace QAlgorithms.Papers.Independent.Information100.P71

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.2, (1.6): CP order. The witness ensures the difference is complex-linear. -/
def CPLe {A B : Type} [Fintype A] [Fintype B] (F G : Superop A B) : Prop :=
  ∃ L : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ,
    Entanglement.IsCompletelyPositive L ∧ ∀ X, L X = G X - F X

/-- PDF p.2, (1.7): map max-relative entropy; infimum of the empty set is +infinity.
EReal also preserves negative values and minus infinity for a zero numerator. -/
def mapMaxRelative {A B : Type} [Fintype A] [Fintype B]
    (F G : Superop A B) : EReal :=
  sInf {d : EReal | ∃ t : ℝ, 0 < t ∧ CPLe F (fun X => (t : ℂ) • G X) ∧
    d = (Real.logb 2 t : EReal)}

/-- PDF p.2, (1.2): frozen Umegaki entropy converted from nats to bits.
Invalid density arguments are assigned +infinity; channel outputs below are densities. -/
def stateRelative {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : EReal :=
  if h : IsDensityMatrix rho ∧ IsDensityMatrix sigma then
    (QuantumLoss.umegakiEntropy rho sigma h.1 h.2 : EReal) *
      ((1 / Real.log 2 : ℝ) : EReal)
  else ⊤

/-- PDF pp.2–3: support inclusion of positive matrices is reversed kernel inclusion. -/
def SupportIncluded {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : Prop :=
  LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin

/-- PDF p.2, (1.3): spectral power set to zero on the kernel, including negative powers.
Every function on a finite spectrum is continuous on that spectrum. -/
def supportPower {I : Type} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else Real.rpow x t) X

/-- PDF p.2, (1.3): sandwiched trace functional. -/
def sandwichedTrace {I : Type} [Fintype I] [DecidableEq I]
    (alpha : ℝ) (rho sigma : Matrix I I ℂ) : ℝ :=
  let S := supportPower sigma ((1 - alpha) / (2 * alpha))
  (supportPower (S * rho * S) alpha).trace.re

/-- PDF pp.2–3, (1.3): sandwiched divergence in bits, on density matrices and orders
alpha >= 1/2 other than 1. Support mismatch above 1 and zero trace below 1 give +infinity. -/
def stateRenyi {I : Type} [Fintype I] [DecidableEq I]
    (alpha : ℝ) (rho sigma : Matrix I I ℂ) : EReal :=
  if 1 < alpha ∧ ¬ SupportIncluded rho sigma then ⊤
  else if 0 < sandwichedTrace alpha rho sigma then
    ((Real.logb 2 (sandwichedTrace alpha rho sigma) / (alpha - 1) : ℝ) : EReal)
  else ⊤

/-- PDF p.2, (1.4): stabilized relative entropy, reference isomorphic to input. -/
def channelRelative {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N M : Superop A B) : EReal :=
  ⨆ psi : {v : EuclideanSpace ℂ (A × A) // IsState v},
    stateRelative (idTensorSuperop (R := A) N (pureDensity psi.1))
      (idTensorSuperop (R := A) M (pureDensity psi.1))

/-- PDF p.2, (1.4): stabilized sandwiched divergence on all normalized pure inputs. -/
def channelRenyi {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (alpha : ℝ) (N M : Superop A B) : EReal :=
  ⨆ psi : {v : EuclideanSpace ℂ (A × A) // IsState v},
    stateRenyi alpha (idTensorSuperop (R := A) N (pureDensity psi.1))
      (idTensorSuperop (R := A) M (pureDensity psi.1))

/-- PDF p.2, (1.5): tensor power on all matrix units, including entangled inputs. -/
def channelPower {A B : Type} [Fintype A] [DecidableEq A]
    (F : Superop A B) (n : ℕ) : Superop (Fin n → A) (Fin n → B) :=
  piSuperop (fun _ : Fin n => F)

/-- PDF p.2, (1.5): positive-block supremum; index k denotes block length k+1.
This defines regularization without assuming a limit and preserves infinite values. -/
def regularize (d : ℕ → EReal) : EReal :=
  ⨆ k : ℕ, (((1 : ℝ) / (k + 1 : ℕ) : ℝ) : EReal) * d (k + 1)

/-- PDF p.2, (1.5): regularized stabilized relative entropy. -/
def relativeReg {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N M : Superop A B) : EReal :=
  regularize (fun n => channelRelative (channelPower N n) (channelPower M n))

/-- PDF p.2, (1.5): regularized stabilized sandwiched divergence. -/
def renyiReg {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (alpha : ℝ) (N M : Superop A B) : EReal :=
  regularize (fun n => channelRenyi alpha (channelPower N n) (channelPower M n))

/-- PDF p.4, (2.3)–(2.4): maximum testing payoff, written as suprema. For channels,
nonempty input spaces and lambda >= 1, both suprema range over nonempty bounded sets:
zero effect attains zero, and every payoff lies in [-lambda,1]. -/
def hockeyStick {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (lambda : ℝ) (N M : Superop A B) : ℝ :=
  ⨆ psi : {v : EuclideanSpace ℂ (A × A) // IsState v},
    ⨆ T : {T : Matrix (A × B) (A × B) ℂ // IsEffect T},
      effectProb T.1 (idTensorSuperop (R := A) N (pureDensity psi.1)) -
        lambda * effectProb T.1 (idTensorSuperop (R := A) M (pureDensity psi.1))

/-- PDF p.3, (1.8): induced map of an arbitrary dilation operator. -/
def dilationMap {A B E : Type} [Fintype A] [Fintype E]
    (V : Matrix (B × E) A ℂ) : Superop A B :=
  fun X => traceRight (V * X * Vᴴ)

/-- PDF p.3: Stinespring isometry in the prescribed environment. -/
def IsStinespring {A B E : Type} [Fintype A] [Fintype B] [Fintype E] [DecidableEq A]
    (N : Superop A B) (V : Matrix (B × E) A ℂ) : Prop :=
  Vᴴ * V = 1 ∧ dilationMap V = N

/-- PDF p.9, §3.2: complex-linear CP map, trace nonincreasing on every positive input;
trace preservation is not required. -/
def IsSubchannel {A B : Type} [Fintype A] [Fintype B] (G : Superop A B) : Prop :=
  ∃ L : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ,
    (∀ X, L X = G X) ∧ Entanglement.IsCompletelyPositive L ∧
      ∀ X : Matrix A A ℂ, X.PosSemidef → (G X).trace.re ≤ X.trace.re

/-- PDF p.9, footnote 7: unhalved diamond norm. Reference dimension equals input dimension;
this suffices also for rectangular complex-linear maps. The trace-norm unit ball is compact
and contains zero, so the real supremum is meaningful on the linear maps used here. -/
def diamond {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : Superop A B) : ℝ :=
  sSup {v : ℝ | ∃ X : Matrix (A × A) (A × A) ℂ,
    traceNorm X ≤ 1 ∧ v = traceNorm (idTensorSuperop (R := A) F X)}

/-- PDF p.9, (3.4): extended-real infimum over nearby subchannels, with no attainment assumed. -/
def smoothMax {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (epsilon : ℝ) (N M : Superop A B) : EReal :=
  sInf {d : EReal | ∃ G : Superop A B, IsSubchannel G ∧
    diamond (fun X => G X - N X) ≤ epsilon ∧ d = mapMaxRelative G M}

/-- PDF p.8, §3.1: n-use adaptive test with arbitrary finite retained memory. Initial state,
interleavings and effect are common to the hypotheses. Different finite memories at different
rounds embed into their maximum dimension. Only interleavings 0,...,n-2 are used. -/
structure AdaptiveTest (A B : Type) [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (n : ℕ) where
  memory : ℕ
  memory_pos : 0 < memory
  initial : Matrix (Fin memory × A) (Fin memory × A) ℂ
  initial_density : IsDensityMatrix initial
  between : ℕ → Superop (Fin memory × B) (Fin memory × A)
  between_channels : ∀ k, IsChannel (between k)
  effect : Matrix (Fin memory × B) (Fin memory × B) ℂ
  effect_valid : IsEffect effect

/-- PDF p.8: input after k completed calls and interleavings. -/
def adaptiveInput {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : AdaptiveTest A B n) (F : Superop A B) :
    ℕ → Matrix (Fin P.memory × A) (Fin P.memory × A) ℂ
  | 0 => P.initial
  | k + 1 => P.between k (idTensorSuperop (R := Fin P.memory) F (adaptiveInput P F k))

/-- PDF p.8: acceptance under the supplied channel. Exactly n calls for n>0;
the unused n=0 term is explicitly zero. -/
def adaptiveAccept {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : AdaptiveTest A B n) (F : Superop A B) : ℝ :=
  if n = 0 then 0 else effectProb P.effect
    (idTensorSuperop (R := Fin P.memory) F (adaptiveInput P F (n - 1)))

/-- PDF pp.8–9, (3.3): fixed-error adaptive type-II infimum. For n>0 and epsilon in
(0,1), the always-accept test is feasible and errors lie in [0,1]. Finite Dmax bounds
the infimum strictly away from zero at each fixed positive n. No minimum is asserted. -/
def adaptiveBeta {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : ℕ) (epsilon : ℝ) (N M : Superop A B) : ℝ :=
  sInf {b : ℝ | ∃ P : AdaptiveTest A B n,
    1 - epsilon ≤ adaptiveAccept P N ∧ b = adaptiveAccept P M}

/-- PDF pp.8–9: parallel test with normalized pure block input and reference isomorphic
to the whole input block. Purification and Schmidt compression give the full testing region. -/
structure ParallelTest (A B : Type) [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (n : ℕ) where
  input : EuclideanSpace ℂ ((Fin n → A) × (Fin n → A))
  input_unit : IsState input
  effect : Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ
  effect_valid : IsEffect effect

/-- PDF p.9: acceptance after n parallel channel calls. -/
def parallelAccept {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : ParallelTest A B n) (F : Superop A B) : ℝ :=
  effectProb P.effect (idTensorSuperop (R := Fin n → A) (channelPower F n)
    (pureDensity P.input))

/-- PDF p.9: fixed-error infimum restricted to parallel tests. -/
def parallelBeta {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : ℕ) (epsilon : ℝ) (N M : Superop A B) : ℝ :=
  sInf {b : ℝ | ∃ P : ParallelTest A B n,
    1 - epsilon ≤ parallelAccept P N ∧ b = parallelAccept P M}

/-- Sanity: CP order is reflexive, including the zero channel difference. -/
example {A B : Type} [Fintype A] [Fintype B] (F : Superop A B) : CPLe F F := by
  refine ⟨0, ?_, ?_⟩
  · intro r X hX
    change (0 : Matrix (Fin r × B) (Fin r × B) ℂ).PosSemidef
    exact Matrix.PosSemidef.zero
  · intro X
    simp

/-- Sanity: zero dilation gives the zero map with no normalization condition. -/
example {A B E : Type} [Fintype A] [Fintype E] (X : Matrix A A ℂ) :
    dilationMap (0 : Matrix (B × E) A ℂ) X = 0 := by
  ext i j
  simp [dilationMap, traceRight]

/-- Sanity: the initial adaptive state is independent of the unknown channel. -/
example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : AdaptiveTest A B n) (F G : Superop A B) :
    adaptiveInput P F 0 = adaptiveInput P G 0 := by
  rfl

/-- Sanity: the one-dimensional identical state has zero sandwiched divergence. -/
example (alpha : ℝ) : stateRenyi alpha (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  simp [stateRenyi, SupportIncluded, sandwichedTrace, supportPower, cfc_one]

/-- Sanity: regularizing identically zero block divergences gives zero. -/
example : regularize (fun _ => 0) = 0 := by
  simp [regularize]

end QAlgorithms.Papers.Independent.Information100.P71


