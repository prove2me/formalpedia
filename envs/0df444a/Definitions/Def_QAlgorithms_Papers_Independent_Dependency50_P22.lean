-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22
-- name    : QAlgorithms_Papers_Independent_Dependency50_P22
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T14:17:00.989279+00:00
-- url     : https://prove2.me/theorems/8977d1d1-20dd-4200-bc27-12fd4d47b17e
-- title:
--   Definitions for Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask)
-- statement:
--   The objects the formalized statements of *Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask)* (arXiv:1210.4583) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsInstrument`: PDF p.4: countable instruments, with convergence on every operator and a trace-preserving sum. Finite labels are a special case. Each branch is explicitly complex-linear and uses the accepted complete-positivity predicate, including zero branches. In finite dimension this is equivalent to the former unnormalized finite-Kraus characterization.
--   - `CoarseGrains`: PDF p.4: classical postprocessing only; sums are over fibers of the readout.
--   - `instrumentDistance`: PDF p.5, Eq.(1): QC diamond distance, without a factor 1/2. Printed: the maximization in Eq.(1) uses 0<=rho<=I without trace normalization. Changed: require a positive trace-one stabilized input. Why: the named diamond norm and the source's bound of 2 require normalized states; the effect interval alone allows dimension-dependent scaling. No factor 1/2 is introduced. For two instruments the set is nonempty and bounded; no use is made of its value on arbitrary non-linear maps or non-instruments.
--   - `productMap`: PDF p.5: tensor product action on matrix units, for unequal local dimensions as well.
--   - `IsOneWay`: PDF p.5: one broadcaster; all other parties apply outcome-conditioned local channels. These arbitrary local channels permit local ancillas and disposal, without a catalyst.
--   - `ExtendsHistory`: PDF pp.5–6: extend a public history by one conditional one-way instrument. The broadcaster can depend on the entire old label. No intermediate readout is discarded.
--   - `RawRounds`: PDF pp.5–6: raw finite-round histories. Identity rounds allow padding. The readout is applied separately, at the end.
--   - `InRounds`: PDF p.5: r communication rounds followed by a fixed classical readout.
--   - `InFiniteLOCC`: PDF pp.5–6: finite-round union, keeping the round count tied to actual conditional operations.
--   - `InLOCC`: PDF pp.5–6: LOCC uses linked raw histories, coarse-grained into the same final labels. Readouts may change with the prefix, but the retained internal labels do not. This is not the independent-approximation definition of closure below.
--   - `InLOCCClosure`: PDF p.6: closure allows independent finite protocols, with no prefix-link requirement.
--   - `IsSeparableMap`: PDF pp.7–9: finite-dimensional separable CP maps have product Kraus representations. No bound on the number of product Kraus operators is assumed.
--   - `InSEP`: PDF p.7: a separable instrument retains its original classical labels.
--   - `completelyDepolarizing`: PDF p.8: complete depolarization transported from the accepted Fin-indexed channel at noise parameter 1 to the fixed input coordinates. The transport uses the same basis bijection on input and output and retains the trace. Empty coordinates have only the zero operator; source applications always have positive dimension.
--   - `depolarizingInstrument`: PDF p.9: m equally weighted depolarizing branches. Only m>0 is used.
--   - `stochasticInstrument`: PDF p.8: SLOCC success is heralded and is uniform on every input; the extra branch is exactly (1-p) times depolarization, not an arbitrary failure channel.
--   - `sepRadius`: PDF p.9: the exact separable mixing coefficient, with real exponent N/2-1.
--   - `loccRadius`: PDF p.9: R_LOCC = R_SEP/(m^2 D^4), including the boundary.
--   - `HasFineBound`: PDF pp.10,16–19: a finite local Kraus realization of a conditional instrument. There is one broadcaster k. Its finite local Kraus instrument is complete across o and its private Kraus index; other parties use normalized conditional local channels. The total number of global single-Kraus product branches is bounded by B. Private Kraus labels can be retained until the final coarse-graining; they are not additional broadcasts, and subsequent public choices only use the readout f o.
--   - `executeRounds`: PDF pp.16–17: execution of a history-dependent finite protocol, including its subnormalized branches. The initial label 0 is deterministic. An extra label stores the full old history and current outcome.
--   - `QConfig`: Fixed-dimension qubit coordinates are the finite-dimensional instance d_k=2 of Config. Bit 0 and bit 1 have their usual order, with party 0 the most significant wire, matching the frozen Qubits convention.
--   - `qubitBits`: Coordinate identification with the frozen Boolean qubit registers; no wire reversal.
--   - `tensorTwo`: PDF p.11: tensor product of two local matrices, in the fixed two-party coordinates.
--   - `qubitProjector`: PDF p.11: |b><b|.
--   - `witnessT`: PDF p.11, Eq.(12): the two local Kraus matrices T_1 and T_2.
--   - `eq11Instrument`: PDF pp.10–11, Eqs.(10)–(12): the explicit flagged instrument. Labels 0,1,2 mean 00,01,10 respectively; the classical register is retained. This is unrelated to Information100.P27.witnessInstrument, a memory-copying matrix.
--   - `paddedWitness`: PDF p.12: append a fourth zero branch; labels are 00,01,10,11.
--   - `weakM`: PDF p.11, Eq.(13): the weak local measurement. Used only for 0<epsilon<=1.
--   - `trialInstrument`: PDF pp.11–12: exactly the source's stopped-trial Kraus families, with mu=i+1. The zero-trial instrument is the identity in branch 00; it is used only for initialization.
--   - `sepGapInstrument`: PDF p.14, Eq.(23): the second, explicitly separable, three-branch instrument.
--   - `excitation`: PDF p.13: a single-excitation three-qubit basis index; A=0, B=1, C=2.
--   - `wVector`: PDF pp.13,19, Eq.(32): include the vacuum coefficient sqrt(1-sum x). The W domain below supplies nonnegativity and sum x<=1.
--   - `CanonicalWCoordinates`: PDF p.13: the paper's unique-coordinate convention, including the biseparable and fully separable cases. In the biseparable case the earlier nonzero party has the larger weight.
--   - `wLocalUnitary`: PDF p.13: the tensor product of three local unitaries.
--   - `RepresentsW`: PDF p.13: canonical W coordinates of a normalized pure state, up to local unitaries.
--   - `IsPureW`: PDF p.13: pure W-class domain includes its biseparable and product boundaries.
--   - `wConcurrence`: PDF p.13, Eq.(20): nonnegative ordered weights are selected by max and min. The distinguished party is fixed, and the other parties are its two cyclic successors. This definition records the nonstrict function only; Lemma 2's strictness is deferred.
--   - `pureWCost`: PDF pp.13–14: the pure-state cost evaluated using the unique canonical coordinates. On IsPureW this is an infimum of a nonempty singleton. Its value outside the pure W domain is never used; no arbitrary zero extension to GHZ states is intended.
--   - `WEnsemble`: PDF p.14, Eq.(22): normalized finite/countable decompositions supported on the pure W domain. Finite decompositions can be padded with zero weights. This explicitly corrects the printed unrestricted "all pure state decompositions", where the pure cost could be undefined.
--   - `IsMixedW`: PDF p.14: mixed W-class states, with density normalization and a supported decomposition. In finite dimension this equals the convex hull specified by the source's compact domain.
--   - `ensembleWCost`: PDF p.14, Eq.(22): expected pure W-cost of a supported decomposition.
--   - `mixedWCost`: PDF p.14, Eq.(22): supported convex roof. The theorem below explicitly asserts attainment. On IsMixedW its feasible set is nonempty and bounded below by zero. The total real infimum's empty-set value outside this domain has no operational meaning.
--   - `branchProbability`: PDF p.4: branch probability is the trace of its subnormalized output.
--   - `conditionalOutput`: PDF pp.4,14: normalization is an interface requiring strictly positive branch probability. For a CP branch on a density input this is its conditional density matrix.
--   - `expectedWCost`: PDF p.14: conditional W-cost is evaluated only on positive-probability branches.
--   - `wKet`: PDF pp.13–14: the normalized W input, with all three excitation amplitudes 1/sqrt(3).
--   - `omegaEntry`: PDF p.14, Eq.(21): the matrix omega in basis 00,01,10,11.
--   - `omegaFlag`: PDF p.14, Eq.(21): distinct classical labels select AC or BC, while the unused qubit is |0>. Each matrix here is normalized; the theorem multiplies each by probability 1/2.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, https://arxiv.org/abs/1210.4583v2

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

/-!
Paper-local operational definitions for arXiv:1210.4583v2, §§2–4.
No additional shared state is an argument of any protocol. Local CP maps include
local ancilla preparation and disposal. Coordinates and output labels are fixed.
Intermediate labels are natural numbers; pairing preserves the full public history.
They may be read out differently at each prefix, without discarding that history.
The topology on finite-outcome instruments is the relative pointwise topology;
on finite-dimensional complex-linear maps it is the unique vector-space topology.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

-- Accepted dependent-product coordinates; no local Config declaration.
open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.4: countable instruments, with convergence on every operator and a trace-preserving sum.
Finite labels are a special case. Each branch is explicitly complex-linear and uses the
accepted complete-positivity predicate, including zero branches. In finite dimension this
is equivalent to the former unnormalized finite-Kraus characterization. -/
def IsInstrument {I O : Type*} [Fintype I] (J : O → Superop I I) : Prop :=
  (∀ o, ∃ E : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ,
    Entanglement.IsCompletelyPositive E ∧ ∀ X, J o X = E X) ∧
  (∀ X, Summable (fun o => J o X)) ∧
  ∀ X, (∑' o, J o X).trace = X.trace

/-- PDF p.4: classical postprocessing only; sums are over fibers of the readout. -/
def CoarseGrains {I A B : Type*} [Fintype I] [DecidableEq B]
    (J : A → Superop I I) (K : B → Superop I I) : Prop :=
  ∃ f : A → B, ∀ b X, K b X = ∑' a, if f a = b then J a X else 0

/-- PDF p.5, Eq.(1): QC diamond distance, without a factor 1/2.
Printed: the maximization in Eq.(1) uses 0<=rho<=I without trace normalization.
Changed: require a positive trace-one stabilized input. Why: the named diamond norm
and the source's bound of 2 require normalized states; the effect interval alone
allows dimension-dependent scaling. No factor 1/2 is introduced.
For two instruments the set is nonempty and bounded; no use is made of its value
on arbitrary non-linear maps or non-instruments. -/
def instrumentDistance {I O : Type*} [Fintype I] [DecidableEq I]
    (J K : O → Superop I I) : ℝ :=
  sSup {v : ℝ | ∃ rho : Matrix (I × I) (I × I) ℂ,
    IsDensityMatrix rho ∧ v = ∑' o,
      traceNorm (idTensorSuperop (R := I) (fun X => J o X - K o X) rho)}

/-- PDF p.5: tensor product action on matrix units, for unequal local dimensions as well. -/
def productMap {N : ℕ} {d : Fin N → ℕ}
    (L : (k : Fin N) → Superop (Fin (d k)) (Fin (d k))) :
    Superop (Config d) (Config d) :=
  fun X y z => ∑ a : Config d, ∑ b : Config d,
    X a b * ∏ k, L k (Matrix.single (a k) (b k) 1) (y k) (z k)

/-- PDF p.5: one broadcaster; all other parties apply outcome-conditioned local channels.
These arbitrary local channels permit local ancillas and disposal, without a catalyst. -/
def IsOneWay {N : ℕ} (d : Fin N → ℕ)
    (J : ℕ → Superop (Config d) (Config d)) : Prop :=
  IsInstrument J ∧ ∃ k : Fin N,
    ∃ L : ℕ → (j : Fin N) → Superop (Fin (d j)) (Fin (d j)),
      IsInstrument (fun o => L o k) ∧
      (∀ o j, j ≠ k → IsChannel (L o j)) ∧
      ∀ o, J o = productMap (L o)

/-- PDF pp.5–6: extend a public history by one conditional one-way instrument.
The broadcaster can depend on the entire old label. No intermediate readout is discarded. -/
def ExtendsHistory {N : ℕ} (d : Fin N → ℕ)
    (J K : ℕ → Superop (Config d) (Config d)) : Prop :=
  ∃ B : ℕ → ℕ → Superop (Config d) (Config d),
    (∀ h, IsOneWay d (B h)) ∧
    ∀ t X, K t X = B (Nat.unpair t).1 (Nat.unpair t).2 (J (Nat.unpair t).1 X)

/-- PDF pp.5–6: raw finite-round histories. Identity rounds allow padding.
The readout is applied separately, at the end. -/
inductive RawRounds {N : ℕ} (d : Fin N → ℕ) :
    ℕ → (ℕ → Superop (Config d) (Config d)) → Prop
  | first (J) (h : IsOneWay d J) : RawRounds d 1 J
  | next {r J K} (h : RawRounds d r J) (link : ExtendsHistory d J K) :
      RawRounds d (r + 1) K

/-- PDF p.5: r communication rounds followed by a fixed classical readout. -/
def InRounds {N : ℕ} {O : Type*} [Countable O] [DecidableEq O]
    (d : Fin N → ℕ) (r : ℕ) (J : O → Superop (Config d) (Config d)) : Prop :=
  IsInstrument J ∧ ∃ K, RawRounds d r K ∧ CoarseGrains K J

/-- PDF pp.5–6: finite-round union, keeping the round count tied to actual conditional operations. -/
def InFiniteLOCC {N : ℕ} {O : Type*} [Countable O] [DecidableEq O]
    (d : Fin N → ℕ) (J : O → Superop (Config d) (Config d)) : Prop :=
  ∃ r : ℕ, 0 < r ∧ InRounds d r J

/-- PDF pp.5–6: LOCC uses linked raw histories, coarse-grained into the same final labels.
Readouts may change with the prefix, but the retained internal labels do not.
This is not the independent-approximation definition of closure below. -/
def InLOCC {N : ℕ} {O : Type*} [Countable O] [DecidableEq O]
    (d : Fin N → ℕ) (J : O → Superop (Config d) (Config d)) : Prop :=
  IsInstrument J ∧ ∃ K : ℕ → ℕ → Superop (Config d) (Config d),
    (∀ n, ∃ r : ℕ, 0 < r ∧ RawRounds d r (K n)) ∧
    (∀ n, ExtendsHistory d (K n) (K (n + 1))) ∧
    ∃ A : ℕ → O → Superop (Config d) (Config d),
      (∀ n, IsInstrument (A n) ∧ CoarseGrains (K n) (A n)) ∧
      Filter.Tendsto (fun n => instrumentDistance (A n) J) Filter.atTop (nhds 0)

/-- PDF p.6: closure allows independent finite protocols, with no prefix-link requirement. -/
def InLOCCClosure {N : ℕ} {O : Type*} [Countable O] [DecidableEq O]
    (d : Fin N → ℕ) (J : O → Superop (Config d) (Config d)) : Prop :=
  IsInstrument J ∧ ∃ A : ℕ → O → Superop (Config d) (Config d),
    (∀ n, InFiniteLOCC d (A n)) ∧
    Filter.Tendsto (fun n => instrumentDistance (A n) J) Filter.atTop (nhds 0)

/-- PDF pp.7–9: finite-dimensional separable CP maps have product Kraus representations.
No bound on the number of product Kraus operators is assumed. -/
def IsSeparableMap {N : ℕ} (d : Fin N → ℕ)
    (E : Superop (Config d) (Config d)) : Prop :=
  ∃ n : ℕ, ∃ A : Fin n → (k : Fin N) → Matrix (Fin (d k)) (Fin (d k)) ℂ,
    ∀ X, E X = krausApply (fun i a b => ∏ k, A i k (a k) (b k)) X

/-- PDF p.7: a separable instrument retains its original classical labels. -/
def InSEP {N : ℕ} {O : Type*} (d : Fin N → ℕ)
    (J : O → Superop (Config d) (Config d)) : Prop :=
  IsInstrument J ∧ ∀ o, IsSeparableMap d (J o)

/-- PDF p.8: complete depolarization transported from the accepted Fin-indexed channel
at noise parameter 1 to the fixed input coordinates. The transport uses the same basis
bijection on input and output and retains the trace. Empty coordinates have only the
zero operator; source applications always have positive dimension. -/
def completelyDepolarizing {I : Type*} [Fintype I] [DecidableEq I] : Superop I I :=
  if h : 0 < Fintype.card I then
    let e := Fintype.equivFin I
    fun X i j => QuditFidelity.depolarizingMap (Fintype.card I) h 1
      (fun a b => X (e.symm a) (e.symm b)) (e i) (e j)
  else fun _ => 0

/-- PDF p.9: m equally weighted depolarizing branches. Only m>0 is used. -/
def depolarizingInstrument {I : Type*} [Fintype I] [DecidableEq I]
    (m : ℕ) : Fin m → Superop I I :=
  fun _ X => ((m : ℂ)⁻¹) • completelyDepolarizing X

/-- PDF p.8: SLOCC success is heralded and is uniform on every input;
the extra branch is exactly (1-p) times depolarization, not an arbitrary failure channel. -/
def stochasticInstrument {I : Type*} [Fintype I] [DecidableEq I]
    {m : ℕ} (p : ℝ) (J : Fin m → Superop I I) : Option (Fin m) → Superop I I
  | some o => fun X => (p : ℂ) • J o X
  | none => fun X => ((1 - p : ℝ) : ℂ) • completelyDepolarizing X

/-- PDF p.9: the exact separable mixing coefficient, with real exponent N/2-1. -/
def sepRadius (N m D : ℕ) : ℝ :=
  ((m : ℝ) * D ^ 2 * Real.rpow 2 ((N : ℝ) / 2 - 1) + 1)⁻¹

/-- PDF p.9: R_LOCC = R_SEP/(m^2 D^4), including the boundary. -/
def loccRadius (N m D : ℕ) : ℝ := sepRadius N m D / ((m : ℝ) ^ 2 * D ^ 4)

example {I : Type*} [Fintype I] :
    Entanglement.IsCompletelyPositive (LinearMap.id : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) := by
  intro r X hX
  exact hX

example {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
    (J : Fin m → Superop I I) (X : Matrix I I ℂ) :
    stochasticInstrument 0 J none X = completelyDepolarizing X := by
  simp [stochasticInstrument]

example : sepRadius 2 1 1 = 1 / 2 := by
  norm_num [sepRadius]

/-- PDF pp.10,16–19: a finite local Kraus realization of a conditional instrument.
There is one broadcaster k. Its finite local Kraus instrument is complete across o
and its private Kraus index; other parties use normalized conditional local channels.
The total number of global single-Kraus product branches is bounded by B.
Private Kraus labels can be retained until the final coarse-graining; they are not
additional broadcasts, and subsequent public choices only use the readout f o. -/
def HasFineBound {N : ℕ} (d : Fin N → ℕ)
    (J : ℕ → Superop (Config d) (Config d)) (B : ℕ) : Prop :=
  ∃ k : Fin N, ∃ s : ℕ, ∃ f : Fin s → ℕ,
    ∃ mult : Fin s → Fin N → ℕ,
    ∃ A : (o : Fin s) → (j : Fin N) →
      Fin (mult o j) → Matrix (Fin (d j)) (Fin (d j)) ℂ,
      IsInstrument (fun o => krausApply (A o k)) ∧
      (∀ o j, j ≠ k → IsKrausFamily (A o j)) ∧
      (∑ o, ∏ j, mult o j) ≤ B ∧
      ∀ p X, J p X = ∑ o, ∑ u : (j : Fin N) → Fin (mult o j),
        if f o = p then
          conjSuperop (fun a b => ∏ j, A o j (u j) (a j) (b j)) X else 0

/-- PDF pp.16–17: execution of a history-dependent finite protocol, including its subnormalized branches.
The initial label 0 is deterministic. An extra label stores the full old history and current outcome. -/
def executeRounds {N : ℕ} {d : Fin N → ℕ}
    (B : ℕ → ℕ → ℕ → Superop (Config d) (Config d)) :
    ℕ → ℕ → Superop (Config d) (Config d)
  | 0 => fun h X => if h = 0 then X else 0
  | n + 1 => fun h X => B n (Nat.unpair h).1 (Nat.unpair h).2
      (executeRounds B n (Nat.unpair h).1 X)

example {N : ℕ} {d : Fin N → ℕ}
    (B : ℕ → ℕ → ℕ → Superop (Config d) (Config d))
    (X : Matrix (Config d) (Config d) ℂ) : executeRounds B 0 0 X = X := by
  simp [executeRounds]

/-- Fixed-dimension qubit coordinates are the finite-dimensional instance d_k=2 of Config.
Bit 0 and bit 1 have their usual order, with party 0 the most significant wire,
matching the frozen Qubits convention. -/
abbrev QConfig (n : ℕ) := Config (fun _ : Fin n => 2)

/-- Coordinate identification with the frozen Boolean qubit registers; no wire reversal. -/
def qubitBits {n : ℕ} (x : QConfig n) : Qubits n := fun k => decide (x k = 1)

/-- PDF p.11: tensor product of two local matrices, in the fixed two-party coordinates. -/
def tensorTwo (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (QConfig 2) (QConfig 2) ℂ :=
  fun x y => A (x 0) (y 0) * B (x 1) (y 1)

/-- PDF p.11: |b><b|. -/
def qubitProjector (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single b b 1

/-- PDF p.11, Eq.(12): the two local Kraus matrices T_1 and T_2. -/
def witnessT : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Matrix.diagonal ![((Real.sqrt 3)⁻¹ : ℂ), ((Real.sqrt 3)⁻¹ : ℂ)],
    Matrix.diagonal ![((Real.sqrt 6)⁻¹ : ℂ), (Real.sqrt (2 / 3) : ℂ)]]

/-- PDF pp.10–11, Eqs.(10)–(12): the explicit flagged instrument.
Labels 0,1,2 mean 00,01,10 respectively; the classical register is retained.
This is unrelated to Information100.P27.witnessInstrument, a memory-copying matrix. -/
def eq11Instrument : Fin 3 → Superop (QConfig 2) (QConfig 2) :=
  ![conjSuperop (tensorTwo (qubitProjector 1) (qubitProjector 1)),
    krausApply (fun i : Fin 2 => tensorTwo (witnessT i) (qubitProjector 0)),
    krausApply (fun i : Fin 2 => tensorTwo (qubitProjector 0) (witnessT i))]

/-- PDF p.12: append a fourth zero branch; labels are 00,01,10,11. -/
def paddedWitness : Fin 4 → Superop (QConfig 2) (QConfig 2) :=
  ![eq11Instrument 0, eq11Instrument 1, eq11Instrument 2, fun _ => 0]

/-- PDF p.11, Eq.(13): the weak local measurement. Used only for 0<epsilon<=1. -/
def weakM (epsilon : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![Matrix.diagonal ![(Real.sqrt (1 - epsilon) : ℂ), 1],
    Matrix.diagonal ![(Real.sqrt epsilon : ℂ), 0]]

/-- PDF pp.11–12: exactly the source's stopped-trial Kraus families, with mu=i+1.
The zero-trial instrument is the identity in branch 00; it is used only for initialization. -/
def trialInstrument (epsilon : ℝ) (nu : ℕ) :
    Fin 4 → Superop (QConfig 2) (QConfig 2) :=
  ![conjSuperop (tensorTwo (weakM epsilon 0 ^ nu) (weakM epsilon 0 ^ nu)),
    krausApply (fun i : Fin nu => tensorTwo (weakM epsilon 0 ^ (i.val + 1))
      (weakM epsilon 1 * weakM epsilon 0 ^ i.val)),
    krausApply (fun i : Fin nu => tensorTwo (weakM epsilon 1 * weakM epsilon 0 ^ i.val)
      (weakM epsilon 0 ^ (i.val + 1))),
    krausApply (fun i : Fin nu => tensorTwo (weakM epsilon 1 * weakM epsilon 0 ^ i.val)
      (weakM epsilon 1 * weakM epsilon 0 ^ i.val))]

/-- PDF p.14, Eq.(23): the second, explicitly separable, three-branch instrument. -/
def sepGapInstrument : Fin 3 → Superop (QConfig 2) (QConfig 2) :=
  let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![((Real.sqrt 2)⁻¹ : ℂ), 1]
  ![conjSuperop (tensorTwo A (qubitProjector 0)),
    conjSuperop (tensorTwo (qubitProjector 0) A),
    conjSuperop (tensorTwo (qubitProjector 1) (qubitProjector 1))]

example : qubitBits (fun _ : Fin 2 => (0 : Fin 2)) = fun _ => false := by
  funext k
  simp [qubitBits]

example (X : Matrix (QConfig 2) (QConfig 2) ℂ) : paddedWitness 3 X = 0 := rfl

example : weakM 1 0 = qubitProjector 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [weakM, qubitProjector, Matrix.diagonal, Matrix.single]

/-- PDF p.13: a single-excitation three-qubit basis index; A=0, B=1, C=2. -/
def excitation (k : Fin 3) : QConfig 3 := fun j => if j = k then 1 else 0

/-- PDF pp.13,19, Eq.(32): include the vacuum coefficient sqrt(1-sum x).
The W domain below supplies nonnegativity and sum x<=1. -/
def wVector (x : Fin 3 → ℝ) : EuclideanSpace ℂ (QConfig 3) :=
  (Real.sqrt (1 - ∑ k, x k) : ℂ) • ket (fun _ => 0) +
    ∑ k : Fin 3, (Real.sqrt (x k) : ℂ) • ket (excitation k)

/-- PDF p.13: the paper's unique-coordinate convention, including the biseparable and
fully separable cases. In the biseparable case the earlier nonzero party has the larger weight. -/
def CanonicalWCoordinates (x : Fin 3 → ℝ) : Prop :=
  (∀ k, 0 ≤ x k) ∧ (∑ k, x k) ≤ 1 ∧
    ((∀ k, 0 < x k) ∨
      ((∃ k, x k = 0 ∧ ∀ j, j ≠ k → 0 < x j) ∧ (∑ k, x k) = 1 ∧
        ((0 < x 0 ∧ x 1 ≤ x 0 ∧ x 2 ≤ x 0) ∨ (x 0 = 0 ∧ x 2 ≤ x 1))) ∨
      x = ![1, 0, 0])

/-- PDF p.13: the tensor product of three local unitaries. -/
def wLocalUnitary (U : Fin 3 → Matrix.unitaryGroup (Fin 2) ℂ) :
    Matrix (QConfig 3) (QConfig 3) ℂ :=
  fun a b => ∏ k, (U k : Matrix (Fin 2) (Fin 2) ℂ) (a k) (b k)

/-- PDF p.13: canonical W coordinates of a normalized pure state, up to local unitaries. -/
def RepresentsW (x : Fin 3 → ℝ) (psi : EuclideanSpace ℂ (QConfig 3)) : Prop :=
  CanonicalWCoordinates x ∧ IsState psi ∧
    ∃ U : Fin 3 → Matrix.unitaryGroup (Fin 2) ℂ, psi = act (wLocalUnitary U) (wVector x)

/-- PDF p.13: pure W-class domain includes its biseparable and product boundaries. -/
def IsPureW (psi : EuclideanSpace ℂ (QConfig 3)) : Prop := ∃ x, RepresentsW x psi

/-- PDF p.13, Eq.(20): nonnegative ordered weights are selected by max and min.
The distinguished party is fixed, and the other parties are its two cyclic successors.
This definition records the nonstrict function only; Lemma 2's strictness is deferred. -/
def wConcurrence (star : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  let a := max (x (star + 1)) (x (star + 2))
  let b := min (x (star + 1)) (x (star + 2))
  if a = 0 then 0 else 2 * Real.sqrt (x star * a) + (2 / 3 : ℝ) * b * Real.sqrt (x star / a)

/-- PDF pp.13–14: the pure-state cost evaluated using the unique canonical coordinates.
On IsPureW this is an infimum of a nonempty singleton. Its value outside the pure
W domain is never used; no arbitrary zero extension to GHZ states is intended. -/
def pureWCost (star : Fin 3) (psi : EuclideanSpace ℂ (QConfig 3)) : ℝ :=
  sInf {v : ℝ | ∃ x, RepresentsW x psi ∧ v = wConcurrence star x}

/-- PDF p.14, Eq.(22): normalized finite/countable decompositions supported on the pure W domain.
Finite decompositions can be padded with zero weights. This explicitly corrects the printed
unrestricted "all pure state decompositions", where the pure cost could be undefined. -/
structure WEnsemble (rho : Matrix (QConfig 3) (QConfig 3) ℂ) where
  weight : ℕ → ℝ
  vector : ℕ → EuclideanSpace ℂ (QConfig 3)
  nonnegative : ∀ i, 0 ≤ weight i
  summable_weight : Summable weight
  total : ∑' i, weight i = 1
  normalized : ∀ i, IsState (vector i)
  pure_domain : ∀ i, IsPureW (vector i)
  summable_density : Summable (fun i => (weight i : ℂ) • pureDensity (vector i))
  density : rho = ∑' i, (weight i : ℂ) • pureDensity (vector i)

/-- PDF p.14: mixed W-class states, with density normalization and a supported decomposition.
In finite dimension this equals the convex hull specified by the source's compact domain. -/
def IsMixedW (rho : Matrix (QConfig 3) (QConfig 3) ℂ) : Prop :=
  IsDensityMatrix rho ∧ Nonempty (WEnsemble rho)

/-- PDF p.14, Eq.(22): expected pure W-cost of a supported decomposition. -/
def ensembleWCost (star : Fin 3) {rho : Matrix (QConfig 3) (QConfig 3) ℂ}
    (e : WEnsemble rho) : ℝ := ∑' i, e.weight i * pureWCost star (e.vector i)

/-- PDF p.14, Eq.(22): supported convex roof. The theorem below explicitly asserts attainment.
On IsMixedW its feasible set is nonempty and bounded below by zero. The total real
infimum's empty-set value outside this domain has no operational meaning. -/
def mixedWCost (star : Fin 3) (rho : Matrix (QConfig 3) (QConfig 3) ℂ) : ℝ :=
  sInf {v : ℝ | ∃ e : WEnsemble rho, v = ensembleWCost star e}

/-- PDF p.4: branch probability is the trace of its subnormalized output. -/
def branchProbability {I : Type*} [Fintype I] (E : Superop I I)
    (rho : Matrix I I ℂ) : ℝ := (E rho).trace.re

/-- PDF pp.4,14: normalization is an interface requiring strictly positive branch probability.
For a CP branch on a density input this is its conditional density matrix. -/
def conditionalOutput {I : Type*} [Fintype I] (E : Superop I I)
    (rho : Matrix I I ℂ) (_hp : 0 < branchProbability E rho) : Matrix I I ℂ :=
  (((branchProbability E rho)⁻¹ : ℝ) : ℂ) • E rho

/-- PDF p.14: conditional W-cost is evaluated only on positive-probability branches. -/
def expectedWCost (star : Fin 3) (E : Superop (QConfig 3) (QConfig 3))
    (rho : Matrix (QConfig 3) (QConfig 3) ℂ) : ℝ :=
  let p := branchProbability E rho
  if hp : 0 < p then p * mixedWCost star (conditionalOutput E rho hp) else 0

/-- PDF pp.13–14: the normalized W input, with all three excitation amplitudes 1/sqrt(3). -/
def wKet : EuclideanSpace ℂ (QConfig 3) :=
  ((Real.sqrt 3)⁻¹ : ℂ) • ∑ k : Fin 3, ket (excitation k)

/-- PDF p.14, Eq.(21): the matrix omega in basis 00,01,10,11. -/
def omegaEntry (a b : Fin 2 × Fin 2) : ℂ :=
  if a = (0, 1) ∧ b = (0, 1) then 1 / 3
  else if a = (1, 0) ∧ b = (1, 0) then 2 / 3
  else if (a = (0, 1) ∧ b = (1, 0)) ∨ (a = (1, 0) ∧ b = (0, 1)) then 4 / 9
  else 0

/-- PDF p.14, Eq.(21): distinct classical labels select AC or BC, while the unused qubit is |0>.
Each matrix here is normalized; the theorem multiplies each by probability 1/2. -/
def omegaFlag (o : Fin 2) : Matrix (QConfig 3) (QConfig 3) ℂ :=
  fun x y => if o = 0 then
    if x 1 = 0 ∧ y 1 = 0 then omegaEntry (x 0, x 2) (y 0, y 2) else 0
  else if x 0 = 0 ∧ y 0 = 0 then omegaEntry (x 1, x 2) (y 1, y 2) else 0

example : wConcurrence 0 ![0, (1 / 2 : ℝ), 1 / 2] = 0 := by
  norm_num [wConcurrence]

example : wConcurrence 0 ![(1 / 3 : ℝ), 1 / 3, 1 / 3] = 8 / 9 := by
  have hweights : (![(1 / 3 : ℝ), 1 / 3, 1 / 3] : Fin 3 → ℝ) =
      fun _ => (1 / 3 : ℝ) := by
    ext i
    fin_cases i <;> rfl
  have hs : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 1 / 3 by norm_num) using 1 <;> norm_num
  rw [hweights]
  norm_num [wConcurrence, hs]

example : omegaEntry (0, 1) (1, 0) = 4 / 9 := by
  norm_num [omegaEntry]

example (star : Fin 3) (rho : Matrix (QConfig 3) (QConfig 3) ℂ) :
    expectedWCost star (fun _ => 0) rho = 0 := by
  simp [expectedWCost, branchProbability]

end QAlgorithms.Papers.Independent.Dependency50.P22


