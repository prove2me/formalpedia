-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
-- name    : QAlgorithms_Papers_Independent_Dependency50_P41
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T16:46:15.583535+00:00
-- url     : https://prove2.me/theorems/6f2b84b7-74b3-4ef0-b0ec-59ebaa482bbf
-- title:
--   Definitions for Entanglement Cost of Quantum Channels
-- statement:
--   The objects the formalized statements of *Entanglement Cost of Quantum Channels* (arXiv:1108.5357) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `logExtended`: PDF p.4: an extended base-two logarithm; zero has value minus infinity.
--   - `logRank`: PDF pp.4,20: unconditional alternative entropy is extended log rank.
--   - `conditionalH0`: PDF p.4, Definition 2 (7): supremum over normalized B states, with extended log.
--   - `cqOperator`: PDF pp.4–5: a quantum-classical operator in the indicated fixed label vectors.
--   - `cqBall`: PDF p.5 (14): positive classical-block perturbations in FULL trace norm. No trace-at-most-one condition is imposed on the perturbations.
--   - `smoothH0`: PDF pp.5,20–21: Definition 4 with its printed SUP corrected to INF, as required by (A6), (A10), (A13). This is trace-norm smooth log-rank, not fidelity Hmax.
--   - `commutingSmoothH0`: PDF pp.20–21, Lemma 28: the same infimum restricted to commuting candidates.
--   - `labelPower`: PDF p.21: the product orthonormal labels for the n-fold classical register.
--   - `maximallyEntangled`: PDF p.6: normalized maximally entangled density of Schmidt rank m, m>0 in protocols.
--   - `simulationInput`: PDF p.6 (20): Alice has the input AND her resource share; Bob has the other share. The Fin(a*m) register is the product input/resource register, input coordinate first.
--   - `ChannelSimulation`: PDF p.6, Definition 10: an actual entanglement-assisted LOCC protocol. Alice's final register has dimension one; Bob receives the entire output.
--   - `simulationChannel`: PDF p.6 (20): the induced whole-input simulation channel.
--   - `channelError`: PDF p.5, Definition 5: full stabilized induced trace norm. Stabilization by the whole input dimension suffices in finite dimension. All matrices, not just product or density inputs, are optimized. On channel differences the set is nonempty and bounded.
--   - `blockChannel`: PDF pp.6–7: the WHOLE tensor-power channel on Fin(a^n), via matrix units. No product-state assumption is made on the block input.
--   - `resourceRate`: PDF p.6, Definition 11: rate is the EReal limsup of log2(M_n)/n. The n=0 term is zero by real division; it has no effect at infinity.
--   - `channelCost`: PDF pp.6–7: OPERATIONAL parallel channel cost, defined before its formula. One protocol per block works for every input and arbitrary reference; the full diamond error tends to zero. Finite protocols suffice for asymptotic approximation of LOCC protocols; no bound on the number of rounds is imposed across block lengths.
--   - `StateDilution`: PDF pp.3,6: actual LOCC dilution from the normalized Schmidt-rank-m resource.
--   - `stateCost`: PDF p.3 (3), pp.5–6: operational STATE cost. The full trace-norm error tends to zero, equivalently the purified-distance error in Definition 6 tends to zero. The definition does not assume the state-cost regularization theorem.
--   - `formationOutputs`: PDF pp.7,9: all pure states on input and a full input-sized reference. The reference is written first; E acts on the second tensor factor.
--   - `singleLetterCost`: PDF p.9 (38): single-letter formation maximum; attainment is in the statements.
--   - `blockMaxima`: PDF p.7 (22): the maxima are over all block purifications, including entangled inputs.
--   - `KrausDecomposition`: PDF pp.7–9: normalized Kraus decompositions, with sum K†K=I_INPUT.
--   - `branchEntropy`: PDF p.7 (23): a zero-probability branch contributes exactly zero.
--   - `krausWorstCost`: PDF p.7 (23): choose the Kraus family BEFORE taking the worst input.
--   - `EntanglementBreaking`: PDF p.13, footnote 16: entanglement breaking in all finite positive dimensions. The accepted separable-density predicate is used, rather than its qubit-only channel wrapper.
--   - `stateCostOutputs`: PDF p.13 (69): state-cost outputs, kept distinct from formation outputs.
--   - `spinY`: PDF p.15 (75): Pauli Y in the computational basis.
--   - `qubitErasure`: PDF p.18 (93): the accepted single erasure channel with its Option flag reindexed to the third qutrit coordinate. The first two coordinates carry the signal.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, https://arxiv.org/abs/1108.5357v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-! Paper-local interfaces and statements from arXiv:1108.5357v3.
All logarithms are in bits. Operational costs are defined using actual local
instruments and maximally entangled resources, independently of formation.
Definitions with an infimum use EReal where the empty set or zero operator
can occur. See the unit's audit for the correction of printed Definition 4.
Compilation and independent moderation are pending the batch handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)
open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)
open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4: an extended base-two logarithm; zero has value minus infinity. -/
def logExtended (x : ℝ) : EReal := if x ≤ 0 then ⊥ else (Real.logb 2 x : EReal)

/-- PDF pp.4,20: unconditional alternative entropy is extended log rank. -/
def logRank {I : Type*} [Fintype I] (rho : Op I) : EReal :=
  logExtended (Matrix.rank rho : ℝ)

/-- PDF p.4, Definition 2 (7): supremum over normalized B states, with extended log. -/
def conditionalH0 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Op (A × B)) : EReal :=
  sSup {h | ∃ sigma : Op B, IsDensityMatrix sigma ∧
    h = logExtended ((Matrix.trace (supportProjection rho * Matrix.kronecker (1 : Op A) sigma)).re)}

/-- PDF pp.4–5: a quantum-classical operator in the indicated fixed label vectors. -/
def cqOperator {A B K : Type*} [Fintype K]
    (v : K → EuclideanSpace ℂ B) (blocks : K → Op A) : Op (A × B) :=
  ∑ k, Matrix.kronecker (blocks k) (pureDensity (v k))

/-- PDF p.5 (14): positive classical-block perturbations in FULL trace norm.
No trace-at-most-one condition is imposed on the perturbations. -/
def cqBall {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] (rho : Op (A × B))
    (v : K → EuclideanSpace ℂ B) (epsilon : ℝ) : Set (Op (A × B)) :=
  {sigma | (∃ blocks : K → Op A, (∀ k, (blocks k).PosSemidef) ∧
    sigma = cqOperator v blocks) ∧ traceNorm (rho - sigma) ≤ epsilon}

/-- PDF pp.5,20–21: Definition 4 with its printed SUP corrected to INF,
as required by (A6), (A10), (A13). This is trace-norm smooth log-rank, not fidelity Hmax. -/
def smoothH0 {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] (rho : Op (A × B))
    (v : K → EuclideanSpace ℂ B) (epsilon : ℝ) : EReal :=
  sInf (conditionalH0 '' cqBall rho v epsilon)

/-- PDF pp.20–21, Lemma 28: the same infimum restricted to commuting candidates. -/
def commutingSmoothH0 {A B : Type} {K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] (rho : Op (A × B))
    (v : K → EuclideanSpace ℂ B) (epsilon : ℝ) : EReal :=
  sInf (conditionalH0 '' {sigma ∈ cqBall rho v epsilon | sigma * rho = rho * sigma})

/-- PDF p.21: the product orthonormal labels for the n-fold classical register. -/
def labelPower {B K : Type*} (v : K → EuclideanSpace ℂ B) (n : ℕ) :
    (Fin n → K) → EuclideanSpace ℂ (Fin n → B) :=
  fun k => WithLp.toLp 2 (fun x => ∏ i, v (k i) (x i))

/-- PDF p.6: normalized maximally entangled density of Schmidt rank m, m>0 in protocols. -/
def maximallyEntangled (m : ℕ) : Op (Fin m × Fin m) :=
  if hm : 0 < m then
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    pureDensity (finiteMaxEntangled (Fin m))
  else 0

/-- PDF p.6 (20): Alice has the input AND her resource share; Bob has the other share.
The Fin(a*m) register is the product input/resource register, input coordinate first. -/
def simulationInput {a m : ℕ} (rho : Op (Fin a)) : Op (Fin (a * m) × Fin m) :=
  let split : Fin (a * m) → Fin a × Fin m := finProdFinEquiv.symm
  fun x y => rho (split x.1).1 (split y.1).1 *
    maximallyEntangled m ((split x.1).2, x.2) ((split y.1).2, y.2)

/-- PDF p.6, Definition 10: an actual entanglement-assisted LOCC protocol.
Alice's final register has dimension one; Bob receives the entire output. -/
structure ChannelSimulation (a b : ℕ) where
  resourceRank : ℕ
  rank_positive : 0 < resourceRank
  operation : Superop (Fin (a * resourceRank) × Fin resourceRank) (Fin 1 × Fin b)
  localProtocol : FiniteLOCC operation
  cptp : IsChannel operation

/-- PDF p.6 (20): the induced whole-input simulation channel. -/
def simulationChannel {a b : ℕ} (P : ChannelSimulation a b) : Superop (Fin a) (Fin b) :=
  fun rho => traceLeft (P.operation (simulationInput rho))

/-- PDF p.5, Definition 5: full stabilized induced trace norm. Stabilization by the
whole input dimension suffices in finite dimension. All matrices, not just product
or density inputs, are optimized. On channel differences the set is nonempty and bounded. -/
def channelError {a b : ℕ} (F E : Superop (Fin a) (Fin b)) : ℝ :=
  sSup {r | ∃ X : Op (Fin a × Fin a), traceNorm X ≤ 1 ∧
    r = traceNorm (idTensorSuperop (R := Fin a) (fun rho => F rho - E rho) X)}

/-- PDF pp.6–7: the WHOLE tensor-power channel on Fin(a^n), via matrix units.
No product-state assumption is made on the block input. -/
def blockChannel {a b : ℕ} (E : Superop (Fin a) (Fin b)) (n : ℕ) :
    Superop (Fin (a ^ n)) (Fin (b ^ n)) :=
  let inEquiv : (Fin n → Fin a) ≃ Fin (a ^ n) := finFunctionFinEquiv
  let outEquiv : (Fin n → Fin b) ≃ Fin (b ^ n) := finFunctionFinEquiv
  fun X y z => ∑ x : Fin n → Fin a, ∑ w : Fin n → Fin a,
    X (inEquiv x) (inEquiv w) *
      ∏ i, E (Matrix.single (x i) (w i) 1) (outEquiv.symm y i) (outEquiv.symm z i)

/-- PDF p.6, Definition 11: rate is the EReal limsup of log2(M_n)/n.
The n=0 term is zero by real division; it has no effect at infinity. -/
def resourceRate (M : ℕ → ℕ) : EReal :=
  Filter.limsup (fun n : ℕ => ((Real.logb 2 (M n) / (n : ℝ) : ℝ) : EReal)) atTop

/-- PDF pp.6–7: OPERATIONAL parallel channel cost, defined before its formula.
One protocol per block works for every input and arbitrary reference; the full
diamond error tends to zero. Finite protocols suffice for asymptotic approximation
of LOCC protocols; no bound on the number of rounds is imposed across block lengths. -/
def channelCost {a b : ℕ} (E : Superop (Fin a) (Fin b)) : EReal :=
  sInf {r | ∃ P : (n : ℕ) → ChannelSimulation (a ^ n) (b ^ n),
    Tendsto (fun n => channelError (simulationChannel (P n)) (blockChannel E n))
      atTop (nhds 0) ∧ r = resourceRate (fun n => (P n).resourceRank)}

/-- PDF pp.3,6: actual LOCC dilution from the normalized Schmidt-rank-m resource. -/
structure StateDilution (a b : ℕ) where
  resourceRank : ℕ
  rank_positive : 0 < resourceRank
  operation : Superop (Fin resourceRank × Fin resourceRank) (Fin a × Fin b)
  localProtocol : FiniteLOCC operation
  cptp : IsChannel operation

/-- PDF p.3 (3), pp.5–6: operational STATE cost. The full trace-norm error tends
to zero, equivalently the purified-distance error in Definition 6 tends to zero.
The definition does not assume the state-cost regularization theorem. -/
def stateCost {a b : ℕ} (rho : Op (Fin a × Fin b)) : EReal :=
  sInf {r | ∃ P : (n : ℕ) → StateDilution (a ^ n) (b ^ n),
    Tendsto (fun n => traceNorm ((P n).operation (maximallyEntangled (P n).resourceRank) -
      (Matrix.of fun (x y : Fin (a ^ n) × Fin (b ^ n)) => ∏ i : Fin n,
        rho ((finFunctionFinEquiv.symm x.1) i, (finFunctionFinEquiv.symm x.2) i)
          ((finFunctionFinEquiv.symm y.1) i, (finFunctionFinEquiv.symm y.2) i))))
      atTop (nhds 0) ∧ r = resourceRate (fun n => (P n).resourceRank)}

/-- PDF pp.7,9: all pure states on input and a full input-sized reference.
The reference is written first; E acts on the second tensor factor. -/
def formationOutputs {a b : ℕ} (E : Superop (Fin a) (Fin b)) : Set ℝ :=
  {r | ∃ psi : EuclideanSpace ℂ (Fin a × Fin a), ‖psi‖ = 1 ∧
    r = formation (idTensorSuperop (R := Fin a) E (pureDensity psi))}

/-- PDF p.9 (38): single-letter formation maximum; attainment is in the statements. -/
def singleLetterCost {a b : ℕ} (E : Superop (Fin a) (Fin b)) : ℝ :=
  sSup (formationOutputs E)

/-- PDF p.7 (22): the maxima are over all block purifications, including entangled inputs. -/
def blockMaxima {a b : ℕ} (E : Superop (Fin a) (Fin b)) : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsGreatest (formationOutputs (blockChannel E n))
    (singleLetterCost (blockChannel E n))

/-- PDF pp.7–9: normalized Kraus decompositions, with sum K†K=I_INPUT. -/
structure KrausDecomposition {a b : ℕ} (E : Superop (Fin a) (Fin b)) where
  size : ℕ
  matrix : Fin size → Matrix (Fin b) (Fin a) ℂ
  complete : IsKrausFamily matrix
  represents : ∀ rho, E rho = krausApply matrix rho

/-- PDF p.7 (23): a zero-probability branch contributes exactly zero. -/
def branchEntropy {a b : ℕ} (K : Matrix (Fin b) (Fin a) ℂ) (rho : Op (Fin a)) : ℝ :=
  let omega := K * rho * Kᴴ
  let p := omega.trace.re
  if p = 0 then 0 else p * vnEntropy (((p⁻¹ : ℝ) : ℂ) • omega)

/-- PDF p.7 (23): choose the Kraus family BEFORE taking the worst input. -/
def krausWorstCost {a b : ℕ} {E : Superop (Fin a) (Fin b)}
    (D : KrausDecomposition E) : ℝ :=
  sSup {r | ∃ rho : Op (Fin a), IsDensityMatrix rho ∧
    r = ∑ k, branchEntropy (D.matrix k) rho}

/-- PDF p.13, footnote 16: entanglement breaking in all finite positive dimensions.
The accepted separable-density predicate is used, rather than its qubit-only channel wrapper. -/
def EntanglementBreaking {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : Superop (Fin a) (Fin b)) : Prop :=
  letI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  ∀ psi : EuclideanSpace ℂ (Fin a × Fin a), ‖psi‖ = 1 →
    QAlgorithms.Entanglement.IsSeparableDensity (idTensorSuperop E (pureDensity psi))

/-- PDF p.13 (69): state-cost outputs, kept distinct from formation outputs. -/
def stateCostOutputs {a b : ℕ} (E : Superop (Fin a) (Fin b)) : Set EReal :=
  {r | ∃ psi : EuclideanSpace ℂ (Fin a × Fin a), ‖psi‖ = 1 ∧
    r = stateCost (idTensorSuperop E (pureDensity psi))}

/-- PDF p.15 (75): Pauli Y in the computational basis. -/
def spinY : Op (Fin 2) := !![0, -Complex.I; Complex.I, 0]

/-- PDF p.18 (93): the accepted single erasure channel with its Option flag
reindexed to the third qutrit coordinate. The first two coordinates carry the signal. -/
def qubitErasure (p : ℝ) : Superop (Fin 2) (Fin 3) :=
  let label : Fin 3 → Option (Fin 2) :=
    fun x => if h : x.val < 2 then some ⟨x.val, h⟩ else none
  fun rho => Matrix.of fun x y =>
    QAlgorithms.Papers.Independent.Information100.P58.singleErasure 2 p rho (label x) (label y)

/-! Small sanity examples for the local interfaces; no source theorem is proved. -/

example : logExtended 0 = ⊥ := by simp [logExtended]

example {I : Type*} [Fintype I] : logRank (0 : Op I) = ⊥ := by
  simp [logRank, logExtended]

example {A B : Type*} (v : Fin 0 → EuclideanSpace ℂ B) (blocks : Fin 0 → Op A) :
    cqOperator v blocks = 0 := by simp [cqOperator]

example {A B : Type*} (rho : Op (A × B)) :
    groupedPower rho 0 = (fun _ _ => 1) := by ext x y; simp [groupedPower]

example (a b : ℕ) : FiniteLOCC (fun X : Op (Fin a × Fin b) => X) :=
  FiniteLOCC.identity a b

example : maximallyEntangled 1 = (1 : Op (Fin 1 × Fin 1)) := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  have hx : x.1 = x.2 := Subsingleton.elim _ _
  have hy : y.1 = y.2 := Subsingleton.elim _ _
  simp [maximallyEntangled, finiteMaxEntangled, pureDensity, Matrix.one_apply, hxy, hx, hy]

example {a b : ℕ} (rho : Op (Fin a)) :
    branchEntropy (0 : Matrix (Fin b) (Fin a) ℂ) rho = 0 := by
  simp [branchEntropy]

example : spinY 0 1 = -Complex.I := rfl

example (rho : Op (Fin 2)) (p : ℝ) : qubitErasure p rho 2 2 = (p : ℂ) * rho.trace := by
  simp [qubitErasure, QAlgorithms.Papers.Independent.Information100.P58.singleErasure]

example : resourceRate (fun _ => 1) = 0 := by
  simp [resourceRate]

example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Op (A × B)) :
    conditionalEntropy rho = vnEntropy rho - vnEntropy (traceLeft rho) := rfl

example {B K : Type*} (v : K → EuclideanSpace ℂ B) (k : Fin 0 → K) (x : Fin 0 → B) :
    labelPower v 0 k x = 1 := by simp [labelPower]

example {A B K : Type*} [Fintype A] [Fintype B] [Fintype K]
    [DecidableEq A] [DecidableEq B] (rho : Op (A × B))
    (v : K → EuclideanSpace ℂ B) (epsilon : ℝ) :
    cqBall rho v epsilon ⊆ cqBall rho v (epsilon + 1) := by
  intro sigma hs
  exact ⟨hs.1, le_trans hs.2 (by linarith)⟩

example {I : Type} [Fintype I] (psi : EuclideanSpace ℂ I) (hpsi : ‖psi‖ = 1) :
    ∃ e : PureEnsemble I, pureAverage e = pureDensity psi := by
  refine ⟨{
    size := 1
    prob := fun _ => 1
    vector := fun _ => psi
    nonneg := fun _ => by norm_num
    total := by simp
    normalized := fun _ => hpsi
  }, ?_⟩
  simp [pureAverage]

example : Nonempty (ChannelSimulation 1 1) := by
  refine ⟨{
    resourceRank := 1
    rank_positive := by decide
    operation := fun X => X
    localProtocol := FiniteLOCC.identity 1 1
    cptp := ?_
  }⟩
  exact ⟨1, fun _ => 1, by simp [IsKrausFamily], fun rho => by simp [krausApply]⟩

example : Nonempty (StateDilution 1 1) := by
  refine ⟨{
    resourceRank := 1
    rank_positive := by decide
    operation := fun X => X
    localProtocol := FiniteLOCC.identity 1 1
    cptp := ?_
  }⟩
  exact ⟨1, fun _ => 1, by simp [IsKrausFamily], fun rho => by simp [krausApply]⟩

end QAlgorithms.Papers.Independent.Dependency50.P41


