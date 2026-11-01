-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P89
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:25:47.820654+00:00
-- url     : https://prove2.me/theorems/085956c0-ffa3-4d90-b312-f5a7824e8d03
-- title:
--   Definitions for Rate-distance tradeoff and resource costs for all-optical quantum repeaters
-- statement:
--   The objects the formalized statements of *Rate-distance tradeoff and resource costs for all-optical quantum repeaters* (arXiv:1603.01353) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Devices`: Source p.5: admissible device parameters; zero delay and zero chip attenuation are allowed.
--   - `etaSD`: Source p.5: source--detector product.
--   - `etaGHZ`: Source p.5: conditional single-photon survival after GHZ heralding.
--   - `chipSurvival`: Source p.5: survival through one chip feedforward step.
--   - `fiberSurvival`: Source p.5: survival through the final fiber feedforward step.
--   - `ghzSuccess`: Source p.7: one six-source GHZ factory heralds with this probability.
--   - `copiesWeight`: Independent copies of an explicitly specified finite experiment.
--   - `heraldLaw`: Push a finite experiment to a Boolean herald.
--   - `anyLaw`: Select a successful copy from independent parallel attempts.
--   - `allLaw`: Require success of every independent copy.
--   - `andLaw`: Two independent subexperiments both have to succeed.
--   - `successes`: The number of successes in a vector of Bernoulli outcomes.
--   - `countLaw`: Independent-trial count law, summed over the actual bit outcomes.
--   - `balancedSize`: Source p.7: equal-size successful fusion consumes exactly two photons.
--   - `leafSourceCount`: Source p.7: six sources per GHZ attempt, two nB-fold daughter stacks per fusion level.
--   - `NaiveSources`: Source p.7: simultaneous source labels including nmeas top-level copies.
--   - `naiveFusionSuccess`: Source p.7: conditional success Q_l of unboosted fusion at level l.
--   - `naiveClusterLaw`: Source pp.7--8: actual recursive cluster-herald experiment. Each andLaw occurrence uses independent daughter copies and an independent physical fusion trial.
--   - `finalMeasurementSuccess`: Source p.7: survival of all 4m X measurements and the single Y measurement.
--   - `naiveFinalLaw`: Source pp.7--8: final cluster selected from nmeas complete independent attempts.
--   - `boostedFactor`: Source p.8: ancillary-source/detector polynomial in boosted Bell success.
--   - `bankFusionSuccess`: Source p.8: boosted fusion of the surviving inputs before level l.
--   - `TreeBits`: Source p.11: survival flags for each child and its b1 grandchildren in a depth-two tree.
--   - `treeWeight`: Independent physical losses on the photons used by a logical measurement.
--   - `treeXEvent`: Indirect root-Z/logical-X: some child and all its grandchildren survive.
--   - `treeZEvent`: Logical Z: each child survives or can be recovered from a surviving leaf.
--   - `depthTwoLogicalXSuccess`: Source p.11: depth-two logical-X success probability from the physical loss experiment. This scalar is distinct from the frozen QAlgorithms.logicalX stabilizer operator.
--   - `logicalZ`: Depth-two logical-Z probability, computed from the physical loss experiment.
--   - `travelingFactor`: Source pp.10--11: C, traveling-photon survival before the half-link.
--   - `stationaryFactor`: Source pp.10--11: B, stationary survival before the complete herald round trip.
--   - `travelingSurvival`: Source p.10: survival of an outer photon to its detector or Bell measurement.
--   - `stationarySurvival`: Source p.10: retained photon survival including the round-trip herald delay.
--   - `linkBellSuccess`: Source p.11, Eq.(7): boosted Bell-trial probability on a half-link pair.
--   - `PauliBasis`: Appendix A p.15: the three Pauli measurement bases.
--   - `basisObservable`: The frozen Pauli matrices, with false labelling the positive eigenvalue.
--   - `pauliProjector`: Appendix A p.15: spectral projector onto the outcome r (eigenvalue (-1)^r).
--   - `conditionalZ`: Conditional Z gate determined by a previous measurement outcome.
--   - `zOutcomeFlip`: Fig.8(a),(b): X/Y outcome flips; a Z measurement is unaffected.
--   - `hadamardBasis`: Fig.8(c): basis after moving a measurement across a Hadamard.
--   - `hadamardOutcomeFlip`: Fig.8(c): H Y H = -Y, so the Y result is flipped.
--   - `effectDiscard`: Subnormalized residual operator after consuming the measured register. For an effect E, this equals tracing that register after its measurement branch. Its trace is branch probability; it retains the correlations with an arbitrary unmeasured reference register.
--   - `unitaryBranch`: Apply a unitary on the surviving register to a subnormalized branch.
--   - `latePauliBranch`: Fig.8(a),(b), left: MA on a; its outcome feeds conditional Z on b; Pauli outcome r on b feeds the later unitary U on the surviving register. Both a and b are consumed.
--   - `earlyPauliBranch`: Fig.8(a),(b), right: measure b before MA; remove conditional Z, relabel its outcome and update the downstream control of U. The stored early outcome is t.
-- source:
--   Rate-distance tradeoff and resource costs for all-optical quantum repeaters, arXiv:1603.01353v4, https://arxiv.org/abs/1603.01353v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
Statements from Pant--Krovi--Englund--Guha, arXiv:1603.01353v4.
The local classical experiments implement the source's loss-only model. They exclude
multiphoton emission, dark counts, mode mismatch and depolarization. They do not define an
operational secret-key capacity. Device lengths and times use consistent units.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P89

open scoped BigOperators ComplexConjugate

-- Accepted probability primitives: symbol true is success; choose n x is zero for x > n.
open QAlgorithms.Papers.Independent.Information100.P54 (binomialMass)
open QAlgorithms.Papers.Independent.Information100.P56 (bernoulli)

noncomputable section

/-- Source p.5: admissible device parameters; zero delay and zero chip attenuation are allowed. -/
structure Devices where
  etaS : ℝ
  etaD : ℝ
  etaC : ℝ
  alpha : ℝ
  beta : ℝ
  tauS : ℝ
  tauF : ℝ
  cChip : ℝ
  cFiber : ℝ
  etaS_pos : 0 < etaS
  etaS_le : etaS ≤ 1
  etaD_pos : 0 < etaD
  etaD_le : etaD ≤ 1
  etaC_pos : 0 < etaC
  etaC_le : etaC ≤ 1
  alpha_pos : 0 < alpha
  beta_nonneg : 0 ≤ beta
  tauS_nonneg : 0 ≤ tauS
  tauF_nonneg : 0 ≤ tauF
  cChip_pos : 0 < cChip
  cFiber_pos : 0 < cFiber

/-- Source p.5: source--detector product. -/
def etaSD (d : Devices) : ℝ := d.etaS * d.etaD

/-- Source p.5: conditional single-photon survival after GHZ heralding. -/
def etaGHZ (d : Devices) : ℝ := etaSD d / (2 - etaSD d)

/-- Source p.5: survival through one chip feedforward step. -/
def chipSurvival (d : Devices) : ℝ := Real.exp (-d.beta * d.tauS * d.cChip)

/-- Source p.5: survival through the final fiber feedforward step. -/
def fiberSurvival (d : Devices) : ℝ := Real.exp (-d.alpha * d.tauF * d.cFiber)

/-- Source p.7: one six-source GHZ factory heralds with this probability. -/
def ghzSuccess (d : Devices) : ℝ := (etaSD d * (2 - etaSD d)) ^ 3 / 32

/-- Independent copies of an explicitly specified finite experiment. -/
def copiesWeight {A : Type*} (w : A → ℝ) (n : ℕ) : (Fin n → A) → ℝ :=
  fun x => ∏ i, w (x i)

/-- Push a finite experiment to a Boolean herald. -/
def heraldLaw {A : Type*} [Fintype A] (w : A → ℝ) (E : A → Prop) : Bool → ℝ := by
  classical
  exact fun b => ∑ a, if (E a ↔ b = true) then w a else 0

/-- Select a successful copy from independent parallel attempts. -/
def anyLaw (n : ℕ) (w : Bool → ℝ) : Bool → ℝ :=
  heraldLaw (copiesWeight w n) (fun x => ∃ i, x i = true)

/-- Require success of every independent copy. -/
def allLaw (n : ℕ) (w : Bool → ℝ) : Bool → ℝ :=
  heraldLaw (copiesWeight w n) (fun x => ∀ i, x i = true)

/-- Two independent subexperiments both have to succeed. -/
def andLaw (w v : Bool → ℝ) : Bool → ℝ :=
  heraldLaw (fun x : Bool × Bool => w x.1 * v x.2)
    (fun x => x.1 = true ∧ x.2 = true)

/-- The number of successes in a vector of Bernoulli outcomes. -/
def successes {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, if x i then 1 else 0

/-- Independent-trial count law, summed over the actual bit outcomes. -/
def countLaw (n : ℕ) (p : ℝ) (x : ℕ) : ℝ :=
  ∑ z, if successes z = x then copiesWeight (bernoulli p) n z else 0

example (d : Devices) (h : etaSD d = 1) : ghzSuccess d = (1 : ℝ) / 32 := by
  norm_num [ghzSuccess, h]

example (p : ℝ) : bernoulli p true = p := rfl

example (p : ℝ) : binomialMass 0 p 1 = 0 := by simp [binomialMass]

/-- Source p.7: equal-size successful fusion consumes exactly two photons. -/
def balancedSize : ℕ → ℕ
  | 0 => 3
  | k + 1 => 2 * balancedSize k - 2

/-- Source p.7: six sources per GHZ attempt, two nB-fold daughter stacks per fusion level. -/
def leafSourceCount (nGHZ nB : ℕ) : ℕ → ℕ
  | 0 => 6 * nGHZ
  | k + 1 => (2 * nB) * leafSourceCount nGHZ nB k

/-- Source p.7: simultaneous source labels including nmeas top-level copies. -/
abbrev NaiveSources (k nGHZ nB nMeas : ℕ) :=
  Fin nMeas × Fin (leafSourceCount nGHZ nB k)

example : balancedSize 0 = 3 := rfl

example (g b : ℕ) : leafSourceCount g b 0 = 6 * g := rfl

/-- Source p.7: conditional success Q_l of unboosted fusion at level l. -/
def naiveFusionSuccess (d : Devices) (l : ℕ) : ℝ :=
  (etaGHZ d * chipSurvival d ^ l) ^ 2 / 2

/-- Source pp.7--8: actual recursive cluster-herald experiment. Each andLaw occurrence uses
independent daughter copies and an independent physical fusion trial. -/
def naiveClusterLaw (d : Devices) (nGHZ nB : ℕ) : ℕ → Bool → ℝ
  | 0 => anyLaw nGHZ (bernoulli (ghzSuccess d))
  | l + 1 => anyLaw nB
      (andLaw (andLaw (naiveClusterLaw d nGHZ nB l) (naiveClusterLaw d nGHZ nB l))
        (bernoulli (naiveFusionSuccess d (l + 1))))

/-- Source p.7: survival of all 4m X measurements and the single Y measurement. -/
def finalMeasurementSuccess (d : Devices) (k m : ℕ) : ℝ :=
  (etaGHZ d * chipSurvival d ^ (k + 1)) ^ (4 * m + 1)

/-- Source pp.7--8: final cluster selected from nmeas complete independent attempts. -/
def naiveFinalLaw (d : Devices) (k m nGHZ nB nMeas : ℕ) : Bool → ℝ :=
  anyLaw nMeas (andLaw (naiveClusterLaw d nGHZ nB k)
    (bernoulli (finalMeasurementSuccess d k m)))

example (d : Devices) (g b : ℕ) :
    naiveClusterLaw d g b 0 = anyLaw g (bernoulli (ghzSuccess d)) := rfl

/-- Source p.8: ancillary-source/detector polynomial in boosted Bell success. -/
def boostedFactor (d : Devices) : ℝ := (etaSD d) ^ 2 / 2 + (etaSD d) ^ 4 / 4

example (d : Devices) (h : etaSD d = 1) : boostedFactor d = (3 : ℝ) / 4 := by
  norm_num [boostedFactor, h]

/-- Source p.8: boosted fusion of the surviving inputs before level l. -/
def bankFusionSuccess (d : Devices) (l : ℕ) : ℝ :=
  (etaGHZ d * chipSurvival d ^ (l + 1)) ^ 2 * boostedFactor d

/-- Source p.11: survival flags for each child and its b1 grandchildren in a depth-two tree. -/
abbrev TreeBits (b0 b1 : ℕ) := Fin b0 → Fin (b1 + 1) → Bool

/-- Independent physical losses on the photons used by a logical measurement. -/
def treeWeight (b0 b1 : ℕ) (p : ℝ) : TreeBits b0 b1 → ℝ :=
  fun z => ∏ i, ∏ j, bernoulli p (z i j)

/-- Indirect root-Z/logical-X: some child and all its grandchildren survive. -/
def treeXEvent {b0 b1 : ℕ} (z : TreeBits b0 b1) : Prop :=
  ∃ i, ∀ j, z i j = true

/-- Logical Z: each child survives or can be recovered from a surviving leaf. -/
def treeZEvent {b0 b1 : ℕ} (z : TreeBits b0 b1) : Prop :=
  ∀ i, ∃ j, z i j = true

/-- Source p.11: depth-two logical-X success probability from the physical loss experiment.
This scalar is distinct from the frozen QAlgorithms.logicalX stabilizer operator. -/
def depthTwoLogicalXSuccess (b0 b1 : ℕ) (p : ℝ) : ℝ := by
  classical
  exact ∑ z, if treeXEvent z then treeWeight b0 b1 p z else 0

/-- Depth-two logical-Z probability, computed from the physical loss experiment. -/
def logicalZ (b0 b1 : ℕ) (p : ℝ) : ℝ := by
  classical
  exact ∑ z, if treeZEvent z then treeWeight b0 b1 p z else 0

example : treeXEvent (fun (_ : Fin 1) (_ : Fin 1) => true) := by
  exact ⟨0, fun _ => rfl⟩

/-- Source pp.10--11: C, traveling-photon survival before the half-link. -/
def travelingFactor (d : Devices) (k : ℕ) : ℝ :=
  chipSurvival d ^ (k + 2) * etaGHZ d * d.etaC

/-- Source pp.10--11: B, stationary survival before the complete herald round trip. -/
def stationaryFactor (d : Devices) (k : ℕ) : ℝ :=
  travelingFactor d k * fiberSurvival d

/-- Source p.10: survival of an outer photon to its detector or Bell measurement. -/
def travelingSurvival (d : Devices) (k n : ℕ) (L : ℝ) : ℝ :=
  Real.exp (-d.alpha * L / (2 * (n : ℝ))) * travelingFactor d k

/-- Source p.10: retained photon survival including the round-trip herald delay. -/
def stationarySurvival (d : Devices) (k n : ℕ) (L : ℝ) : ℝ :=
  Real.exp (-d.alpha * L / (n : ℝ)) * stationaryFactor d k

/-- Source p.11, Eq.(7): boosted Bell-trial probability on a half-link pair. -/
def linkBellSuccess (d : Devices) (k n : ℕ) (L : ℝ) : ℝ :=
  travelingSurvival d k n L ^ 2 * boostedFactor d

/-- Appendix A p.15: the three Pauli measurement bases. -/
inductive PauliBasis where
  | X
  | Y
  | Z
  deriving DecidableEq

/-- The frozen Pauli matrices, with false labelling the positive eigenvalue. -/
def basisObservable : PauliBasis → Matrix Bool Bool ℂ
  | .X => QAlgorithms.pauliX
  | .Y => QAlgorithms.pauliY
  | .Z => QAlgorithms.pauliZ

/-- Appendix A p.15: spectral projector onto the outcome r (eigenvalue (-1)^r). -/
def pauliProjector (a : PauliBasis) (r : Bool) : Matrix Bool Bool ℂ :=
  (2⁻¹ : ℂ) • (1 + if r then -basisObservable a else basisObservable a)

/-- Conditional Z gate determined by a previous measurement outcome. -/
def conditionalZ (i : Bool) : Matrix Bool Bool ℂ :=
  if i then QAlgorithms.pauliZ else 1

/-- Fig.8(a),(b): X/Y outcome flips; a Z measurement is unaffected. -/
def zOutcomeFlip (a : PauliBasis) (i : Bool) : Bool :=
  match a with
  | .X => i
  | .Y => i
  | .Z => false

/-- Fig.8(c): basis after moving a measurement across a Hadamard. -/
def hadamardBasis : PauliBasis → PauliBasis
  | .X => .Z
  | .Y => .Y
  | .Z => .X

/-- Fig.8(c): H Y H = -Y, so the Y result is flipped. -/
def hadamardOutcomeFlip : PauliBasis → Bool
  | .X => false
  | .Y => true
  | .Z => false

/-- Subnormalized residual operator after consuming the measured register. For an effect E,
this equals tracing that register after its measurement branch. Its trace is branch probability;
it retains the correlations with an arbitrary unmeasured reference register. -/
def effectDiscard {A R : Type*} [Fintype A]
    (E : Matrix A A ℂ) (rho : Matrix (A × R) (A × R) ℂ) : Matrix R R ℂ :=
  fun r s => ∑ a, ∑ b, E b a * rho (a, r) (b, s)

example {R : Type*} (rho : Matrix (Unit × R) (Unit × R) ℂ) :
    effectDiscard (1 : Matrix Unit Unit ℂ) rho =
      (fun r s => rho ((), r) ((), s)) := by
  ext r s
  simp [effectDiscard]

/-- Apply a unitary on the surviving register to a subnormalized branch. -/
def unitaryBranch {R : Type*} [Fintype R] [DecidableEq R]
    (U : Matrix.unitaryGroup R ℂ) (rho : Matrix R R ℂ) : Matrix R R ℂ :=
  (U : Matrix R R ℂ) * rho * (U : Matrix R R ℂ).conjTranspose

/-- Fig.8(a),(b), left: MA on a; its outcome feeds conditional Z on b; Pauli outcome r
on b feeds the later unitary U on the surviving register. Both a and b are consumed. -/
def latePauliBranch {O R : Type*} [Fintype R] [DecidableEq R]
    (MA : O → Matrix Bool Bool ℂ) (feed : O → Bool)
    (U : O → Bool → Matrix.unitaryGroup R ℂ) (a : PauliBasis) (o : O) (r : Bool)
    (rho : Matrix ((Bool × Bool) × R) ((Bool × Bool) × R) ℂ) : Matrix R R ℂ :=
  unitaryBranch (U o r) (effectDiscard
    (Matrix.kronecker ((MA o).conjTranspose * MA o)
      ((conditionalZ (feed o)).conjTranspose * pauliProjector a r * conditionalZ (feed o))) rho)

/-- Fig.8(a),(b), right: measure b before MA; remove conditional Z, relabel its outcome
and update the downstream control of U. The stored early outcome is t. -/
def earlyPauliBranch {O R : Type*} [Fintype R] [DecidableEq R]
    (MA : O → Matrix Bool Bool ℂ) (feed : O → Bool)
    (U : O → Bool → Matrix.unitaryGroup R ℂ) (a : PauliBasis) (o : O) (t : Bool)
    (rho : Matrix ((Bool × Bool) × R) ((Bool × Bool) × R) ℂ) : Matrix R R ℂ :=
  unitaryBranch (U o (xor t (zOutcomeFlip a (feed o))))
    (effectDiscard (Matrix.kronecker ((MA o).conjTranspose * MA o) (pauliProjector a t)) rho)

example : hadamardBasis .X = .Z := rfl

example : hadamardOutcomeFlip .Y = true := rfl

example (i : Bool) : zOutcomeFlip .Z i = false := rfl

end

end QAlgorithms.Papers.Independent.Intakenext100.P89


