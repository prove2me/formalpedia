-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P11
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P11
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:46:53.011429+00:00
-- url     : https://prove2.me/theorems/22f97360-c32f-44b0-9275-7f6d218598b2
-- title:
--   Definitions for On the distributed compression of quantum information
-- statement:
--   The objects the formalized statements of *On the distributed compression of quantum information* (arXiv:quant-ph/0403042) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DistributedBlockCode`: PDF pp.2–3, (2)–(3): an actual blind distributed code. Only the two compressed quantum registers are transmitted; there is no other resource register or message.
--   - `DistributedBlockCode.output`: PDF p.2: independent encoders followed by the joint receiver's decoder. The accepted `both` applies each local map to all matrix blocks, including coherences.
--   - `sourceWordVector`: PDF p.2: tensor word with Alice's and Bob's factors grouped by owner. The empty word is the unit vector of the singleton zero-copy space.
--   - `letterFidelity`: PDF p.2, (2): pure-input squared fidelity, including possible mixed output.
--   - `finiteFidelity`: PDF p.2: the i.i.d. finite source average in (2); repeated labels remain labels.
--   - `DistributedAchievable`: PDF p.3, (3): every positive accuracy and rate slack, then every sufficiently large positive integer block. Dimension one permits zero communication.
--   - `FiniteAchievable`: PDF pp.2–3: achievable rates for the given finite pure ensemble. Validity of p and the pure vectors is supplied in theorem binders, or by explicit constructions.
--   - `sourceMean`: PDF p.2: average density, using the frozen finite-ensemble definition after enumerating the abstract finite label type.
--   - `EnsembleIrreducible`: PDF p.5: no nontrivial orthogonal partition of the positive-probability support. A singleton support is irreducible; a zero-weight letter cannot connect components.
--   - `bellSourceVectors`: PDF p.8, (13), in the order phi+, phi-, psi+, psi-. Both registers are qubits.
--   - `erasureBasis`: PDF p.5, (8): four orthonormal erasure-code words. Fin 4 denotes the fixed most-significant-bit-first two-qubit basis 00,01,10,11 on each party.
--   - `erasureVector`: PDF p.5: the isometric image of the first column of U(4), sampling all pure superpositions in the code subspace, rather than only the four code words.
--   - `erasureFidelity`: PDF p.5 with p.2, (2): Haar-uniform pure ensemble in the whole code subspace, with independent U(4) samples at the n source positions.
--   - `hiddenAlice`: PDF p.11, (23)–(25), in letter order 1,2,3.
--   - `hiddenBob`: PDF p.11, (26)–(28): Bob's original qutrit vectors.
--   - `hiddenBobAfter`: PDF p.11: Bob's vectors after projecting onto |2> and its complement and resetting the |2> branch to |0>. The output on the third letter is pure |0>.
--   - `hiddenJoint`: PDF p.11: the original equiprobable product source, before Bob's local reset.
--   - `hiddenRateA`: PDF p.11: Alice's actual Schumacher rate, from the average marginal density.
--   - `hiddenRateB`: PDF p.11: Bob's actual Schumacher rate after the project/reset operation.
--   - `hiddenComparison`: PDF p.11, (30): the expression from III.3, evaluated on the original source.
--   - `hybridVector`: PDF p.12, (31)–(32): the displayed opposite-parity family. False/true denote 0/1 for the source label and both computational qubits. This is a restriction of scope: the printed universal local-unitary reduction to this family is false.
--   - `hybridQ`: PDF p.13, (33): Alice's measurement-outcome probabilities.
--   - `hybridConditional`: PDF p.13, (33): conditional density on Bob. A zero-probability outcome is assigned |0><0|; it contributes zero to every averaged quantity.
--   - `hybridChi`: PDF p.13: E' Holevo information; H(E') in (36)–(38) is instead H(q).
--   - `hybridPiggyback`: PDF p.13, (35): chi(E'')=1+S(E_B)-S(E_AB), since Alice is a qubit.
--   - `hybridRateA`: PDF p.13, (37): exact hybrid Alice rate; its denominator is always at least one for normalized p and coefficient pairs, including zero probabilities.
-- source:
--   On the distributed compression of quantum information, arXiv:quant-ph/0403042v3, https://arxiv.org/abs/quant-ph/0403042v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27

/-!
Ahn, Doherty, Hayden and Winter, On the distributed compression of quantum information,
quant-ph/0403042v3. Codes reconstruct the supplied pure ensemble in average squared
fidelity, not with a reference. All rates and entropies are in bits/qubits per signal.
Only pinned accepted modules are imported. The universal local normal form on p.12
is false and is deferred in HARD.md; the hybrid result retains its displayed-family scope.
Compilation is pending the mechanical batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P11

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate Matrix
open QAlgorithms.Papers.Independent.Dependency50.P19 (both)
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2–3, (2)–(3): an actual blind distributed code. Only the two compressed
quantum registers are transmitted; there is no other resource register or message. -/
structure DistributedBlockCode (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (n da db : ℕ) where
  length_pos : 0 < n
  alice_dim_pos : 0 < da
  bob_dim_pos : 0 < db
  encodeA : Superop (Fin n → A) (Fin da)
  encodeB : Superop (Fin n → B) (Fin db)
  decode : Superop (Fin da × Fin db) ((Fin n → A) × (Fin n → B))
  alice_channel : IsChannel encodeA
  bob_channel : IsChannel encodeB
  decoder_channel : IsChannel decode

/-- PDF p.2: independent encoders followed by the joint receiver's decoder. The
accepted `both` applies each local map to all matrix blocks, including coherences. -/
def DistributedBlockCode.output {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] {n da db : ℕ}
    (c : DistributedBlockCode A B n da db) :
    Superop ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) :=
  c.decode ∘ both c.encodeA c.encodeB

/-- PDF p.2: tensor word with Alice's and Bob's factors grouped by owner. The
empty word is the unit vector of the singleton zero-copy space. -/
def sourceWordVector {I A B : Type*} (v : I → EuclideanSpace ℂ (A × B))
    {n : ℕ} (w : Fin n → I) : EuclideanSpace ℂ ((Fin n → A) × (Fin n → B)) :=
  WithLp.toLp 2 fun x => ∏ t, v (w t) (x.1 t, x.2 t)

/-- PDF p.2, (2): pure-input squared fidelity, including possible mixed output. -/
def letterFidelity {I A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (v : I → EuclideanSpace ℂ (A × B))
    {n da db : ℕ} (c : DistributedBlockCode A B n da db) (w : Fin n → I) : ℝ :=
  effectProb (pureDensity (sourceWordVector v w)) (c.output (pureDensity (sourceWordVector v w)))

/-- PDF p.2: the i.i.d. finite source average in (2); repeated labels remain labels. -/
def finiteFidelity {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (p : I → ℝ) (v : I → EuclideanSpace ℂ (A × B))
    {n da db : ℕ} (c : DistributedBlockCode A B n da db) : ℝ :=
  ∑ w : Fin n → I, (∏ t, p (w t)) * letterFidelity v c w

/-- PDF p.3, (3): every positive accuracy and rate slack, then every sufficiently
large positive integer block. Dimension one permits zero communication. -/
def DistributedAchievable {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (fidelity : {n da db : ℕ} → DistributedBlockCode A B n da db → ℝ) (ra rb : ℝ) : Prop :=
  ∀ delta > (0 : ℝ), ∀ eps > (0 : ℝ), ∃ N : ℕ, ∀ n : ℕ, N < n →
    ∃ da db : ℕ, ∃ c : DistributedBlockCode A B n da db,
      1 - eps ≤ fidelity c ∧
      Real.logb 2 da / n ≤ ra + delta ∧ Real.logb 2 db / n ≤ rb + delta

/-- PDF pp.2–3: achievable rates for the given finite pure ensemble. Validity of
p and the pure vectors is supplied in theorem binders, or by explicit constructions. -/
def FiniteAchievable {I A B : Type*} [Fintype I] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (p : I → ℝ) (v : I → EuclideanSpace ℂ (A × B))
    (ra rb : ℝ) : Prop :=
  DistributedAchievable (fun c => finiteFidelity p v c) ra rb

/-- PDF p.2: average density, using the frozen finite-ensemble definition after
enumerating the abstract finite label type. -/
def sourceMean {I X : Type*} [Fintype I] (p : I → ℝ)
    (v : I → EuclideanSpace ℂ X) : Matrix X X ℂ :=
  ensembleDensity (fun j => p ((Fintype.equivFin I).symm j))
    (fun j => v ((Fintype.equivFin I).symm j))

/-- PDF p.5: no nontrivial orthogonal partition of the positive-probability support.
A singleton support is irreducible; a zero-weight letter cannot connect components. -/
def EnsembleIrreducible {I X : Type*} [Fintype X] (p : I → ℝ)
    (v : I → EuclideanSpace ℂ X) : Prop :=
  (∃ i, 0 < p i) ∧ ∀ S : Set I,
    (∃ i, 0 < p i ∧ i ∈ S) → (∃ j, 0 < p j ∧ j ∉ S) →
    ∃ i j, 0 < p i ∧ 0 < p j ∧ i ∈ S ∧ j ∉ S ∧ inner ℂ (v i) (v j) ≠ 0

/-- PDF p.8, (13), in the order phi+, phi-, psi+, psi-. Both registers are qubits. -/
def bellSourceVectors : Fin 4 → EuclideanSpace ℂ (Bool × Bool) :=
  let s : ℂ := (Real.sqrt 2 : ℝ)⁻¹
  ![s • (ket (false, false) + ket (true, true)),
    s • (ket (false, false) - ket (true, true)),
    s • (ket (false, true) + ket (true, false)),
    s • (ket (false, true) - ket (true, false))]

/-- PDF p.5, (8): four orthonormal erasure-code words. Fin 4 denotes the fixed
most-significant-bit-first two-qubit basis 00,01,10,11 on each party. -/
def erasureBasis : Fin 4 → EuclideanSpace ℂ (Fin 4 × Fin 4) :=
  let s : ℂ := (Real.sqrt 2 : ℝ)⁻¹
  ![s • (ket (0, 0) + ket (3, 3)), s • (ket (0, 3) + ket (3, 0)),
    s • (ket (1, 1) + ket (2, 2)), s • (ket (2, 1) + ket (1, 2))]

/-- PDF p.5: the isometric image of the first column of U(4), sampling all pure
superpositions in the code subspace, rather than only the four code words. -/
def erasureVector (U : Matrix.unitaryGroup (Fin 4) ℂ) :
    EuclideanSpace ℂ (Fin 4 × Fin 4) :=
  ∑ j : Fin 4, (U : Matrix (Fin 4) (Fin 4) ℂ) j 0 • erasureBasis j

/-- PDF p.5 with p.2, (2): Haar-uniform pure ensemble in the whole code subspace,
with independent U(4) samples at the n source positions. -/
def erasureFidelity {n da db : ℕ} (c : DistributedBlockCode (Fin 4) (Fin 4) n da db) : ℝ :=
  ∫ w : Fin n → Matrix.unitaryGroup (Fin 4) ℂ,
    letterFidelity erasureVector c w ∂Measure.pi (fun _ : Fin n => Schur.unitaryHaar 4)

/-- PDF p.11, (23)–(25), in letter order 1,2,3. -/
def hiddenAlice (alpha : ℝ) : Fin 3 → EuclideanSpace ℂ (Fin 2) :=
  ![ket 0, (Real.sqrt alpha : ℂ) • ket 0 + (Real.sqrt (1 - alpha) : ℂ) • ket 1, ket 1]

/-- PDF p.11, (26)–(28): Bob's original qutrit vectors. -/
def hiddenBob (beta : ℝ) : Fin 3 → EuclideanSpace ℂ (Fin 3) :=
  ![(Real.sqrt (1 - beta) : ℂ) • ket 0 + (Real.sqrt beta : ℂ) • ket 1,
    ket 1, (Real.sqrt (1 - beta) : ℂ) • ket 2 + (Real.sqrt beta : ℂ) • ket 0]

/-- PDF p.11: Bob's vectors after projecting onto |2> and its complement and
resetting the |2> branch to |0>. The output on the third letter is pure |0>. -/
def hiddenBobAfter (beta : ℝ) : Fin 3 → EuclideanSpace ℂ (Fin 3) :=
  ![hiddenBob beta 0, hiddenBob beta 1, ket 0]

/-- PDF p.11: the original equiprobable product source, before Bob's local reset. -/
def hiddenJoint (alpha beta : ℝ) (i : Fin 3) :=
  tensorVec (hiddenAlice alpha i) (hiddenBob beta i)

/-- PDF p.11: Alice's actual Schumacher rate, from the average marginal density. -/
def hiddenRateA (alpha : ℝ) : ℝ :=
  vnEntropy (sourceMean (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenAlice alpha))

/-- PDF p.11: Bob's actual Schumacher rate after the project/reset operation. -/
def hiddenRateB (beta : ℝ) : ℝ :=
  vnEntropy (sourceMean (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenBobAfter beta))

/-- PDF p.11, (30): the expression from III.3, evaluated on the original source. -/
def hiddenComparison (alpha beta : ℝ) : ℝ :=
  (hiddenRateA alpha +
    vnEntropy (sourceMean (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenBob beta)) +
    vnEntropy (sourceMean (fun _ : Fin 3 => (1 / 3 : ℝ)) (hiddenJoint alpha beta))) / 2

/-- PDF p.12, (31)–(32): the displayed opposite-parity family. False/true denote
0/1 for the source label and both computational qubits. This is a restriction of
scope: the printed universal local-unitary reduction to this family is false. -/
def hybridVector (alpha beta : Bool → ℂ) (i : Bool) : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 fun x => if x.2 = Bool.xor x.1 i then
    (if x.1 then beta i else alpha i) else 0

/-- PDF p.13, (33): Alice's measurement-outcome probabilities. -/
def hybridQ (p : Bool → ℝ) (alpha beta : Bool → ℂ) (j : Bool) : ℝ :=
  ∑ i, p i * (if j then Complex.normSq (beta i) else Complex.normSq (alpha i))

/-- PDF p.13, (33): conditional density on Bob. A zero-probability outcome is
assigned |0><0|; it contributes zero to every averaged quantity. -/
def hybridConditional (p : Bool → ℝ) (alpha beta : Bool → ℂ) (j : Bool) :
    Matrix Bool Bool ℂ :=
  if hybridQ p alpha beta j = 0 then pureDensity (ket false) else
    ((hybridQ p alpha beta j)⁻¹ : ℂ) •
      ∑ i, ((p i * (if j then Complex.normSq (beta i) else Complex.normSq (alpha i)) : ℝ) : ℂ) •
        pureDensity (ket (Bool.xor j i))

/-- PDF p.13: E' Holevo information; H(E') in (36)–(38) is instead H(q). -/
def hybridChi (p : Bool → ℝ) (alpha beta : Bool → ℂ) : ℝ :=
  vnEntropy (∑ j, (hybridQ p alpha beta j : ℂ) • hybridConditional p alpha beta j) -
    ∑ j, hybridQ p alpha beta j * vnEntropy (hybridConditional p alpha beta j)

/-- PDF p.13, (35): chi(E'')=1+S(E_B)-S(E_AB), since Alice is a qubit. -/
def hybridPiggyback (p : Bool → ℝ) (alpha beta : Bool → ℂ) : ℝ :=
  let rho := sourceMean p (hybridVector alpha beta)
  1 + vnEntropy (traceLeft rho) - vnEntropy rho

/-- PDF p.13, (37): exact hybrid Alice rate; its denominator is always at least one
for normalized p and coefficient pairs, including zero probabilities. -/
def hybridRateA (p : Bool → ℝ) (alpha beta : Bool → ℂ) : ℝ :=
  let a := shannon (hybridQ p alpha beta) - hybridChi p alpha beta
  a / (a + hybridPiggyback p alpha beta)

section SanityExamples

example {I A B : Type*} (v : I → EuclideanSpace ℂ (A × B))
    (w : Fin 0 → I) (x : (Fin 0 → A) × (Fin 0 → B)) : sourceWordVector v w x = 1 := by
  simp [sourceWordVector]

example {I A B : Type*} (v : I → EuclideanSpace ℂ (A × B))
    (w : Fin 1 → I) (x : (Fin 1 → A) × (Fin 1 → B)) :
    sourceWordVector v w x = v (w 0) (x.1 0, x.2 0) := by
  simp [sourceWordVector]

example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n da db : ℕ} (c : DistributedBlockCode A B n da db)
    (X : Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ) :
    c.output X = c.decode (both c.encodeA c.encodeB X) := rfl

example : hiddenBobAfter 0 2 = ket (0 : Fin 3) := by
  simp [hiddenBobAfter]

example (alpha beta : Bool → ℂ) : hybridVector alpha beta false (false, false) = alpha false := by
  simp [hybridVector]

example (alpha beta : Bool → ℂ) : hybridVector alpha beta true (true, false) = beta true := by
  simp [hybridVector]

example (p : Bool → ℝ) (alpha beta : Bool → ℂ) (j : Bool)
    (hq : hybridQ p alpha beta j = 0) :
    hybridConditional p alpha beta j = pureDensity (ket false) := by
  simp [hybridConditional, hq]

end SanityExamples

end QAlgorithms.Papers.Independent.Intakethird100.P11


