-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
-- name    : QAlgorithms_Papers_Independent_Information100_P32
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T10:23:52.920391+00:00
-- url     : https://prove2.me/theorems/0944d44a-fc55-455f-a04a-01a2969c6dc8
-- title:
--   Definitions for Coherence -assisted quantum state preparation and thermal control through repeated interactions
-- statement:
--   The objects the formalized statements of *Coherence -assisted quantum state preparation and thermal control through repeated interactions* (arXiv:2610.10794) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Op`
--   - `rho`: PDF p.2, Eq.(4): upper-right entry is c; false labels the ground state.
--   - `Physical`: PDF p.2: exactly the positivity domain for a normalized qubit density matrix.
--   - `Model`: PDF pp.1–3: identical, fresh resonant ancillas and a fixed positive collision duration.
--   - `localEnergy`: PDF p.2, Eq.(3).
--   - `freeEnergy`: PDF p.2, Eq.(2); tensor order is system, ancilla.
--   - `interaction`: PDF p.2, Eq.(1), with the source's Pauli-Y sign convention.
--   - `evolution`: PDF p.3: exact exponential, without a short-time approximation.
--   - `reduced`: PDF p.2, Eq.(6), and p.15, Eq.(A1): trace out the second factor.
--   - `collision`: PDF pp.2–3: a fresh, uncorrelated ancillary state at every collision.
--   - `trajectory`: PDF p.2, Eq.(6), including the initial state at n=0.
--   - `population`: PDF p.2, Eq.(5).
--   - `coherence`: PDF p.2, Eq.(5).
--   - `angleC`: PDF pp.3–4: C=cos(2J tau), S=sin(2J tau), L=C-cos(omega tau).
--   - `angleS`: PDF p.3: S=sin(2J tau).
--   - `differenceL`: PDF p.4: L=cos(2J tau)-cos(omega tau).
--   - `denominatorD`: PDF p.4, Eq.(14).
--   - `denominatorK`: PDF p.3, Eq.(13); q here means |cA|^2, not Appendix C's 4|cA|^2.
--   - `lambda`: PDF p.4, Eq.(14).
--   - `starPopulation`: PDF p.3, Eq.(11): algebraic candidate; claims using it explicitly guard K>0.
--   - `starCoherence`: PDF p.3, Eq.(12). Both displayed summands have a minus sign.
--   - `starState`: PDF p.3, Eqs.(11)–(12): this is constructed, not an arbitrary fixed point parameter.
--   - `phase`: PDF p.4, Eq.(17): the phase e^(i theta) constructed from the collision parameters.
--   - `purity`: PDF p.5, Eq.(23): real trace of the square.
--   - `dephasingCollision`: PDF p.8, Eqs.(27)–(28): exact second-stage Ising collision.
--   - `dephasingFactor`: PDF p.8, Eq.(30), including the free-system rotation.
--   - `inverseTemperature`: PDF p.8, Eqs.(31)–(32): population-defined temperature, including coherent states.
--   - `observableChange`: PDF p.9, Eqs.(34)–(35): change of a joint observable, with source sign.
--   - `work`: PDF p.9, Eq.(34).
--   - `heat`: PDF p.9, Eq.(35): positive heat means energy deposited in the ancilla.
--   - `diagonalAncilla`: PDF p.9, Eq.(36): these components are operators, not two normalized states.
--   - `offDiagonalAncilla`: PDF p.9, Eq.(36): only the off-diagonal part of the incoming ancilla.
--   - `diagonal`: PDF p.15, Eq.(A2), in a fixed reference orthonormal basis.
--   - `Decoupled`: PDF p.15: sector invariance is the definition, rather than Eq.(A5) itself.
--   - `affineMatrix`: PDF p.18, Eq.(B2); first-row second entry conjugates cA.
--   - `affineOffset`: PDF p.18, Eq.(B3).
--   - `coordinates`: PDF p.18, before Eq.(B1).
--   - `weightedNorm`: PDF p.21, Eq.(E2), G=diag(1,1/2,1/2).
--   - `weightedInducedNorm`: PDF p.21, Eq.(E5): actual induced norm, not the default matrix norm. The quotient set contains zero and is bounded in this finite-dimensional norm.
--   - `contractionRate`: PDF p.21, Eq.(E5).
--   - `collisionBound`: Corrected PDF p.21, Eqs.(E7)–(E8): strict distance needs floor+1. Zero initial distance and zero contraction are handled before logarithms.
--   - `resourceL1`: PDF p.22, Eq.(F1), finite reindexing of the accepted l1 coherence.
--   - `resourceEntropy`: PDF p.22, Eq.(F2): multiply accepted bit entropy by log 2 to obtain nats.
--   - `varyingPopulation`: PDF p.4, Eq.(16): the exact algebraic population as ancillary coherence varies.
--   - `varyingCoherence`: PDF p.4, Eq.(20): the exact algebraic coherence as ancillary coherence varies.
-- source:
--   Coherence-assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, https://arxiv.org/abs/2610.10794v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_BasisCoherence

noncomputable section

open scoped Matrix ComplexConjugate Topology
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

abbrev Op (I : Type*) := Matrix I I ℂ

/-- PDF p.2, Eq.(4): upper-right entry is c; false labels the ground state. -/
def rho (p : ℝ) (c : ℂ) : Op Bool :=
  fun i j => if i then (if j then (1 - p : ℝ) else conj c)
    else (if j then c else (p : ℂ))

/-- PDF p.2: exactly the positivity domain for a normalized qubit density matrix. -/
def Physical (p : ℝ) (c : ℂ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ Complex.normSq c ≤ p * (1 - p)

/-- PDF pp.1–3: identical, fresh resonant ancillas and a fixed positive collision duration. -/
structure Model where
  coupling : ℝ
  frequency : ℝ
  duration : ℝ
  pA : ℝ
  cA : ℂ
  duration_pos : 0 < duration
  ancilla_physical : Physical pA cA

/-- PDF p.2, Eq.(3). -/
def localEnergy (omega : ℝ) : Op Bool := (-(omega : ℂ) / 2) • pauliZ

/-- PDF p.2, Eq.(2); tensor order is system, ancilla. -/
def freeEnergy (omega : ℝ) : Op (Bool × Bool) :=
  Matrix.kronecker (localEnergy omega) 1 + Matrix.kronecker 1 (localEnergy omega)

/-- PDF p.2, Eq.(1), with the source's Pauli-Y sign convention. -/
def interaction (j : ℝ) : Op (Bool × Bool) :=
  (j : ℂ) • (Matrix.kronecker pauliX pauliX + Matrix.kronecker pauliY pauliY)

/-- PDF p.3: exact exponential, without a short-time approximation. -/
def evolution {I : Type*} [Fintype I] [DecidableEq I] (h : Op I) (t : ℝ) : Op I :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • h)

/-- PDF p.2, Eq.(6), and p.15, Eq.(A1): trace out the second factor. -/
def reduced {I A : Type*} [Fintype I] [Fintype A]
    (u : Op (I × A)) (a : Op A) (x : Op I) : Op I :=
  fun i j => ∑ k, (u * Matrix.kronecker x a * u.conjTranspose) (i, k) (j, k)

/-- PDF pp.2–3: a fresh, uncorrelated ancillary state at every collision. -/
def collision (m : Model) : Op Bool → Op Bool :=
  reduced (evolution (freeEnergy m.frequency + interaction m.coupling) m.duration)
    (rho m.pA m.cA)

/-- PDF p.2, Eq.(6), including the initial state at n=0. -/
def trajectory (m : Model) (r : Op Bool) (n : ℕ) : Op Bool :=
  (collision m)^[n] r

/-- PDF p.2, Eq.(5). -/
def population (r : Op Bool) : ℝ := (r false false).re

/-- PDF p.2, Eq.(5). -/
def coherence (r : Op Bool) : ℂ := r false true

/-- PDF pp.3–4: C=cos(2J tau), S=sin(2J tau), L=C-cos(omega tau). -/
def angleC (m : Model) : ℝ := Real.cos (2 * m.coupling * m.duration)

/-- PDF p.3: S=sin(2J tau). -/
def angleS (m : Model) : ℝ := Real.sin (2 * m.coupling * m.duration)

/-- PDF p.4: L=cos(2J tau)-cos(omega tau). -/
def differenceL (m : Model) : ℝ := angleC m - Real.cos (m.frequency * m.duration)

/-- PDF p.4, Eq.(14). -/
def denominatorD (m : Model) : ℝ :=
  differenceL m ^ 2 + Real.sin (m.frequency * m.duration) ^ 2

/-- PDF p.3, Eq.(13); q here means |cA|^2, not Appendix C's 4|cA|^2. -/
def denominatorK (m : Model) : ℝ :=
  denominatorD m - 4 * Complex.normSq m.cA * angleC m * differenceL m

/-- PDF p.4, Eq.(14). -/
def lambda (m : Model) : ℝ :=
  4 * Complex.normSq m.cA * angleC m * differenceL m / denominatorD m

/-- PDF p.3, Eq.(11): algebraic candidate; claims using it explicitly guard K>0. -/
def starPopulation (m : Model) : ℝ :=
  m.pA + 2 * Complex.normSq m.cA / denominatorK m * (2 * m.pA - 1) *
    angleC m * differenceL m

/-- PDF p.3, Eq.(12). Both displayed summands have a minus sign. -/
def starCoherence (m : Model) : ℂ :=
  -Complex.I * (m.cA / (denominatorK m : ℂ)) * (2 * m.pA - 1 : ℝ) *
      (angleS m : ℂ) * (differenceL m : ℂ) -
    (m.cA / (denominatorK m : ℂ)) * (2 * m.pA - 1 : ℝ) *
      (angleS m : ℂ) * (Real.sin (m.frequency * m.duration) : ℂ)

/-- PDF p.3, Eqs.(11)–(12): this is constructed, not an arbitrary fixed point parameter. -/
def starState (m : Model) : Op Bool := rho (starPopulation m) (starCoherence m)

/-- PDF p.4, Eq.(17): the phase e^(i theta) constructed from the collision parameters. -/
def phase (m : Model) : ℂ :=
  ((Real.sin (m.frequency * m.duration) : ℂ) + Complex.I * (differenceL m : ℂ)) /
    (Real.sqrt (denominatorD m) : ℂ)

/-- PDF p.5, Eq.(23): real trace of the square. -/
def purity {I : Type*} [Fintype I] (r : Op I) : ℝ := (r * r).trace.re

/-- PDF p.8, Eqs.(27)–(28): exact second-stage Ising collision. -/
def dephasingCollision (m : Model) (jzz : ℝ) : Op Bool → Op Bool :=
  reduced (evolution (freeEnergy m.frequency +
    (jzz : ℂ) • Matrix.kronecker pauliZ pauliZ) m.duration) (rho m.pA m.cA)

/-- PDF p.8, Eq.(30), including the free-system rotation. -/
def dephasingFactor (m : Model) (jzz : ℝ) : ℂ :=
  (m.pA : ℂ) * Complex.exp (-Complex.I * ((2 * jzz - m.frequency) * m.duration : ℝ)) +
    (1 - m.pA : ℝ) * Complex.exp (Complex.I * ((2 * jzz + m.frequency) * m.duration : ℝ))

/-- PDF p.8, Eqs.(31)–(32): population-defined temperature, including coherent states. -/
def inverseTemperature (omega p : ℝ) : ℝ := Real.log (p / (1 - p)) / omega

/-- PDF p.9, Eqs.(34)–(35): change of a joint observable, with source sign. -/
def observableChange (m : Model) (b : Op (Bool × Bool)) (r a : Op Bool) : ℝ :=
  let u := evolution (freeEnergy m.frequency + interaction m.coupling) m.duration
  ((u.conjTranspose * b * u - b) * Matrix.kronecker r a).trace.re

/-- PDF p.9, Eq.(34). -/
def work (m : Model) (r : Op Bool) : ℝ :=
  observableChange m (interaction m.coupling) r (rho m.pA m.cA)

/-- PDF p.9, Eq.(35): positive heat means energy deposited in the ancilla. -/
def heat (m : Model) (r a : Op Bool) : ℝ :=
  observableChange m (Matrix.kronecker 1 (localEnergy m.frequency)) r a

/-- PDF p.9, Eq.(36): these components are operators, not two normalized states. -/
def diagonalAncilla (m : Model) : Op Bool := rho m.pA 0

/-- PDF p.9, Eq.(36): only the off-diagonal part of the incoming ancilla. -/
def offDiagonalAncilla (m : Model) : Op Bool := rho m.pA m.cA - diagonalAncilla m

/-- PDF p.15, Eq.(A2), in a fixed reference orthonormal basis. -/
def diagonal {I : Type*} [DecidableEq I] (x : Op I) : Op I :=
  fun i j => if i = j then x i i else 0

/-- PDF p.15: sector invariance is the definition, rather than Eq.(A5) itself. -/
def Decoupled {I : Type*} [DecidableEq I] (f : Op I → Op I) : Prop :=
  (∀ x, diagonal x = x → diagonal (f x) = f x) ∧
  (∀ x, diagonal x = 0 → diagonal (f x) = 0)

/-- PDF p.18, Eq.(B2); first-row second entry conjugates cA. -/
def affineMatrix (m : Model) : Matrix (Fin 3) (Fin 3) ℂ :=
  let e := Complex.exp (Complex.I * (m.frequency * m.duration : ℝ))
  !![(angleC m ^ 2 : ℝ), Complex.I / 2 * Real.sin (4 * m.coupling * m.duration) * conj m.cA,
        -Complex.I / 2 * Real.sin (4 * m.coupling * m.duration) * m.cA;
     Complex.I * 2 * m.cA * angleS m * e, (angleC m : ℂ) * e, 0;
     -Complex.I * 2 * conj m.cA * angleS m * conj e, 0, (angleC m : ℂ) * conj e]

/-- PDF p.18, Eq.(B3). -/
def affineOffset (m : Model) : Fin 3 → ℂ :=
  let e := Complex.exp (Complex.I * (m.frequency * m.duration : ℝ))
  ![(m.pA * angleS m ^ 2 : ℝ), -Complex.I * m.cA * angleS m * e,
    Complex.I * conj m.cA * angleS m * conj e]

/-- PDF p.18, before Eq.(B1). -/
def coordinates (r : Op Bool) : Fin 3 → ℂ :=
  ![(population r : ℂ), coherence r, conj (coherence r)]

/-- PDF p.21, Eq.(E2), G=diag(1,1/2,1/2). -/
def weightedNorm (x : Fin 3 → ℂ) : ℝ :=
  Real.sqrt (Complex.normSq (x 0) + Complex.normSq (x 1) / 2 + Complex.normSq (x 2) / 2)

/-- PDF p.21, Eq.(E5): actual induced norm, not the default matrix norm.
The quotient set contains zero and is bounded in this finite-dimensional norm. -/
def weightedInducedNorm (a : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  sSup (Set.range fun x : Fin 3 → ℂ => weightedNorm (a.mulVec x) / weightedNorm x)

/-- PDF p.21, Eq.(E5). -/
def contractionRate (m : Model) : ℝ :=
  Real.sqrt (1 - angleS m ^ 2 * (1 - 4 * Complex.normSq m.cA))

/-- Corrected PDF p.21, Eqs.(E7)–(E8): strict distance needs floor+1.
Zero initial distance and zero contraction are handled before logarithms. -/
def collisionBound (r d epsilon : ℝ) : ℕ :=
  if d < epsilon then 0 else if r = 0 then 1
  else Nat.floor ((Real.log epsilon - Real.log d) / Real.log r) + 1

/-- PDF p.22, Eq.(F1), finite reindexing of the accepted l1 coherence. -/
def resourceL1 (r : Op Bool) : ℝ :=
  QAlgorithms.Coherence.l1Coherence !![r false false, r false true; r true false, r true true]

/-- PDF p.22, Eq.(F2): multiply accepted bit entropy by log 2 to obtain nats. -/
def resourceEntropy (r : Op Bool) : ℝ :=
  Real.log 2 * (vnEntropy (diagonal r) - vnEntropy r)

/-- Sanity: the upper-right entry is the source coherence, not its conjugate. -/
example (p : ℝ) (c : ℂ) : coherence (rho p c) = c := by rfl

/-- Sanity: the collision sequence includes its specified initial state. -/
example (m : Model) (r : Op Bool) : trajectory m r 0 = r := by rfl

/-- Sanity: the dephasing map preserves every population entry. -/
example {I : Type*} [DecidableEq I] (r : Op I) (i : I) : diagonal r i i = r i i := by
  simp [diagonal]

/-- Sanity: an initially attained strict tolerance uses zero collisions. -/
example (r epsilon : ℝ) (h : 0 < epsilon) : collisionBound r 0 epsilon = 0 := by
  simp [collisionBound, h]

/-- PDF p.4, Eq.(16): the exact algebraic population as ancillary coherence varies. -/
def varyingPopulation (m : Model) (c : ℂ) : ℝ :=
  m.pA + 2 * Complex.normSq c /
    (denominatorD m - 4 * Complex.normSq c * angleC m * differenceL m) *
    (2 * m.pA - 1) * angleC m * differenceL m

/-- PDF p.4, Eq.(20): the exact algebraic coherence as ancillary coherence varies. -/
def varyingCoherence (m : Model) (c : ℂ) : ℂ :=
  -c * (2 * m.pA - 1 : ℝ) * (angleS m : ℂ) *
    ((Real.sin (m.frequency * m.duration) : ℂ) + Complex.I * (differenceL m : ℂ)) /
    ((denominatorD m - 4 * Complex.normSq c * angleC m * differenceL m : ℝ) : ℂ)

section

open scoped Matrix.Norms.Elementwise

end

end QAlgorithms.Papers.Independent.Information100.P32


