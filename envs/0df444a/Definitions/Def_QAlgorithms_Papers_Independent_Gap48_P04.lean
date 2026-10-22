-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04
-- name    : QAlgorithms_Papers_Independent_Gap48_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:54:08.551997+00:00
-- url     : https://prove2.me/theorems/2b871abe-a10c-40a2-aba1-5a01efbfdd0f
-- title:
--   Definitions for Capacities of Quantum Erasure Channels
-- statement:
--   The objects the formalized statements of *Capacities of Quantum Erasure Channels* (arXiv:quant-ph/9701015) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Schedule`
--   - `UnknownQubitCode`: PDF p.1: one encoder and decoder, fixed before the unknown input.
--   - `UnknownQubitCode.output`: PDF p.1, Fig.1: independent uses act on the full, possibly entangled block.
--   - `QuantumSupported`: PDF p.1: every accuracy admits a positive block with rate strictly above R; the one code must work uniformly for every unit pure input.
--   - `uniformQuantumCapacity`: PDF p.1: the unassisted quantum capacity in qubits per use. The nonnegative extended supremum includes capacity zero and cannot default to zero at infinity.
--   - `CollectiveBitCode`: PDF pp.1--2: arbitrary collective state preparations and one collective POVM. Messages are m-bit strings. No shared resource or side communication is supplied.
--   - `ClassicalSupported`: PDF p.1: worst-message error is strictly smaller than every specified eta.
--   - `worstMessageCapacity`: PDF pp.1--2: unassisted asymptotic classical capacity, in bits per use.
--   - `aliceBranch`: PDF p.2: one Alice instrument branch, retaining Bob's full quantum memory.
--   - `bobBranch`: PDF p.2: one Bob instrument branch, retaining Alice's full quantum memory.
--   - `sendRegister`: PDF pp.1--2: send the input factor of Alice's memory through one actual channel. Initially Alice holds Fin a times Fin d, and Bob holds Fin b. Afterwards Alice holds Fin a and Bob holds Fin e times Fin b. Off-diagonal blocks of both memories are retained. finProdFinEquiv is only a coordinate relabelling.
--   - `Adaptive`: PDF pp.1--2: evaluated finite adaptive protocol, with n forward channel slots. Each local complete Kraus instrument reports its classical outcome; the continuation may depend on it. Arbitrary finite quantum memories, local ancillas, randomness, discarding, and arbitrarily many finite two-way rounds are included. A protocol is a function of the slot maps but may access them only through send; it cannot inspect a future erasure schedule. No shared entanglement is supplied.
--   - `TwoWayQubitCode`: PDF pp.1--2: Alice encodes locally; Bob's initial memory is one dimensional. The protocol, including its dependence on classical outcomes, precedes the input state and the channel schedule. There is no initial shared entanglement.
--   - `TwoWayQubitCode.output`: PDF pp.1--2: unconditional output sums every instrument branch, without postselection.
--   - `TwoWaySupported`: PDF pp.1--2: quantum reliability with free two-way classical communication; the n forward slots are independent copies of the same channel.
--   - `adaptiveQuantumCapacity`: PDF pp.1--2: operational two-way assisted quantum capacity, in qubits per use.
--   - `phaseErasure`: PDF p.3, Eq.(3): the second output qubit is the flag. Coordinates are (qubit,flag) via finProdFinEquiv, with flag 0 intact and flag 1 phase erased.
--   - `mixedErasure`: PDF p.3, Eq.(4): three mutually exclusive flags, in direct-sum order intact (two dimensions), phase erased (two), erased (one). p and delta are unconditional probabilities. No division by 1-delta occurs, including at delta=1,p=0.
--   - `labelOutcomeLaw`: PDF p.3, Eq.(5): classical joint law after preparing rho_x and measuring M_y.
--   - `oneShotValues`: PDF p.3, Eq.(5): measured mutual-information values over every finite normalized ensemble of arbitrary density matrices and every finite POVM.
--   - `oneShotCapacity`: PDF p.3: measured single-use classical capacity. Finite nonempty registers and channels give a nonempty value set bounded above by log2(d); the theorem also states an actual greatest value, so the real-sSup default is never used.
--   - `basisProjector`: PDF p.3: density and measurement projector of a column of any orthonormal basis.
--   - `erasureSchedule`: PDF p.4: evaluate the slots at a prescribed pattern, without revealing it to Alice or hardwiring it into the protocol. Erasure is to one orthogonal dimension.
--   - `CorrectsEveryPattern`: PDF pp.3--4: one fixed nontrivial code subspace; each known erased set may have its own CPTP recovery. The condition covers every density operator in the logical subspace, and hence every unknown pure logical state. The physical Bool-word rows of V are relabelled coordinatewise by the accepted finTwoEquiv from Fin 2 to Bool before applying the Fin-2-indexed slot tensor; no wire is reversed.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, https://arxiv.org/abs/quant-ph/9701015v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

/-! Statements of Bennett--DiVincenzo--Smolin, quant-ph/9701015v2.
Capacities below are operational, in bits or qubits per forward use. They are
extended nonnegative suprema, never definitions by an information formula.
The matrix abbreviation Op is imported from the accepted library. Distinct
source-specific operational concepts have distinct names. Compilation is pending. -/

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

abbrev Schedule (d e n : ℕ) := Fin n → Superop (Fin d) (Fin e)

/-- PDF p.1: one encoder and decoder, fixed before the unknown input. -/
structure UnknownQubitCode (d e n m : ℕ) where
  encode : Superop (Qubits m) (Fin n → Fin d)
  decode : Superop (Fin n → Fin e) (Qubits m)
  encode_channel : IsChannel encode
  decode_channel : IsChannel decode

/-- PDF p.1, Fig.1: independent uses act on the full, possibly entangled block. -/
def UnknownQubitCode.output {d e n m : ℕ} (P : UnknownQubitCode d e n m)
    (N : Superop (Fin d) (Fin e)) : Superop (Qubits m) (Qubits m) :=
  P.decode ∘ piSuperop (fun _ : Fin n => N) ∘ P.encode

/-- PDF p.1: every accuracy admits a positive block with rate strictly above R;
the one code must work uniformly for every unit pure input. -/
def QuantumSupported {d e : ℕ} (N : Superop (Fin d) (Fin e)) (R : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ m n : ℕ, 0 < n ∧ R < (m : ℝ) / n ∧
    ∃ P : UnknownQubitCode d e n m, ∀ psi : EuclideanSpace ℂ (Qubits m),
      IsState psi → 1 - eta ≤ effectProb (pureDensity psi) (P.output N (pureDensity psi))

/-- PDF p.1: the unassisted quantum capacity in qubits per use. The nonnegative
extended supremum includes capacity zero and cannot default to zero at infinity. -/
def uniformQuantumCapacity {d e : ℕ} (N : Superop (Fin d) (Fin e)) : ENNReal :=
  sSup {q | ∃ R : ℝ, 0 ≤ R ∧ QuantumSupported N R ∧ q = ENNReal.ofReal R}

/-- PDF pp.1--2: arbitrary collective state preparations and one collective POVM.
Messages are m-bit strings. No shared resource or side communication is supplied. -/
structure CollectiveBitCode (d e n m : ℕ) where
  prepare : Qubits m → Op (Fin n → Fin d)
  prepare_density : ∀ x, IsDensityMatrix (prepare x)
  measure : Qubits m → Op (Fin n → Fin e)
  measure_povm : IsPOVM measure

/-- PDF p.1: worst-message error is strictly smaller than every specified eta. -/
def ClassicalSupported {d e : ℕ} (N : Superop (Fin d) (Fin e)) (R : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ m n : ℕ, 0 < n ∧ R < (m : ℝ) / n ∧
    ∃ P : CollectiveBitCode d e n m, ∀ x,
      1 - effectProb (P.measure x)
        (piSuperop (fun _ : Fin n => N) (P.prepare x)) < eta

/-- PDF pp.1--2: unassisted asymptotic classical capacity, in bits per use. -/
def worstMessageCapacity {d e : ℕ} (N : Superop (Fin d) (Fin e)) : ENNReal :=
  sSup {q | ∃ R : ℝ, 0 ≤ R ∧ ClassicalSupported N R ∧ q = ENNReal.ofReal R}

/-- PDF p.2: one Alice instrument branch, retaining Bob's full quantum memory. -/
def aliceBranch {a b h : ℕ} (E : Matrix (Fin h) (Fin a) ℂ) :
    Superop (Fin a × Fin b) (Fin h × Fin b) :=
  conjSuperop (Matrix.kronecker E (1 : Op (Fin b)))

/-- PDF p.2: one Bob instrument branch, retaining Alice's full quantum memory. -/
def bobBranch {a b h : ℕ} (E : Matrix (Fin h) (Fin b) ℂ) :
    Superop (Fin a × Fin b) (Fin a × Fin h) :=
  conjSuperop (Matrix.kronecker (1 : Op (Fin a)) E)

/-- PDF pp.1--2: send the input factor of Alice's memory through one actual channel.
Initially Alice holds Fin a times Fin d, and Bob holds Fin b. Afterwards Alice
holds Fin a and Bob holds Fin e times Fin b. Off-diagonal blocks of both memories
are retained. finProdFinEquiv is only a coordinate relabelling. -/
def sendRegister {a b d e : ℕ} (N : Superop (Fin d) (Fin e)) :
    Superop (Fin (a*d) × Fin b) (Fin a × Fin (e*b)) :=
  fun X p q =>
    let yp : Fin e × Fin b := finProdFinEquiv.symm p.2
    let yq : Fin e × Fin b := finProdFinEquiv.symm q.2
    N (fun i j => X (finProdFinEquiv (p.1,i),yp.2)
      (finProdFinEquiv (q.1,j),yq.2)) yp.1 yq.1

/-- PDF pp.1--2: evaluated finite adaptive protocol, with n forward channel slots.
Each local complete Kraus instrument reports its classical outcome; the
continuation may depend on it. Arbitrary finite quantum memories, local ancillas,
randomness, discarding, and arbitrarily many finite two-way rounds are included.
A protocol is a function of the slot maps but may access them only through send;
it cannot inspect a future erasure schedule. No shared entanglement is supplied. -/
inductive Adaptive (d e m : ℕ) : {n a b : ℕ} →
    (Schedule d e n → Superop (Fin a × Fin b) (Qubits m)) → Prop
  | finish {a b : ℕ} (D : Superop (Fin b) (Qubits m)) (hD : IsChannel D) :
      Adaptive d e m (n := 0) (a := a) (b := b) (fun _ X => D (traceLeft X))
  | alice {n a b h k : ℕ} (E : Fin k → Matrix (Fin h) (Fin a) ℂ)
      (complete : IsKrausFamily E)
      (next : Fin k → Schedule d e n → Superop (Fin h × Fin b) (Qubits m))
      (valid : ∀ i, Adaptive d e m (next i)) :
      Adaptive d e m (fun S X => ∑ i, next i S (aliceBranch (E i) X))
  | bob {n a b h k : ℕ} (E : Fin k → Matrix (Fin h) (Fin b) ℂ)
      (complete : IsKrausFamily E)
      (next : Fin k → Schedule d e n → Superop (Fin a × Fin h) (Qubits m))
      (valid : ∀ i, Adaptive d e m (next i)) :
      Adaptive d e m (fun S X => ∑ i, next i S (bobBranch (E i) X))
  | send {n a b : ℕ}
      (next : Schedule d e n → Superop (Fin a × Fin (e*b)) (Qubits m))
      (valid : Adaptive d e m next) :
      Adaptive d e m (n := n+1) (a := a*d) (b := b)
        (fun S X => next (fun i => S i.succ) (sendRegister (S 0) X))

/-- PDF pp.1--2: Alice encodes locally; Bob's initial memory is one dimensional.
The protocol, including its dependence on classical outcomes, precedes the input
state and the channel schedule. There is no initial shared entanglement. -/
structure TwoWayQubitCode (d e n m : ℕ) where
  memory : ℕ
  memory_positive : 0 < memory
  encode : Superop (Qubits m) (Fin memory)
  encode_channel : IsChannel encode
  run : Schedule d e n → Superop (Fin memory × Fin 1) (Qubits m)
  valid : Adaptive d e m run

/-- PDF pp.1--2: unconditional output sums every instrument branch, without postselection. -/
def TwoWayQubitCode.output {d e n m : ℕ} (P : TwoWayQubitCode d e n m)
    (S : Schedule d e n) (rho : Op (Qubits m)) : Op (Qubits m) :=
  P.run S (Matrix.kronecker (P.encode rho) (1 : Op (Fin 1)))

/-- PDF pp.1--2: quantum reliability with free two-way classical communication;
the n forward slots are independent copies of the same channel. -/
def TwoWaySupported {d e : ℕ} (N : Superop (Fin d) (Fin e)) (R : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ m n : ℕ, 0 < n ∧ R < (m : ℝ) / n ∧
    ∃ P : TwoWayQubitCode d e n m, ∀ psi : EuclideanSpace ℂ (Qubits m),
      IsState psi → 1 - eta ≤ effectProb (pureDensity psi)
        (P.output (fun _ => N) (pureDensity psi))

/-- PDF pp.1--2: operational two-way assisted quantum capacity, in qubits per use. -/
def adaptiveQuantumCapacity {d e : ℕ} (N : Superop (Fin d) (Fin e)) : ENNReal :=
  sSup {q | ∃ R : ℝ, 0 ≤ R ∧ TwoWaySupported N R ∧ q = ENNReal.ofReal R}

/-- PDF p.3, Eq.(3): the second output qubit is the flag. Coordinates are
(qubit,flag) via finProdFinEquiv, with flag 0 intact and flag 1 phase erased. -/
def phaseErasure (p : ℝ) : Superop (Fin 2) (Fin 4) :=
  fun X u v =>
    let x : Fin 2 × Fin 2 := finProdFinEquiv.symm u
    let y : Fin 2 × Fin 2 := finProdFinEquiv.symm v
    if x.2 = y.2 then
      if x.2 = 0 then (1-(p : ℂ)) * X x.1 y.1
      else (p : ℂ) * (Matrix.diagonal (fun i : Fin 2 => X i i)) x.1 y.1
    else 0

/-- PDF p.3, Eq.(4): three mutually exclusive flags, in direct-sum order intact
(two dimensions), phase erased (two), erased (one). p and delta are unconditional
probabilities. No division by 1-delta occurs, including at delta=1,p=0. -/
def mixedErasure (p delta : ℝ) : Superop (Fin 2) (Fin 5) :=
  fun X u v => if hu : u.val < 2 then
    if hv : v.val < 2 then (1-(delta : ℂ)-(p : ℂ)) * X ⟨u.val,hu⟩ ⟨v.val,hv⟩ else 0
  else if hu : u.val < 4 then
    if hv0 : 2 ≤ v.val then
      if hv : v.val < 4 then (delta : ℂ) *
        (Matrix.diagonal (fun i : Fin 2 => X i i))
          ⟨u.val-2,by omega⟩ ⟨v.val-2,by omega⟩ else 0
    else 0
  else if v.val = 4 then (p : ℂ) * X.trace else 0

/-- PDF p.3, Eq.(5): classical joint law after preparing rho_x and measuring M_y. -/
def labelOutcomeLaw {I J X Y : Type*} [Fintype J] (N : Superop I J)
    (p : X → ℝ) (rho : X → Op I) (M : Y → Op J) : X × Y → ℝ :=
  fun xy => p xy.1 * effectProb (M xy.2) (N (rho xy.1))

/-- PDF p.3, Eq.(5): measured mutual-information values over every finite
normalized ensemble of arbitrary density matrices and every finite POVM. -/
def oneShotValues {d e : ℕ} (N : Superop (Fin d) (Fin e)) : Set ℝ :=
  {v | ∃ k l : ℕ, 0 < k ∧ 0 < l ∧ ∃ p : Fin k → ℝ,
    (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1 ∧ ∃ rho : Fin k → Op (Fin d),
    (∀ x, IsDensityMatrix (rho x)) ∧ ∃ M : Fin l → Op (Fin e),
    IsPOVM M ∧ v = mutualInfoBits (labelOutcomeLaw N p rho M)}

/-- PDF p.3: measured single-use classical capacity. Finite nonempty registers and
channels give a nonempty value set bounded above by log2(d); the theorem also
states an actual greatest value, so the real-sSup default is never used. -/
def oneShotCapacity {d e : ℕ} (N : Superop (Fin d) (Fin e)) : ℝ := sSup (oneShotValues N)

/-- PDF p.3: density and measurement projector of a column of any orthonormal basis. -/
def basisProjector (U : Matrix.unitaryGroup (Fin 2) ℂ) (i : Fin 2) : Op (Fin 2) :=
  pureDensity (act (U : Op (Fin 2)) (ket i))

/-- PDF p.4: evaluate the slots at a prescribed pattern, without revealing it to
Alice or hardwiring it into the protocol. Erasure is to one orthogonal dimension. -/
def erasureSchedule {n : ℕ} (S : Finset (Fin n)) : Schedule 2 3 n :=
  fun i => QAlgorithms.Papers.Independent.Dependency50.P09.erasureFin 2 (if i ∈ S then 1 else 0)

/-- PDF pp.3--4: one fixed nontrivial code subspace; each known erased set may
have its own CPTP recovery. The condition covers every density operator in the
logical subspace, and hence every unknown pure logical state. The physical
Bool-word rows of V are relabelled coordinatewise by the accepted finTwoEquiv
from Fin 2 to Bool before applying the Fin-2-indexed slot tensor; no wire is reversed. -/
def CorrectsEveryPattern {n k : ℕ} (V : Matrix (Qubits n) (Fin k) ℂ) (t : ℕ) : Prop :=
  Vᴴ * V = 1 ∧ ∀ S : Finset (Fin n), S.card = t →
    ∃ D : Superop (Fin n → Fin 3) (Fin k), IsChannel D ∧
      ∀ rho : Op (Fin k), IsDensityMatrix rho →
        D (piSuperop (erasureSchedule S)
          (conjSuperop (fun (x : Fin n → Fin 2) (j : Fin k) =>
            V (fun i => finTwoEquiv (x i)) j) rho)) = rho

/-! Sanity checks of the new operational and channel definitions. -/

example {d e n m : ℕ} (P : UnknownQubitCode d e n m) (N : Superop (Fin d) (Fin e))
    (rho : Op (Qubits m)) : P.output N rho =
      P.decode (piSuperop (fun _ : Fin n => N) (P.encode rho)) := rfl

example {d e n m : ℕ} (P : TwoWayQubitCode d e n m) (S : Schedule d e n)
    (rho : Op (Qubits m)) : P.output S rho =
      P.run S (Matrix.kronecker (P.encode rho) (1 : Op (Fin 1))) := rfl

example (X : Op (Fin 2)) : (Matrix.diagonal (fun i : Fin 2 => X i i)) 0 1 = 0 := by simp

example (X : Op (Fin 2)) : (Matrix.diagonal (fun i : Fin 2 => X i i)) 1 1 = X 1 1 := by simp

example (p : ℝ) (X : Op (Fin 2)) : mixedErasure p 0 X 4 4 = (p : ℂ) * X.trace := by
  simp [mixedErasure]

example (X : Op (Fin 2)) : mixedErasure 0 1 X 0 0 = 0 := by simp [mixedErasure]

example {n : ℕ} (i : Fin n) : erasureSchedule (∅ : Finset (Fin n)) i =
    QAlgorithms.Papers.Independent.Dependency50.P09.erasureFin 2 0 := by simp [erasureSchedule]

example {n : ℕ} (i : Fin n) : erasureSchedule (Finset.univ : Finset (Fin n)) i =
    QAlgorithms.Papers.Independent.Dependency50.P09.erasureFin 2 1 := by simp [erasureSchedule]

example {d e m a b : ℕ} (D : Superop (Fin b) (Qubits m)) (hD : IsChannel D) :
    Adaptive d e m (a := a) (n := 0) (fun _ X => D (traceLeft X)) :=
  Adaptive.finish D hD

/-- A noiseless slot transfers even off-diagonal matrix entries; neither local
memory nor the transmitted register is measured by the send semantics. -/
example {a b d : ℕ} (X : Op (Fin (a*d) × Fin b))
    (u v : Fin a) (i j : Fin d) (r s : Fin b) :
    sendRegister (d := d) (e := d) (fun Y => Y) X
      (u,finProdFinEquiv (i,r)) (v,finProdFinEquiv (j,s)) =
        X (finProdFinEquiv (u,i),r) (finProdFinEquiv (v,j),s) := by
  simp [sendRegister]

example (X : Op (Fin 2)) :
    phaseErasure 0 X (finProdFinEquiv ((0 : Fin 2),(0 : Fin 2)))
      (finProdFinEquiv ((1 : Fin 2),(0 : Fin 2))) = X 0 1 := by
  simp [phaseErasure]

example (X : Op (Fin 2)) :
    phaseErasure 1 X (finProdFinEquiv ((0 : Fin 2),(1 : Fin 2)))
      (finProdFinEquiv ((1 : Fin 2),(1 : Fin 2))) = 0 := by
  simp [phaseErasure]

end

end QAlgorithms.Papers.Independent.Gap48.P04


