-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P100
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:15:41.04896+00:00
-- url     : https://prove2.me/theorems/4771bb47-d22e-4649-b24e-7f8fae0c1a3b
-- title:
--   Definitions for Locking classical correlation in quantum states
-- statement:
--   The objects the formalized statements of *Locking classical correlation in quantum states* (arXiv:quant-ph/0303088) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pairBasis`: PDF p.1, Eq.(1): transport the accepted two-register basis to A times B.
--   - `measuredState`: PDF p.1: a normalized matrix, reindexed without changing either local system.
--   - `lockingMeasuredInformation`: PDF p.1, Eq.(1): solely a basis-transport wrapper around the frozen I_c. The distinct name avoids the unrelated frozen channel-ensemble Holevo quantity Renew46.P36.classicalInformation; that definition cannot represent this I_c. The zero branch is an invalid-input default; every theorem uses density matrices on positive-dimensional spaces or asserts normalization of its constructed state. There is no new POVM optimization or outcome restriction.
--   - `OneWayMap`: PDF pp.2--3: one Alice-to-Bob classical message of at most l bits. Alice's rectangular Kraus instrument has at most 2^l message values; Bob applies a channel conditioned on that value. Unsent private outcomes can be retained inside C, and both parties can retain the message in C and D. Arbitrary local ancillas, disposal and local preprocessing are included in these CP maps; there is no additional shared resource.
--   - `oneWayOutput`: PDF p.2, Eq.(2): the actual output of the specified one-round protocol.
--   - `oneWayInformation`: PDF p.3, Theorem 1: Eq.(2) restricted to one-way classical communication. Both output dimensions range over all positive integers. For states the set is nonempty (identity protocol) and bounded by log(dim A)+l, since Alice's initial system plus her transmitted classical record bounds the correlation.
--   - `lockingState`: PDF p.2, Eq.(5), and p.5, Eq.(17): the explicit uniform product mixture. Alice's label is (k,t), Bob's vector is column k of U_t.
--   - `disclosedState`: PDF pp.2,5: actual classical output after disclosure of t, inverse U_t, and measurement of k. Alice and Bob both retain (k,t). The copied key is included in Bob's output, so the physical output space is larger.
--   - `IsUnbiasedFamily`: PDF pp.2,5: U_0=I and the column bases are pairwise mutually unbiased. Unitarity is in U's type; squared overlaps are 1/d.
--   - `basisScore`: PDF p.5, Eq.(18): averaged negative measurement entropy of a vector.
--   - `maximalBasisScore`: PDF p.5, Eq.(18): maximize only over normalized vectors. For d,L>0 this set is nonempty and bounded in [-log d,0]; attainment is also included in the theorem below.
--   - `lockingCopies`: PDF p.3: independent copies regrouped as Alice's m systems versus Bob's. This is the already accepted mixed-state tensor-power definition.
--   - `localOutput`: PDF pp.2,6: local CPTP maps act on the full bipartite matrix.
--   - `sendAlice`: PDF pp.2,6: send Alice's two-dimensional factor to Bob, retaining all coherences. finProdFinEquiv fixes the finite basis convention.
--   - `sendBob`: PDF pp.2,6: the reverse transfer, sending Bob's qubit to Alice.
--   - `QuantumExecution`: PDF pp.2,6: finite two-way quantum executions. Local channels may add or discard local ancillas and keep private measurement records. Only actual qubit transfers increment the cost; composition adds these counts. No shared ancilla state or additional correlated resource is an input.
--   - `QuantumObtainable`: PDF p.2, Eq.(2): at most l qubits, with the endpoint equal to the actual executed output, including all records that the protocol retains.
--   - `IsPrimePower`: PDF p.6: a nontrivial prime power p^n, n>=1.
--   - `IsLeastPrimePowerAbove`: PDF p.6, Theorem 2: the least prime power no smaller than d.
--   - `lockingEntropyTerm`: PDF p.6: eta(x)=-x log_2 x, continuously interpreted as zero at x=0. This is distinct from the frozen tomography loss Claimed50.P28.eta and the SchmidtInput.eta seed-vector construction in Next46.P39; neither has this scalar entropy body.
--   - `correlationRoot`: PDF pp.4,6: shorthand for sqrt(2 ln(2) I_c(rho)); ln is natural log.
--   - `refinedError`: PDF p.6: the printed refined continuity error, with its exact coefficient.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, https://arxiv.org/abs/quant-ph/0303088v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P39

/-! DiVincenzo et al., arXiv:quant-ph/0303088v1.
All logarithms in information expressions are base two. Matrix states are
positive semidefinite with trace one. The only information optimization used
below is the accepted Claimed50.P33.independentMeasuredInformation.
The printed small-correlation thresholds are retained: their appendix proof
has the Fannes substitution-domain gap described in MODERATION_NOTES.md.
Compilation is pending the authorized mechanical handoff. -/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.1, Eq.(1): transport the accepted two-register basis to A times B. -/
def pairBasis (A B : Type) [Fintype A] [Fintype B] :
    Claimed50.P33.RegisterBasis (fun i => Fin (![Fintype.card A, Fintype.card B] i)) ≃ A × B :=
  (piFinTwoEquiv (fun i => Fin (![Fintype.card A, Fintype.card B] i))).trans
    (Equiv.prodCongr (Fintype.equivFin A).symm (Fintype.equivFin B).symm)

/-- PDF p.1: a normalized matrix, reindexed without changing either local system. -/
def measuredState {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ)
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B)
    (h : IsDensityMatrix rho) : Claimed50.P33.FiniteState 2 where
  dims := ![Fintype.card A, Fintype.card B]
  positive := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  rho := rho.submatrix (pairBasis A B) (pairBasis A B)
  normalized := by
    refine ⟨h.1.submatrix _, ?_⟩
    change (∑ i, rho (pairBasis A B i) (pairBasis A B i)) = 1
    rw [(pairBasis A B).sum_comp (fun i => rho i i)]
    exact h.2

/-- PDF p.1, Eq.(1): solely a basis-transport wrapper around the frozen I_c.
The distinct name avoids the unrelated frozen channel-ensemble Holevo quantity
Renew46.P36.classicalInformation; that definition cannot represent this I_c.
The zero branch is an invalid-input default; every theorem uses density
matrices on positive-dimensional spaces or asserts normalization of its
constructed state. There is no new POVM optimization or outcome restriction. -/
def lockingMeasuredInformation {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  if h : 0 < Fintype.card A ∧ 0 < Fintype.card B ∧ IsDensityMatrix rho then
    Claimed50.P33.independentMeasuredInformation (measuredState rho h.1 h.2.1 h.2.2)
  else 0

/-- Sanity: basis transport identifies the two party coordinates separately. -/
example {A B : Type} [Fintype A] [Fintype B]
    (x : Claimed50.P33.RegisterBasis (fun i => Fin (![Fintype.card A, Fintype.card B] i))) :
    pairBasis A B x = ((Fintype.equivFin A).symm (x 0),
      (Fintype.equivFin B).symm (x 1)) := rfl

/-- Sanity: the wrapper is exactly the frozen quantity on every valid input. -/
example {A B : Type} [Fintype A] [Fintype B] (rho : Matrix (A × B) (A × B) ℂ)
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B) (h : IsDensityMatrix rho) :
    lockingMeasuredInformation rho =
      Claimed50.P33.independentMeasuredInformation (measuredState rho hA hB h) := by
  unfold lockingMeasuredInformation
  split_ifs with hvalid
  · rfl
  · exact (hvalid ⟨hA, hB, h⟩).elim

/-- PDF pp.2--3: one Alice-to-Bob classical message of at most l bits.
Alice's rectangular Kraus instrument has at most 2^l message values; Bob
applies a channel conditioned on that value. Unsent private outcomes can be
retained inside C, and both parties can retain the message in C and D.
Arbitrary local ancillas, disposal and local preprocessing are included in
these CP maps; there is no additional shared resource. -/
structure OneWayMap (A B C D : Type) [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] (l : ℕ) where
  messages : ℕ
  messages_pos : 0 < messages
  budget : messages ≤ 2 ^ l
  krausCount : ℕ
  alice : Fin messages → Fin krausCount → Matrix C A ℂ
  complete : (∑ t, ∑ r, (alice t r)ᴴ * alice t r) = 1
  bob : Fin messages → Superop B D
  bob_valid : ∀ t, IsChannel (bob t)

/-- PDF p.2, Eq.(2): the actual output of the specified one-round protocol. -/
def oneWayOutput {A B C D : Type} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] {l : ℕ} (P : OneWayMap A B C D l)
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (C × D) (C × D) ℂ :=
  ∑ t, idTensorSuperop (P.bob t)
    (Support50.P39.aliceAction (krausApply (P.alice t)) rho)

/-- PDF p.3, Theorem 1: Eq.(2) restricted to one-way classical communication.
Both output dimensions range over all positive integers. For states the set
is nonempty (identity protocol) and bounded by log(dim A)+l, since Alice's
initial system plus her transmitted classical record bounds the correlation. -/
def oneWayInformation {A B : Type} [Fintype A] [Fintype B]
    (l : ℕ) (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v : ℝ | ∃ c d : ℕ, ∃ P : OneWayMap A B (Fin (c+1)) (Fin (d+1)) l,
    v = lockingMeasuredInformation (oneWayOutput P rho)}

/-- Sanity: a message is tied to the source's exponential alphabet budget. -/
example {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (P : OneWayMap A B C D 0) : P.messages ≤ 1 := by
  simpa using P.budget

/-- PDF p.2, Eq.(5), and p.5, Eq.(17): the explicit uniform product mixture.
Alice's label is (k,t), Bob's vector is column k of U_t. -/
def lockingState {d L : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix ((Fin d × Fin L) × Fin d) ((Fin d × Fin L) × Fin d) ℂ :=
  fun a b => if a.1 = b.1 then
    ((L*d : ℕ) : ℂ)⁻¹ * (U a.1.2 : Matrix (Fin d) (Fin d) ℂ) a.2 a.1.1 *
      conj ((U a.1.2 : Matrix (Fin d) (Fin d) ℂ) b.2 a.1.1)
    else 0

/-- PDF pp.2,5: actual classical output after disclosure of t, inverse U_t,
and measurement of k. Alice and Bob both retain (k,t). The copied key is
included in Bob's output, so the physical output space is larger. -/
def disclosedState (d L : ℕ) :
    Matrix ((Fin d × Fin L) × (Fin d × Fin L))
      ((Fin d × Fin L) × (Fin d × Fin L)) ℂ :=
  fun a b => if a = b ∧ a.1 = a.2 then ((L*d : ℕ) : ℂ)⁻¹ else 0

/-- PDF pp.2,5: U_0=I and the column bases are pairwise mutually unbiased.
Unitarity is in U's type; squared overlaps are 1/d. -/
def IsUnbiasedFamily {d L : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  (∀ t, t.val = 0 → (U t : Matrix (Fin d) (Fin d) ℂ) = 1) ∧
  ∀ t s, t ≠ s → ∀ k j : Fin d,
    Complex.normSq (∑ i, conj ((U t : Matrix (Fin d) (Fin d) ℂ) i k) *
      (U s : Matrix (Fin d) (Fin d) ℂ) i j) = 1 / (d : ℝ)

/-- PDF p.5, Eq.(18): averaged negative measurement entropy of a vector. -/
def basisScore {d L : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ)
    (phi : EuclideanSpace ℂ (Fin d)) : ℝ :=
  (L : ℝ)⁻¹ * ∑ t, ∑ k,
    let p := Complex.normSq (∑ i, conj (phi i) * (U t : Matrix (Fin d) (Fin d) ℂ) i k)
    p * Real.logb 2 p

/-- PDF p.5, Eq.(18): maximize only over normalized vectors. For d,L>0
this set is nonempty and bounded in [-log d,0]; attainment is also included
in the theorem below. -/
def maximalBasisScore {d L : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ) : ℝ :=
  sSup {v | ∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧ v = basisScore U phi}

/-- Sanity: Eq.(17) has weight 1/(Ld) on each Alice label and the
outer product of the corresponding Bob column, including off-diagonals. -/
example {d L : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ)
    (k : Fin d) (t : Fin L) (i j : Fin d) :
    lockingState U ((k,t),i) ((k,t),j) =
      ((L*d : ℕ) : ℂ)⁻¹ * (U t : Matrix (Fin d) (Fin d) ℂ) i k *
        conj ((U t : Matrix (Fin d) (Fin d) ℂ) j k) := by
  simp [lockingState]

/-- Sanity: the disclosed output cannot have support on unequal shared labels. -/
example (d L : ℕ) (a b : (Fin d × Fin L) × (Fin d × Fin L)) (h : a.1 ≠ a.2) :
    disclosedState d L a b = 0 := by
  simp [disclosedState, h]

/-- PDF p.3: independent copies regrouped as Alice's m systems versus Bob's.
This is the already accepted mixed-state tensor-power definition. -/
abbrev lockingCopies {d L : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ) (m : ℕ) :=
  Support50.P39.noisyResourceCopies (lockingState U) m

/-- Sanity: the empty tensor product has its single matrix entry equal to one. -/
example {d L : ℕ} (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ)
    (a b : (Fin 0 → Fin d × Fin L) × (Fin 0 → Fin d)) :
    lockingCopies U 0 a b = 1 := by
  simp [lockingCopies, Support50.P39.noisyResourceCopies]

/-- PDF pp.2,6: local CPTP maps act on the full bipartite matrix. -/
def localOutput {a b c d : ℕ} (F : Superop (Fin a) (Fin c))
    (G : Superop (Fin b) (Fin d))
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ :=
  idTensorSuperop G (Support50.P39.aliceAction F rho)

/-- PDF pp.2,6: send Alice's two-dimensional factor to Bob, retaining all
coherences. finProdFinEquiv fixes the finite basis convention. -/
def sendAlice {a b : ℕ}
    (rho : Matrix (Fin (a*2) × Fin b) (Fin (a*2) × Fin b) ℂ) :
    Matrix (Fin a × Fin (2*b)) (Fin a × Fin (2*b)) ℂ :=
  fun x y => rho
    (finProdFinEquiv (x.1, (finProdFinEquiv.symm x.2).1), (finProdFinEquiv.symm x.2).2)
    (finProdFinEquiv (y.1, (finProdFinEquiv.symm y.2).1), (finProdFinEquiv.symm y.2).2)

/-- PDF pp.2,6: the reverse transfer, sending Bob's qubit to Alice. -/
def sendBob {a b : ℕ}
    (rho : Matrix (Fin a × Fin (2*b)) (Fin a × Fin (2*b)) ℂ) :
    Matrix (Fin (a*2) × Fin b) (Fin (a*2) × Fin b) ℂ :=
  fun x y => rho
    ((finProdFinEquiv.symm x.1).1, finProdFinEquiv ((finProdFinEquiv.symm x.1).2, x.2))
    ((finProdFinEquiv.symm y.1).1, finProdFinEquiv ((finProdFinEquiv.symm y.1).2, y.2))

/-- PDF pp.2,6: finite two-way quantum executions. Local channels may add or
discard local ancillas and keep private measurement records. Only actual
qubit transfers increment the cost; composition adds these counts. No shared
ancilla state or additional correlated resource is an input. -/
inductive QuantumExecution : (a b : ℕ) →
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ → (c d : ℕ) →
    Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ → ℕ → Prop where
  | local {a b c d : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
      (F : Superop (Fin a) (Fin c)) (G : Superop (Fin b) (Fin d))
      (hF : IsChannel F) (hG : IsChannel G) :
      QuantumExecution a b rho c d (localOutput F G rho) 0
  | alice {a b : ℕ} (rho : Matrix (Fin (a*2) × Fin b) (Fin (a*2) × Fin b) ℂ) :
      QuantumExecution (a*2) b rho a (2*b) (sendAlice rho) 1
  | bob {a b : ℕ} (rho : Matrix (Fin a × Fin (2*b)) (Fin a × Fin (2*b)) ℂ) :
      QuantumExecution a (2*b) rho (a*2) b (sendBob rho) 1
  | trans {a b c d e f q r : ℕ}
      {rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}
      {sigma : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ}
      {tau : Matrix (Fin e × Fin f) (Fin e × Fin f) ℂ}
      (first : QuantumExecution a b rho c d sigma q)
      (second : QuantumExecution c d sigma e f tau r) :
      QuantumExecution a b rho e f tau (q+r)

/-- PDF p.2, Eq.(2): at most l qubits, with the endpoint equal to the actual
executed output, including all records that the protocol retains. -/
def QuantumObtainable {a b c d : ℕ} (l : ℕ)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (sigma : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) : Prop :=
  ∃ q : ℕ, q ≤ l ∧ QuantumExecution a b rho c d sigma q

/-- Sanity: sending a qubit and sending it back preserves every matrix entry. -/
example {a b : ℕ} (rho : Matrix (Fin (a*2) × Fin b) (Fin (a*2) × Fin b) ℂ) :
    sendBob (sendAlice rho) = rho := by
  ext x y
  simp only [sendBob, sendAlice, Equiv.symm_apply_apply, Prod.eta,
    Equiv.apply_symm_apply]

/-- PDF p.6: a nontrivial prime power p^n, n>=1. -/
def IsPrimePower (d : ℕ) : Prop :=
  ∃ p n : ℕ, Nat.Prime p ∧ 0 < n ∧ d = p ^ n

/-- PDF p.6, Theorem 2: the least prime power no smaller than d. -/
def IsLeastPrimePowerAbove (d dp : ℕ) : Prop :=
  d ≤ dp ∧ IsPrimePower dp ∧ ∀ q : ℕ, d ≤ q → IsPrimePower q → dp ≤ q

/-- PDF p.6: eta(x)=-x log_2 x, continuously interpreted as zero at x=0.
This is distinct from the frozen tomography loss Claimed50.P28.eta and the
SchmidtInput.eta seed-vector construction in Next46.P39; neither has this scalar entropy body. -/
def lockingEntropyTerm (x : ℝ) : ℝ := -x * Real.logb 2 x

/-- PDF pp.4,6: shorthand for sqrt(2 ln(2) I_c(rho)); ln is natural log. -/
def correlationRoot {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  Real.sqrt (2 * Real.log 2 * lockingMeasuredInformation rho)

/-- PDF p.6: the printed refined continuity error, with its exact coefficient. -/
def refinedError {A B : Type} [Fintype A] [Fintype B]
    (d dp : ℕ) (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  let x := ((dp : ℝ)+1)^2 * correlationRoot rho
  2 * x * Real.logb 2 d + lockingEntropyTerm x

/-- Sanity: when I_c vanishes, the square-root parameter is exactly zero. -/
example {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) (h : lockingMeasuredInformation rho = 0) :
    correlationRoot rho = 0 := by
  simp [correlationRoot, h]

/-- Sanity: the refined error also vanishes continuously at zero correlation. -/
example {A B : Type} [Fintype A] [Fintype B] (d dp : ℕ)
    (rho : Matrix (A × B) (A × B) ℂ) (h : lockingMeasuredInformation rho = 0) :
    refinedError d dp rho = 0 := by
  simp [refinedError, correlationRoot, h, lockingEntropyTerm]

/-- Sanity: the continuous zero convention does not add a positivity assumption. -/
example : lockingEntropyTerm 0 = 0 := by simp [lockingEntropyTerm]

/-- Sanity: 2 is a prime power with positive exponent. -/
example : IsPrimePower 2 := ⟨2, 1, by norm_num, by norm_num, by norm_num⟩

end QAlgorithms.Papers.Independent.Intakenext100.P100


