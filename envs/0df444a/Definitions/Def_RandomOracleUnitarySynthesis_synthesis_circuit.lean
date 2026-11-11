-- Prove2me | Definitions.Def_RandomOracleUnitarySynthesis_synthesis_circuit
-- name    : RandomOracleUnitarySynthesis_synthesis_circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:21.436175+00:00
-- url     : https://prove2.me/theorems/f82ef26c-1147-4ad6-9070-c3108d63b262
-- title:
--   Phase-query circuits, their actual channels, influences, and Pauli observables
-- statement:
--   Let $n\le m$, $m_0\le m$ and let $V_0,\ldots,V_k\in U(2^m)$ be fixed before drawing a Boolean truth table $f$ on $m_0$ bits. The phase oracle acts on every computational basis state according to its first $m_0$ bits. The circuit, its compressed block, and its actual channel are
--
--   $$W_f=V_kO_f\cdots O_fV_0,\qquad A_f=J^\dagger W_fJ,\qquad E_f(\rho)=\operatorname{Tr}_{\rm anc}(W_fJ\rho J^\dagger W_f^\dagger).$$
--
--   Here $J$ appends zero ancillas, and the partial trace sums over all ancillary outputs. For query $i$, the source's left and right products omit that oracle call; its influence is the sum of the squared Frobenius norms of both projected products. The Heisenberg observable is $A_{f,P}=J^\dagger W_f^\dagger(P\otimes I)W_fJ$.
--
--   This is the paper's concrete oracle/circuit model, including arbitrary dirty ancillas and distinct gates at each query time. There is no condition $m_0\le n$ or bound on gate complexity.
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), §2.1, printed pp. 10–11 (PDF pp. 12–13); Definition 3.6, printed p. 16 (PDF p. 18); Definition 4.6, printed p. 18 (PDF p. 20); Lemma 4.11, printed p. 26 (PDF p. 28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_matrix_model

open scoped Matrix ComplexConjugate
open MeasureTheory
noncomputable section

namespace RandomOracleUnitarySynthesis

/-! §2.1, Definition 3.6 and Definition 4.6, printed pp.10,16,18 (PDF pp.12,18,20).
No restriction on gate complexity, ancilla growth, or the overlap of the oracle register
with the system/ancilla split. Gate lists are fixed data, independent of the oracle. -/
abbrev synthesis_Oracle (m₀ : ℕ) := synthesis_Bits m₀ → Bool

structure synthesis_Circuit (n m m₀ k : ℕ) where
  system_le : n ≤ m
  oracle_le : m₀ ≤ m
  gates : Fin (k+1) → synthesis_Unitary m

/-- Concatenate computational-basis words; the size hypotheses guard every subtraction. -/
def synthesis_join {n m : ℕ} (h : n ≤ m) (x : synthesis_Bits n)
    (a : synthesis_Bits (m-n)) : synthesis_Bits m :=
  fun i => if hi : i.val < n then x ⟨i.val,hi⟩ else a ⟨i.val-n, by omega⟩

def synthesis_prefix {s m : ℕ} (h : s ≤ m) (x : synthesis_Bits m) : synthesis_Bits s :=
  fun i => x ⟨i.val, by omega⟩

def synthesis_suffix {n m : ℕ} (h : n ≤ m) (x : synthesis_Bits m) : synthesis_Bits (m-n) :=
  fun i => x ⟨n+i.val, by omega⟩

/-- J|x⟩=|x⟩|0^(m-n)⟩. -/
def synthesis_J {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k) :
    Matrix (synthesis_Bits m) (synthesis_Bits n) ℂ :=
  fun y x => if y = synthesis_join C.system_le x (fun _ => 0) then 1 else 0

/-- Π_x fixes the FIRST m₀ bits, with the identity on every remaining basis state. -/
def synthesis_projector {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (x : synthesis_Bits m₀) : synthesis_Mat m :=
  fun y z => if y=z ∧ synthesis_prefix C.oracle_le y = x then 1 else 0

/-- The complete phase oracle, including its action on nonzero/entangled workspace states. -/
def synthesis_oracle {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) : synthesis_Mat m :=
  Matrix.diagonal fun y => if f (synthesis_prefix C.oracle_le y) then -1 else 1

/-- Gate access is total; only indices 0,...,k occur in the circuit and influence products. -/
def synthesis_gate {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k) (i : ℕ) : synthesis_Mat m :=
  if h : i < k+1 then (C.gates ⟨i,h⟩ : synthesis_Mat m) else 1

/-- V_b O_f ... O_f V_a for 0≤a≤b≤k, with first-applied gate rightmost. -/
def synthesis_segment {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) (a b : ℕ) : synthesis_Mat m :=
  (List.range (b-a)).foldl (fun W t =>
    synthesis_gate C (a+t+1) * synthesis_oracle C f * W) (synthesis_gate C a)

def synthesis_W {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) : synthesis_Mat m := synthesis_segment C f 0 k

def synthesis_A {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) : synthesis_Mat n :=
  (synthesis_J C)ᴴ * synthesis_W C f * synthesis_J C

/-- Partial trace of W J ρ J† W† over the last m-n qubits. Garbage is summed over,
never projected onto zero and never postselected. -/
def synthesis_actualChannel {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) : synthesis_Channel n :=
  synthesis_coordinates fun ρ =>
    let σ := synthesis_W C f * synthesis_J C * ρ * (synthesis_J C)ᴴ * (synthesis_W C f)ᴴ
    WildeQIT.partialTraceRight (Matrix.of fun a b =>
      σ (synthesis_join C.system_le a.1 a.2) (synthesis_join C.system_le b.1 b.2))

/-- `j : Fin k` denotes query i=j+1, counting from the right. -/
def synthesis_left {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) (j : Fin k) :=
  (synthesis_J C)ᴴ * synthesis_segment C f (j.val+1) k

def synthesis_right {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) (j : Fin k) :=
  synthesis_segment C f 0 j.val * synthesis_J C

/-- Definition 4.6, both left and right contributions for all k queries. -/
def synthesis_influence {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) : ℝ :=
  ∑ j : Fin k, ((QAlgorithms.frobNorm (synthesis_left C f j * synthesis_projector C x))^2 +
    (QAlgorithms.frobNorm (synthesis_projector C x * synthesis_right C f j))^2)

def synthesis_flip {m₀ : ℕ} (f : synthesis_Oracle m₀) (x : synthesis_Bits m₀) :
    synthesis_Oracle m₀ := Function.update f x (!f x)

/-- P ⊗ I on the full m-qubit space. -/
def synthesis_liftPauli {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (P : synthesis_Pauli n) : synthesis_Mat m :=
  fun y z => if synthesis_suffix C.system_le y = synthesis_suffix C.system_le z then
    DirectFidelity.State.W P (synthesis_prefix C.system_le y) (synthesis_prefix C.system_le z)
    else 0

/-- Heisenberg observable of the dirty channel, obtained from the actual 2k-query
circuit W†(P⊗I)W, not from the original compressed block. -/
def synthesis_observable {n m m₀ k : ℕ} (C : synthesis_Circuit n m m₀ k)
    (f : synthesis_Oracle m₀) (P : synthesis_Pauli n) : synthesis_Mat n :=
  (synthesis_J C)ᴴ * (synthesis_W C f)ᴴ * synthesis_liftPauli C P *
    synthesis_W C f * synthesis_J C

end RandomOracleUnitarySynthesis


