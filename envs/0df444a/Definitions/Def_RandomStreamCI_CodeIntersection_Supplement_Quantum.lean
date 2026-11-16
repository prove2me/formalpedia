-- Prove2me | Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_Quantum
-- name    : RandomStreamCI_CodeIntersection_Supplement_Quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:46:27.274861+00:00
-- url     : https://prove2.me/theorems/4d8e3e63-b467-41b2-93a6-8faa65af9c4b
-- title:
--   Charged one-pass quantum programs with polynomial outputs
-- statement:
--   A polynomial-output program has a normalized initial density matrix on $q$ persistent qubits, a finite CPTP channel controlled only by time and the current stream item, an input-independent final channel, and a normalized POVM with outcomes $F^d\cup\{\mathrm{abort}\}$. Every coefficient outcome denotes the published degree-strictly-below-$d$ polynomial. All persistent quantum and classical records, sparse lists, syndromes and reusable computation scratch must fit in the $q$ qubits. There is no access to the oracle or stream order outside the current-item interface.
--
--   Execution iterates the channels exactly once over the complete stream. At fixed order $\pi$, success averages the Born probabilities over the uniform oracle, counting abort and low score as failures. Charged memory is
--   $$3q+2\left\lceil\log_2(1+|F|^d)\right\rceil+1.$$
--   This adds a recycled Kraus environment of at most $2q$ qubits and measurement/readout space to the persistent registers, including preparation and final processing. Arbitrary fixed finite-dimensional operations and unrestricted time are allowed, as in the source bounded-space interpretation. No algorithmic success claim is built into the model.
-- source:
--   Bouland–Ding–Jain, Exponential quantum space advantage in random data streams, STOC 2027 submission #71, preprint dated 2026-11-02, release papers-1/71.pdf, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/71.pdf, SHA256 3fe1835efedc1b9f29103379085d28d84ab1057dc30c3e3f05a8dce9f536a797, Appendix A, Theorem 29 and proof, pp. 28--30

import Definitions.Def_RandomStreamCI_CodeIntersection_Quantum
import Definitions.Def_RandomStreamCI_CodeIntersection_Supplement_OPI

noncomputable section

namespace RandomStreamCI.CodeIntersection.Supplement

open scoped BigOperators
open QAlgorithms
attribute [local instance] Classical.propDecidable

/-- Appendix A, pp. 28--30: a one-pass bounded-memory machine with coefficient-or-abort output.
Every persistent classical/quantum register, including sparse-list and syndrome workspace,
is in q qubits. Initial and final operations are input-independent. Each step sees only
its time and current stream item. No later oracle access or order parameter is available.
Finite-channel environments and coefficient readout workspace are additionally charged below.
No correctness, decoding or space promise is part of the data. -/
structure PolynomialProgram (n d : ℕ) (F : Type*) [Field F] [Fintype F] where
  q : ℕ
  initial : Matrix (Qubits q) (Qubits q) ℂ
  initial_valid : IsDensityMatrix initial
  step : Fin (Fintype.card (Address n F)) → Input n F → FiniteChannel q
  finish : FiniteChannel q
  measurement : Option (Coefficients F d) → Matrix (Qubits q) (Qubits q) ℂ
  measurement_valid : IsPOVM measurement

namespace PolynomialProgram

variable {n d : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def state (Q : PolynomialProgram n d F) (ω : Sample n F) :
    ℕ → Matrix (Qubits Q.q) (Qubits Q.q) ℂ
  | 0 => Q.initial
  | t+1 => if h : t < Fintype.card (Address n F) then
      (Q.step ⟨t,h⟩ (streamItem ω ⟨t,h⟩)).apply (Q.state ω t)
    else Q.state ω t

def outcomeProbability (Q : PolynomialProgram n d F) (ω : Sample n F)
    (out : Option (Coefficients F d)) : ℝ :=
  effectProb (Q.measurement out)
    (Q.finish.apply (Q.state ω (Fintype.card (Address n F))))

/-- Problem 2 success: every coefficient tuple denotes a degree-<d polynomial; none is failure. -/
def ValidPolynomial (α : Fin n → F) (τ : ℕ) (H : Oracle n F) :
    Option (Coefficients F d) → Prop
  | none => False
  | some x => τ ≤ value H (evaluation α x) Finset.univ

/-- Average over uniform oracle at a fixed order, retaining all quantum abort/failure mass. -/
def successAtOrder (Q : PolynomialProgram n d F) (α : Fin n → F)
    (τ : ℕ) (π : Order n F) : ℝ :=
  (Fintype.card (Oracle n F) : ℝ)⁻¹ *
    ∑ H : Oracle n F, ∑ out : Option (Coefficients F d),
      if ValidPolynomial α τ H out then Q.outcomeProbability (H,π) out else 0

/-- q live qubits + at most 2q recycled Kraus-environment qubits + twice the coefficient
output-label length + one flag. This includes preparation, final operation, abort handling,
and measurement/readout; there is no uncharged persistent scratch. Exponential time is allowed.
The output labels number 1+|F|^d, rather than 1+|F|^n. -/
def memoryBits (Q : PolynomialProgram n d F) : ℕ :=
  3 * Q.q + 2 * ⌈log₂ (Fintype.card (Option (Coefficients F d)))⌉₊ + 1

end PolynomialProgram

end RandomStreamCI.CodeIntersection.Supplement


