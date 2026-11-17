-- Prove2me | Definitions.Def_SingleInteraction_Supplement_StoqMA
-- name    : SingleInteraction_Supplement_StoqMA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:01:40.282244+00:00
-- url     : https://prove2.me/theorems/0ef94a98-3d0e-4195-b9e2-3f1e814c69ca
-- title:
--   The class StoqMA (Definition 5) and StoqMA-hardness
-- statement:
--   A promise problem $L=(L_{\mathrm{yes}},L_{\mathrm{no}})$ is in **StoqMA** if a deterministic polynomial-time algorithm outputs, for each input $x$, a circuit $U_x$ of polynomially many gates from $\{X,\mathrm{CNOT},\mathrm{Toffoli}\}$ (classical reversible gates, permutations of the computational basis) acting on
--   $$|0\rangle^{\otimes n_0}\otimes|1\rangle^{\otimes n_1}\otimes|+\rangle^{\otimes n_+}\otimes|\xi\rangle,$$
--   followed by a measurement of the output qubit in the Hadamard basis, accepting on outcome $+$, and there are thresholds $0\le\epsilon_{\mathrm{no}}(|x|)<\epsilon_{\mathrm{yes}}(|x|)\le1$ with $\epsilon_{\mathrm{yes}}-\epsilon_{\mathrm{no}}\ge1/\mathrm{poly}(|x|)$ such that some witness $|\xi\rangle$ is accepted with probability $\ge\epsilon_{\mathrm{yes}}$ when $x\in L_{\mathrm{yes}}$, and every witness with probability $\le\epsilon_{\mathrm{no}}$ when $x\in L_{\mathrm{no}}$. No amplification is assumed (Remark 2). A problem is StoqMA-hard if every StoqMA promise problem reduces to it by a polynomial-time many-one reduction.
--
--   This is the class of Theorems 73 and 77.
--
--   **Formalization Note** The output qubit is qubit $0$; the ancilla blocks come first, the witness last. The thresholds are required to be computable to precision $2^{-q}$ in polynomial time (a reading: Definition 5 leaves this implicit; the class of [BBT06] and every reduction of the paper compute them). The gap is $\ge1/(|x|+1)^d$ for one exponent $d$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 5 and Remark 2, p.17

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-!
# StoqMA (Definition 5)

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…), Definition 5 (StoqMA, adapted from [BBT06]) and Remark 2, p.17: a deterministic
polynomial-time algorithm outputs, for each input `x`, a circuit `U_x` on
`n0(|x|) + n1(|x|) + n+(|x|) + m(|x|)` qubits with `t(|x|)` gates "from a finite gate set that is
universal for classical reversible computation", followed by a measurement of a designated output
qubit in the Hadamard basis; it is applied to `|0⟩^{⊗n0} ⊗ |1⟩^{⊗n1} ⊗ |+⟩^{⊗n+} ⊗ |ξ⟩`, accepts on
outcome `+`, and YES ⇒ some `|ξ⟩` is accepted with probability `≥ ϵyes`, NO ⇒ every `|ξ⟩` with
probability `≤ ϵno`, where `0 ≤ ϵno < ϵyes ≤ 1` and `ϵyes − ϵno ≥ 1/poly(|x|)`.

**Formalization Note**
* The gate set is `{X, CNOT, Toffoli}` (a finite gate set universal for classical reversible
  computation, the one of [BBT06]). Gates are permutations of the computational basis; a gate whose
  qubit indices are out of range or not distinct makes the circuit ill-formed.
* Qubit order: qubits `0, …, n0−1` start in `|0⟩`, the next `n1` in `|1⟩`, the next `n+` in `|+⟩`,
  and the last `m` hold the witness. The designated output qubit is qubit `0`.
* "Polynomial-size" is a polynomial bound on qubit count plus gate count, as in the published
  `QuantumVerifier`. Uniformity is `Turing.TM2ComputableInPolyTime` from the input bits to the
  circuit code.
* The thresholds are functions of `|x|`. Definition 5 does not say how they are given; they are
  required to be polynomial-time computable to any precision `2^{−q}` (`EfficientThreshold`), as in
  [BBT06] and every reduction of the paper (a reading). The gap `ϵyes − ϵno ≥ 1/poly` is
  `≥ ((|x|+1)^d)⁻¹` for one exponent `d`. No amplification is assumed (Remark 2). -/

/-- The gates `X`, `CNOT`, `Toffoli` (qubit indices). -/
inductive StoqGate where
  | pauliX (target : ℕ)
  | cnot (control target : ℕ)
  | toffoli (control₁ control₂ target : ℕ)
  deriving DecidableEq, Repr

/-- Equivalence used to build the gate code. -/
def stoqGateEquiv : StoqGate ≃ (ℕ ⊕ ((ℕ × ℕ) ⊕ (ℕ × (ℕ × ℕ)))) where
  toFun
    | .pauliX i => Sum.inl i
    | .cnot i j => Sum.inr (Sum.inl (i, j))
    | .toffoli i j l => Sum.inr (Sum.inr (i, j, l))
  invFun
    | Sum.inl i => .pauliX i
    | Sum.inr (Sum.inl (i, j)) => .cnot i j
    | Sum.inr (Sum.inr (i, j, l)) => .toffoli i j l
  left_inv g := by cases g <;> rfl
  right_inv g := by rcases g with i | ⟨i, j⟩ | ⟨i, j, l⟩ <;> rfl

/-- The code of a gate. -/
def stoqGateCodec : Codec StoqGate :=
  BinaryEncoding.equiv (BinaryEncoding.sum natural (BinaryEncoding.sum (pair natural natural)
    (pair natural (pair natural natural)))) stoqGateEquiv

/-- A stoquastic verifier circuit: the ancilla counts `n0, n1, n+`, the witness size `m`, and the
gate list (applied first to last). -/
structure StoqCircuit where
  zeros : ℕ
  ones : ℕ
  pluses : ℕ
  witness : ℕ
  gates : List StoqGate
  deriving DecidableEq, Repr

/-- Equivalence used to build the circuit code. -/
def stoqCircuitEquiv : StoqCircuit ≃ (ℕ × (ℕ × (ℕ × (ℕ × List StoqGate)))) where
  toFun c := (c.zeros, c.ones, c.pluses, c.witness, c.gates)
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, c, d, e⟩; rfl

/-- The code of a circuit. -/
def stoqCircuitCodec : Codec StoqCircuit :=
  BinaryEncoding.equiv (pair natural (pair natural (pair natural (pair natural
    (BinaryEncoding.list stoqGateCodec))))) stoqCircuitEquiv

/-- The total number of qubits `n0 + n1 + n+ + m`. -/
def StoqCircuit.size (c : StoqCircuit) : ℕ := c.zeros + c.ones + c.pluses + c.witness

/-- A gate is well formed on `N` qubits: its indices are `< N` and pairwise distinct. -/
def StoqGate.WellFormed (N : ℕ) : StoqGate → Prop
  | .pauliX i => i < N
  | .cnot i j => i < N ∧ j < N ∧ i ≠ j
  | .toffoli i j l => i < N ∧ j < N ∧ l < N ∧ i ≠ j ∧ i ≠ l ∧ j ≠ l

/-- A circuit is well formed: it has at least one qubit (the output qubit `0`) and every gate is
well formed. -/
def StoqCircuit.WellFormed (c : StoqCircuit) : Prop :=
  1 ≤ c.size ∧ ∀ g ∈ c.gates, g.WellFormed c.size

/-- The bit of a basis state at index `i` (`0` out of range). -/
def bitAt {N : ℕ} (s : Fin N → Fin 2) (i : ℕ) : Fin 2 :=
  if h : i < N then s ⟨i, h⟩ else 0

/-- The basis permutation of a gate (each gate is an involution). -/
def StoqGate.act {N : ℕ} (g : StoqGate) (s : Fin N → Fin 2) : Fin N → Fin 2 :=
  match g with
  | .pauliX i => fun q => if q.val = i then 1 - s q else s q
  | .cnot i j => fun q => if q.val = j ∧ bitAt s i = 1 then 1 - s q else s q
  | .toffoli i j l => fun q =>
      if q.val = l ∧ bitAt s i = 1 ∧ bitAt s j = 1 then 1 - s q else s q

/-- The initial state `|0⟩^{⊗n0} ⊗ |1⟩^{⊗n1} ⊗ |+⟩^{⊗n+} ⊗ |ξ⟩` as an amplitude function. -/
noncomputable def stoqInitial (c : StoqCircuit) (ξ : EuclideanSpace ℂ (Fin c.witness → Fin 2)) :
    (Fin c.size → Fin 2) → ℂ :=
  fun s =>
    if (∀ q : Fin c.size, q.val < c.zeros → s q = 0) ∧
        (∀ q : Fin c.size, c.zeros ≤ q.val → q.val < c.zeros + c.ones → s q = 1) then
      ((Real.sqrt 2 : ℂ)⁻¹) ^ c.pluses *
        ξ (fun i => bitAt s (c.zeros + c.ones + c.pluses + i.val))
    else 0

/-- The state after the circuit: gates are applied in list order, each permuting the basis. -/
noncomputable def stoqFinal (c : StoqCircuit) (ξ : EuclideanSpace ℂ (Fin c.witness → Fin 2)) :
    (Fin c.size → Fin 2) → ℂ :=
  c.gates.foldl (fun ψ g => fun s => ψ (g.act s)) (stoqInitial c ξ)

/-- Flip the output qubit `0`. -/
def flipOut {N : ℕ} (s : Fin N → Fin 2) : Fin N → Fin 2 :=
  fun q => if q.val = 0 then 1 - s q else s q

/-- The probability that measuring the output qubit `0` in the Hadamard basis yields `+`. -/
noncomputable def stoqAcceptance (c : StoqCircuit)
    (ξ : EuclideanSpace ℂ (Fin c.witness → Fin 2)) : ℝ :=
  ∑ s : Fin c.size → Fin 2,
    if bitAt s 0 = 0 then
      Complex.normSq ((stoqFinal c ξ s + stoqFinal c ξ (flipOut s)) / (Real.sqrt 2 : ℂ))
    else 0

/-- A uniform polynomial-size stoquastic verifier. -/
structure StoqVerifier where
  generate : BitString → StoqCircuit
  uniform : Turing.TM2ComputableInPolyTime id stoqCircuitCodec.encode generate
  size : Polynomial ℕ
  size_bound : ∀ x, (generate x).size + (generate x).gates.length ≤ size.eval x.length
  wellFormed : ∀ x, (generate x).WellFormed

/-- A threshold function `ϵ : ℕ → ℝ` (of the input length) computable to precision `2^{−q}` in
polynomial time. -/
def EfficientThreshold (e : ℕ → ℝ) : Prop :=
  ∃ f : ℕ × ℕ → BinaryRational,
    Nonempty (Turing.TM2ComputableInPolyTime (pair unary unary).encode binaryRationalCodec.encode f) ∧
    ∀ n q : ℕ, 0 < (f (n, q)).denominator ∧ |((f (n, q)).value : ℝ) - e n| ≤ (1 / 2 : ℝ) ^ q

/-- Membership in StoqMA (Definition 5). -/
def InStoqMA (P : PromiseProblem BitString) : Prop :=
  ∃ (V : StoqVerifier) (eyes eno : ℕ → ℝ) (d : ℕ),
    EfficientThreshold eyes ∧ EfficientThreshold eno ∧
    (∀ n : ℕ, 0 ≤ eno n ∧ eno n < eyes n ∧ eyes n ≤ 1 ∧
      (((n : ℝ) + 1) ^ d)⁻¹ ≤ eyes n - eno n) ∧
    (∀ x ∈ P.yes, ∃ ξ : EuclideanSpace ℂ (Fin (V.generate x).witness → Fin 2),
      ‖ξ‖ = 1 ∧ eyes x.length ≤ stoqAcceptance (V.generate x) ξ) ∧
    (∀ x ∈ P.no, ∀ ξ : EuclideanSpace ℂ (Fin (V.generate x).witness → Fin 2),
      ‖ξ‖ = 1 → stoqAcceptance (V.generate x) ξ ≤ eno x.length)

/-- StoqMA-hardness of a promise problem on instances `α` presented by `encoding`. -/
def StoqMAHard {α : Type} (encoding : α → BitString) (Q : PromiseProblem α) : Prop :=
  ∀ P : PromiseProblem BitString, InStoqMA P → Nonempty (PolynomialManyOne id encoding P Q)

end Supplement

end SingleInteraction


