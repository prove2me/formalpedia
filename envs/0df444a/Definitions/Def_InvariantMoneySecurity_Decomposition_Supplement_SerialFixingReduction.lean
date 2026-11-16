-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_SerialFixingReduction
-- name    : InvariantMoneySecurity_Decomposition_Supplement_SerialFixingReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:32:46.020812+00:00
-- url     : https://prove2.me/theorems/462d5440-4515-40fb-a60b-082980313e00
-- title:
--   Definition 6.8 — serial-fixing and sound reductions
-- statement:
--   A **reduction** $R$ is a uniform family of polynomial-size oracle circuits. It receives $(p,x)\leftarrow M_n$ as a classical input on its input wires and outputs one $n$-qubit register, whose reduced state is $\sigma_{R^A}(p,x)$. Besides local gates of at most three qubits (with the same polynomial size bound, uniform description and effectively computable entries as the published quantum polynomial-time circuits), it contains at most $t(n)=\mathrm{poly}(n)$ instances of $U_A$ and $U_A^\dagger$, each placed on wires of $R$ that form the serial-number register, the challenge register and the further registers. Measurements are deferred; there are no controlled calls. $R$ may prepare challenges in superposition, rewind, and initialize every register it passes to $U_A$.
--
--   $R$ is **serial-fixing** if, for every adversary unitary and every input $(p,x)$ in the support of $M_n$, the serial-number register is in the basis state $|p\rangle$ at every instance of $U_A$ and $U_A^\dagger$: the state just before the instance lies in the range of $|p\rangle\langle p|\otimes I$.
--
--   $R$ is **sound** if for every adversary $A$, efficient or not,
--   $$\mathrm{win}_A(n)\ge 1/\mathrm{poly}(n)\text{ infinitely often}\;\Longrightarrow\;\mathbb E_{(p,x)\leftarrow M_n}\big[\mathrm{aw}_p(\sigma_{R^A}(p,x))\big]\ge 1/\mathrm{poly}(n)\text{ infinitely often},$$
--   where $\mathrm{aw}_p$ is the accepted weight. A **fully black-box derivation** of the transfer assumption from the preparation assumption is a sound reduction.
--
--   **Formalization Note** "At least $1/\mathrm{poly}(n)$ infinitely often" is the negation of the published `Negligible`. The circuit description is a length-delimited code of every step, produced from $1^n$ by a polynomial-time machine.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 29, Definition 6.8 and the paragraph "What the definition allows"

import Definitions.Def_InvariantMoneySecurity_Decomposition_Supplement_UnitaryAdversary
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition.Supplement

open InvariantMoneySecurity.Decomposition

/-- One step of an oracle circuit of width `w` with a `k`-qubit oracle: a published local gate,
or an instance of `U_A` or of `U_A†` placed on `k` distinct wires. There are no controlled calls. -/
inductive OracleStep (w k : ℕ) where
  | gate (g : LocalGate w)
  | call (wires : Fin k ↪ Fin w)
  | callInverse (wires : Fin k ↪ Fin w)

/-- Place a `k`-qubit operator on the given wires, the identity elsewhere. -/
def embedOperator {w k : ℕ} (wires : Fin k ↪ Fin w) (U : Matrix (Bits k) (Bits k) ℂ) :
    Matrix (Bits w) (Bits w) ℂ :=
  fun a b => if (∀ j, j ∉ Set.range wires → a j = b j) then U (a ∘ wires) (b ∘ wires) else 0

/-- The operator of one step for the oracle unitary `U`. -/
def OracleStep.operator {w k : ℕ} (U : Matrix (Bits k) (Bits k) ℂ) :
    OracleStep w k → Matrix (Bits w) (Bits w) ℂ
  | .gate g => g.operator
  | .call wires => embedOperator wires U
  | .callInverse wires => embedOperator wires U.conjTranspose

/-- Structural code of a step: tag, then the gate code or the call's wires. -/
def OracleStep.code {w k : ℕ} : OracleStep w k → List Bool
  | .gate g => [false] ++ g.code
  | .call wires => [true, false] ++ (List.ofFn fun j => codeNat (wires j).val).flatten
  | .callInverse wires => [true, true] ++ (List.ofFn fun j => codeNat (wires j).val).flatten

/-- Numerical data of a step: only local gates carry numbers. -/
def OracleStep.entries {w k : ℕ} : OracleStep w k → List ℝ
  | .gate g => g.entries
  | .call _ => []
  | .callInverse _ => []

/-- A serial oracle circuit with named input and retained output wires (measurements deferred). -/
structure OracleCircuit (i o k : ℕ) where
  width : ℕ
  inputWire : Fin i ↪ Fin width
  outputWire : Fin o ↪ Fin width
  steps : List (OracleStep width k)

/-- Clean initialization: the classical input on the input wires, every other wire `0`. -/
def OracleCircuit.initialVector {i o k : ℕ} (C : OracleCircuit i o k) (input : Bits i) :
    Bits C.width → ℂ :=
  fun a => if a ∘ C.inputWire = input ∧ ∀ j, j ∉ Set.range C.inputWire → a j = false
    then 1 else 0

/-- The pure state after the first `t` steps, with oracle `U`; later steps multiply on the left. -/
def OracleCircuit.stateAfter {i o k : ℕ} (C : OracleCircuit i o k)
    (U : Matrix (Bits k) (Bits k) ℂ) (input : Bits i) (t : ℕ) : Bits C.width → ℂ :=
  ((C.steps.take t).foldl (fun M (s : OracleStep C.width k) => s.operator U * M) 1).mulVec (C.initialVector input)

/-- The reduced state `σ_{R^A}` of the output register after all steps. -/
def OracleCircuit.output {i o k : ℕ} (C : OracleCircuit i o k)
    (U : Matrix (Bits k) (Bits k) ℂ) (input : Bits i) : Matrix (Bits o) (Bits o) ℂ :=
  let v := C.stateAfter U input C.steps.length
  fun x y => ∑ a, ∑ b,
    if (a ∘ C.outputWire = x ∧ b ∘ C.outputWire = y ∧
      ∀ j, j ∉ Set.range C.outputWire → a j = b j) then v a * star (v b) else 0

/-- Full structural code, length-delimited as for published circuits. -/
def OracleCircuit.code {i o k : ℕ} (C : OracleCircuit i o k) : List Bool :=
  codeNat i ++ codeNat o ++ codeNat k ++ codeNat C.width ++
  (List.ofFn fun j => codeNat (C.inputWire j).val).flatten ++
  (List.ofFn fun j => codeNat (C.outputWire j).val).flatten ++
  codeNat C.steps.length ++ (C.steps.map fun (s : OracleStep C.width k) => codeBits s.code).flatten

/-- Definition 6.8: a reduction is a uniform family of polynomial-size oracle circuits with input
`(p, x)` on `serialBits + n` qubits, one `n`-qubit output register, and oracle instances on
`advWidth D e n` wires (serial, challenge, further registers of width `n + e(n)`). The local gates
satisfy the same polynomial bound, uniform description and effective-entry requirements as the
published `QPT`; the number of oracle instances is bounded by the step count. -/
structure Reduction (D : Scheme) (e : ℕ → ℕ) where
  circuit : ∀ n, OracleCircuit ((D.data n).serialBits + n) n (advWidth D e n)
  bound : ∃ q : Polynomial ℕ, ∀ n,
    (circuit n).width ≤ q.eval n ∧ (circuit n).steps.length ≤ q.eval n
  uniform : ∃ f : List Bool → List Bool,
    QAlgorithms.Complexity.PolyTimeComputable f ∧ ∀ n, f (codeNat n) = (circuit n).code
  effective : ∃ (z : ℕ → ℕ → List ℤ) (f : List Bool → List Bool),
    QAlgorithms.Complexity.PolyTimeComputable f ∧
    (∀ n t, f (codeNat n ++ codeNat t) = (z n t |>.map codeInt).flatten) ∧
    ∀ n t, List.Forall₂
      (fun a r => |(a : ℝ) / (2 : ℝ) ^ t - r| ≤ (2 : ℝ)⁻¹ ^ t)
      (z n t) ((circuit n).steps.flatMap OracleStep.entries)

/-- The reduction's output state `σ_{R^A}(p, x)` with the adversary unitary `U`. -/
def Reduction.output {D : Scheme} {e : ℕ → ℕ} (R : Reduction D e)
    (U : ∀ n, Matrix (Bits (advWidth D e n)) (Bits (advWidth D e n)) ℂ) (n : ℕ)
    (p : Bits (D.data n).serialBits) (x : (D.data n).Object) : Matrix (Bits n) (Bits n) ℂ :=
  (R.circuit n).output (U n) (appendBits p x.val)

/-- `E_{(p,x) ← M_n}[aw_p(σ_{R^A}(p, x))]`. -/
def Reduction.advantage {D : Scheme} {e : ℕ → ℕ} (R : Reduction D e)
    (U : ∀ n, Matrix (Bits (advWidth D e n)) (Bits (advWidth D e n)) ℂ) (n : ℕ) : ℝ :=
  (D.data n).mintAverage fun p x => (D.data n).acceptedWeight p (R.output U n p x)

/-- Definition 6.8(i): serial-fixing. For every adversary unitary and every minted input
`(p, x)`, the state just before every instance of `U_A` or `U_A†` lies in the range of
`|p⟩⟨p| ⊗ I` on that instance's serial-number register. -/
def Reduction.SerialFixing {D : Scheme} {e : ℕ → ℕ} (R : Reduction D e) : Prop :=
  ∀ U, IsAdversary D e U → ∀ n (x : (D.data n).Object),
    ∀ t (ht : t < (R.circuit n).steps.length) (wires : Fin (advWidth D e n) ↪ Fin (R.circuit n).width),
      ((R.circuit n).steps.get ⟨t, ht⟩ = .call wires ∨
        (R.circuit n).steps.get ⟨t, ht⟩ = .callInverse wires) →
      ∀ a, (R.circuit n).stateAfter (U n) (appendBits ((D.data n).invariant x) x.val) t a ≠ 0 →
        advSerial (a ∘ wires) = (D.data n).invariant x

/-- Definition 6.8(ii)–(iii): soundness (= fully black-box derivation). For every adversary,
efficient or not, a non-negligible winning probability forces a non-negligible average accepted
weight of the reduction's output. -/
def Reduction.Sound {D : Scheme} {e : ℕ → ℕ} (R : Reduction D e) : Prop :=
  ∀ U, IsAdversary D e U → ¬ Negligible (advWin D e U) → ¬ Negligible (R.advantage U)

end InvariantMoneySecurity.Decomposition.Supplement


