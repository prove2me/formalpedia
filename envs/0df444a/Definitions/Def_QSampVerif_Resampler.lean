-- Prove2me | Definitions.Def_QSampVerif_Resampler
-- name    : QSampVerif_Resampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:16.376851+00:00
-- url     : https://prove2.me/theorems/e06606e6-1e50-43d6-8b5c-0c0dbd8259ac
-- title:
--   Resampling circuits on the output alphabet $\mathcal Y\cup\{\bot\}$ and the induced map on diagonal operators
-- statement:
--   Fix $m$ and the output alphabet $\mathcal Y\cup\{\bot\}$ with $\mathcal Y=\{0,1\}^m$. A **resampling circuit** has $n$ wires started in $|0\cdots0\rangle$; its classical input $z$ is written as an acceptance flag followed by the string ($\bot\mapsto0\,0^m$, $y\mapsto1\,y$) into designated wires by $X$ flips; a layered Clifford+T circuit runs; a flag wire and $m$ output wires are measured, and the output is $\bot$ if the flag reads $0$ and the read string otherwise. Its transition probabilities $\Pr[z'\mid z]$ are given by the Born rule.
--
--   The induced map on diagonal operators of the output register (real functions on $\mathcal Y\cup\{\bot\}$) is
--
--   $$\mathcal T(f)(z')=\sum_z f(z)\Pr[z'\mid z],$$
--
--   and $\delta_\bot$ is the rejected output state.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Lemma 14.1, p.184 (PDF 185)

import Definitions.Def_QSampVerif_TargetCircuit

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- The input bits of a classical register with alphabet `Y ∪ {⊥}`, `Y = {0,1}^m`: an acceptance
flag followed by the string (`⊥ ↦ 0 0…0`, `y ↦ 1 y`). -/
def optBits {m : ℕ} : Option (Qubits m) → Qubits (m + 1)
  | none => fun _ => false
  | some y => Fin.cons true y

/-- A quantum circuit with a classical input and a classical output, both in `Y ∪ {⊥}` with
`Y = {0,1}^m` (Lemma 14.1, p.184: an operation that "leaves rejection unchanged and replaces every
accepted string"). It has `n` wires started in `|0…0⟩`; the input `optBits z` is written into the
wires `inW` by `X` flips; the layered Clifford+T circuit runs; the flag wire and the `m` output
wires are measured, and the output is `⊥` if the flag reads `0` and the read string otherwise. -/
structure Resampler (m : ℕ) where
  /-- Number of wires. -/
  n : ℕ
  /-- Input wires (flag first). -/
  inW : Fin (m + 1) → Fin n
  /-- The circuit. -/
  circ : Layered n
  /-- The output flag wire. -/
  flagW : Fin n
  /-- The output string wires. -/
  outW : Fin m → Fin n

namespace Resampler

variable {m : ℕ}

/-- Well formed: distinct input wires, distinct output wires, the flag is not an output wire,
disjoint gates in each layer. -/
def Valid (R : Resampler m) : Prop :=
  Function.Injective R.inW ∧ Function.Injective R.outW ∧ (∀ j, R.outW j ≠ R.flagW) ∧
    ∀ l ∈ R.circ, LayerOk l

/-- The classical description of the circuit. -/
def encode (R : Resampler m) : Str :=
  tup [unary R.n, tup (List.ofFn fun j => unary (R.inW j).val), encCirc R.circ,
    unary R.flagW.val, tup (List.ofFn fun j => unary (R.outW j).val)]

/-- The computational basis configuration holding the input `z`. -/
def inputCfg (R : Resampler m) (z : Option (Qubits m)) : Qubits R.n :=
  fun i => decide (∃ j, R.inW j = i ∧ optBits z j = true)

/-- The classical output read from a measured configuration `w`. -/
def readOut (R : Resampler m) (w : Qubits R.n) : Option (Qubits m) :=
  if w R.flagW then some (fun j => w (R.outW j)) else none

/-- The transition probability `Pr[output z' | input z]` (Born rule). -/
noncomputable def kernel (R : Resampler m) (z z' : Option (Qubits m)) : ℝ :=
  ∑ w : Qubits R.n, if R.readOut w = z' then
    ‖runLayered R.circ (fun y => if y = R.inputCfg z then 1 else 0) w‖ ^ 2 else 0

/-- The induced map on diagonal operators of the classical register (real functions on
`Y ∪ {⊥}`): `T(f)(z') = Σ_z f(z) Pr[z' | z]`. -/
noncomputable def apply (R : Resampler m) (f : Option (Qubits m) → ℝ) : Option (Qubits m) → ℝ :=
  fun z' => ∑ z, f z * R.kernel z z'

end Resampler

/-- The rejected output state `δ_⊥` as a diagonal operator. -/
def deltaNone {m : ℕ} : Option (Qubits m) → ℝ := fun z => if z.isNone then 1 else 0

end QSampVerif


