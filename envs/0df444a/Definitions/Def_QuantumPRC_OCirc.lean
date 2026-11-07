-- Prove2me | Definitions.Def_QuantumPRC_OCirc
-- name    : QuantumPRC_OCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:34:22.622072+00:00
-- url     : https://prove2.me/theorems/f93720c4-8016-4c1c-bc01-794a44713d94
-- title:
--   Quantum circuits, oracle queries and uniform QPT adversaries (machine model)
-- statement:
--   The paper uses "QPT algorithm", "uniform QPT algorithm" and "QPT adversary $\mathcal A^{(\cdot)}$" with adaptive, possibly reference-entangled oracle queries, but fixes no machine model. This definition fixes one.
--
--   1. **Circuits.** A circuit acts on $N$ wires by the gates $H$, $T=\mathrm{diag}(1,e^{i\pi/4})$ and $\mathrm{CNOT}$. A circuit from $a$ to $b$ qubits places its input on $a$ designated wires, all other wires start in $|0\rangle$, applies its gates, and traces out every wire that is not one of its $b$ output wires; this defines its channel.
--   2. **Oracle circuits.** An oracle circuit may also contain queries. A query to oracle $i$ names injective lists of input wires and output wires; it traces out the output wires that are not input wires, applies the oracle channel from the input wires to the output wires, and resets to $|0\rangle$ the input wires that are not output wires. Its classical input is written on the first wires; its output is the measurement of wire $0$, and its **acceptance probability** $\Pr[1\leftarrow\mathcal A^{O}]$ is the probability of outcome $1$.
--   3. **Uniform families.** A family $(\mathcal A_\lambda)_\lambda$ of oracle circuits is **uniform** (a uniform QPT adversary) if one polynomial-time Turing machine prints the description of $\mathcal A_\lambda$ from $1^\lambda$.
--
--   Intermediate measurements and classical post-processing are covered by deferred measurement, since Toffoli and every classical reversible circuit are exact over $\{H,T,\mathrm{CNOT}\}$.
--
--   **Formalization Note** A security game runs the $\lambda$-th adversary on the empty classical input (the index $\lambda$ replaces the input $1^\lambda$); an adversary against an assumption is run on its challenge string. Circuits are encoded by an injective prefix code.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), §3.1, p.16 (QPT); Definition 4.3, p.25 (uniform QPT); §5, p.32 (adaptive multi-query, reference-entangled queries)

import Mathlib
import Definitions.Def_QuantumPRC_pauliXZ

open Matrix

namespace QuantumPRC

/-! # Quantum circuits, oracle queries and uniform families

Hsieh, Yamada, *Quantum Pseudorandom Error-Correcting Codes*, arXiv:2609.38986 (held file sha256
6901b59d…). The paper uses "QPT algorithm", "uniform QPT algorithm" (Definition 4.3, p.25) and
"QPT adversary `A^{(·)}`" with oracle access, including adaptive, reference-entangled queries (p.32),
without fixing a machine model. This file fixes one:

* a circuit acts on `N` wires (qubits `Fin N`) by the gates `H`, `T`, `CNOT` (Clifford+T);
* an oracle circuit may also contain queries: a query to oracle `i` names input wires `ins` and
  output wires `outs`; it traces out the wires of `outs` that are not in `ins`, applies the oracle
  channel from the `ins` wires to the `outs` wires, and re-initializes to `|0⟩` the wires of `ins`
  that are not in `outs`; all other wires are untouched;
* the classical input is written on the first wires, all other wires start in `|0⟩`, and the
  output bit is the measurement of wire `0` in the computational basis;
* a family of circuits is uniform if one polynomial-time Turing machine
  (`CookPvsNP.PolyTimeComputable`) prints the description of the `λ`-th circuit from `1^λ`
  (so the circuit size is polynomial).

Intermediate measurements and classical post-processing are covered by deferred measurement:
Toffoli and all classical reversible circuits are exact over Clifford+T.
-/

/-- A gate on `N` wires: Hadamard, `T = diag(1, e^{iπ/4})`, or `CNOT` with control `a` and target
`b ≠ a`. -/
inductive Gate (N : ℕ) where
  | H (a : Fin N)
  | T (a : Fin N)
  | CNOT (a b : Fin N) (h : a ≠ b)

/-- The unitary matrix of a gate, on the computational basis `Fin N → Bool`. -/
noncomputable def Gate.unitary {N : ℕ} : Gate N → Matrix (Bits N) (Bits N) ℂ
  | .H a => fun y x =>
      if (∀ i, i ≠ a → y i = x i) then
        (if x a = true ∧ y a = true then -1 else 1) / (Real.sqrt 2 : ℂ)
      else 0
  | .T a => Matrix.diagonal fun x =>
      if x a = true then Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) else 1
  | .CNOT a b _ => fun y x => if y = Function.update x b (Bool.xor (x b) (x a)) then 1 else 0

/-- An instruction of an oracle circuit on `N` wires with `k` oracles, each mapping `nIn` qubits
to `nOut` qubits: a gate, or a query to oracle `i` on the input wires `ins` and output wires
`outs` (both injective lists of wires). -/
inductive Instr (N nIn nOut k : ℕ) where
  | gate (g : Gate N)
  | query (i : Fin k) (ins : Fin nIn ↪ Fin N) (outs : Fin nOut ↪ Fin N)

/-- Semantics of a query (see the file header). For `ρ` on the `N` wires, the output entry at
`(y, y')` is the linear extension of: trace out the wires `J = outs ∖ ins`, apply `id ⊗ O` with `O`
from the `ins` wires to the `outs` wires, and put the wires `ins ∖ outs` into `|0⟩`. `W` is the set
of wires in neither `ins` nor `outs`. -/
noncomputable def queryMap {N nIn nOut : ℕ} (O : Superop (Bits nIn) (Bits nOut))
    (ins : Fin nIn ↪ Fin N) (outs : Fin nOut ↪ Fin N) : Superop (Bits N) (Bits N) := by
  classical
  exact fun ρ y y' =>
    let inI : Fin N → Prop := fun w => ∃ j, ins j = w
    let inO : Fin N → Prop := fun w => ∃ j, outs j = w
    if (∀ w, inI w → ¬ inO w → y w = false ∧ y' w = false) then
      ∑ x : Bits N, ∑ x' : Bits N,
        if (∀ w, ¬ inI w → ¬ inO w → x w = y w ∧ x' w = y' w) ∧
            (∀ w, inO w → ¬ inI w → x w = x' w) then
          ρ x x' * O (Matrix.single (fun j => x (ins j)) (fun j => x' (ins j)) 1)
            (fun j => y (outs j)) (fun j => y' (outs j))
        else 0
    else 0

/-- The superoperator of one instruction, given the oracles. -/
noncomputable def Instr.apply {N nIn nOut k : ℕ} (O : Fin k → Superop (Bits nIn) (Bits nOut)) :
    Instr N nIn nOut k → Superop (Bits N) (Bits N)
  | .gate g => conjMap g.unitary
  | .query i ins outs => queryMap (O i) ins outs

/-- **Oracle circuit (QPT adversary at one value of λ).** `N` wires and a list of instructions,
executed first to last. -/
structure OCirc (nIn nOut k : ℕ) where
  N : ℕ
  instrs : List (Instr N nIn nOut k)

/-- The basis state that writes the classical input `word` on the first wires (bits beyond the
`N` wires are not read) and `0` on all other wires. -/
def inputBasis (N : ℕ) (word : List Bool) : Bits N := fun i => word.getD i.val false

/-- **Acceptance probability** `Pr[1 ← A^{O}(word)]`: start from `|x₀⟩⟨x₀|` with `x₀` the input
basis state, apply the instructions with oracles `O`, and measure wire `0`
(probability of outcome `1`; it is `0` for a circuit with no wire). -/
noncomputable def OCirc.accept {nIn nOut k : ℕ} (A : OCirc nIn nOut k)
    (O : Fin k → Superop (Bits nIn) (Bits nOut)) (word : List Bool) : ℝ := by
  classical
  exact
    let ρ0 : Matrix (Bits A.N) (Bits A.N) ℂ :=
      Matrix.single (inputBasis A.N word) (inputBasis A.N word) 1
    let ρ := A.instrs.foldl (fun σ ins => ins.apply O σ) ρ0
    (∑ x : Bits A.N, if (∃ h : 0 < A.N, x ⟨0, h⟩ = true) then ρ x x else 0).re

/-- Number of oracle queries of an oracle circuit. -/
def OCirc.numQueries {nIn nOut k : ℕ} (A : OCirc nIn nOut k) : ℕ :=
  (A.instrs.filter fun ins => match ins with
    | .gate _ => false
    | .query _ _ _ => true).length

/-- **Circuit implementing a channel from `a` to `b` qubits** (no oracle): `N` wires, the input
qubits on the wires `inW`, the output qubits on the wires `outW`, and a gate list. -/
structure Circuit (a b : ℕ) where
  N : ℕ
  inW : Fin a ↪ Fin N
  outW : Fin b ↪ Fin N
  gates : List (Gate N)

/-- The channel of a circuit: put the input on the wires `inW` and `|0⟩` on all other wires, apply
the gates (first gate first), and trace out every wire not in `outW`. -/
noncomputable def Circuit.channel {a b : ℕ} (C : Circuit a b) : Superop (Bits a) (Bits b) := by
  classical
  exact fun ρ y y' =>
    let σ : Matrix (Bits C.N) (Bits C.N) ℂ := fun x x' =>
      if (∀ w, (¬ ∃ j, C.inW j = w) → x w = false ∧ x' w = false) then
        ρ (fun j => x (C.inW j)) (fun j => x' (C.inW j))
      else 0
    let τ := C.gates.foldl (fun σ g => conjMap g.unitary σ) σ
    ∑ x : Bits C.N, ∑ x' : Bits C.N,
      if (fun j => x (C.outW j)) = y ∧ (fun j => x' (C.outW j)) = y' ∧
          (∀ w, (¬ ∃ j, C.outW j = w) → x w = x' w) then τ x x'
      else 0

/-- Self-delimiting code of a natural number: `1^n 0`. -/
def natCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- Code of a gate. -/
def Gate.encode {N : ℕ} : Gate N → List Bool
  | .H a => [false, false] ++ natCode a.val
  | .T a => [false, true] ++ natCode a.val
  | .CNOT a b _ => [true, false] ++ natCode a.val ++ natCode b.val

/-- Code of an instruction. -/
def Instr.encode {N nIn nOut k : ℕ} : Instr N nIn nOut k → List Bool
  | .gate g => false :: g.encode
  | .query i ins outs =>
      true :: natCode i.val ++ (List.ofFn fun j => natCode (ins j).val).flatten ++
        (List.ofFn fun j => natCode (outs j).val).flatten

/-- Code of an oracle circuit (injective). -/
def OCirc.encode {nIn nOut k : ℕ} (A : OCirc nIn nOut k) : List Bool :=
  natCode A.N ++ natCode A.instrs.length ++ (A.instrs.map Instr.encode).flatten

/-- Code of a circuit (injective). -/
def Circuit.encode {a b : ℕ} (C : Circuit a b) : List Bool :=
  natCode C.N ++ (List.ofFn fun j => natCode (C.inW j).val).flatten ++
    (List.ofFn fun j => natCode (C.outW j).val).flatten ++ natCode C.gates.length ++
    (C.gates.map Gate.encode).flatten

/-- **Uniform QPT algorithm / adversary.** A family `A λ` of oracle circuits is uniform if one
polynomial-time Turing machine prints the code of `A λ` from `1^λ`. Adversaries of the security
games are such families; the `λ`-th member is run on the empty classical input (it is indexed by
`λ`, which replaces the input `1^λ`), and an adversary for an assumption is run on its challenge. -/
def IsUniformAdv {nIn nOut : ℕ → ℕ} {k : ℕ} (A : ∀ lam, OCirc (nIn lam) (nOut lam) k) : Prop :=
  ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
    ∀ lam, f (unary lam) = (A lam).encode

end QuantumPRC


