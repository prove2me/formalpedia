-- Prove2me | Definitions.Def_GL2QFT_Uniform
-- name    : GL2QFT_Uniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:44.010098+00:00
-- url     : https://prove2.me/theorems/4c354f65-8bc0-4880-8dfa-858b4550d7b6
-- title:
--   Clifford+T circuits, operator-norm implementation with clean ancillas, and uniform families
-- statement:
--   The notion of a uniform efficient implementation used by Theorem 6.1 and its circuit milestones.
--
--   1. **Circuits.** A circuit is a list of instructions $H$, $S$, $T$, $X$ on a wire and $\mathrm{CNOT}$ on two distinct wires; its unitary is the product of the gates in list order and its size is the number of instructions.
--   2. **Implementation.** A unitary $U$ on $n$ qubits implements a linear map $\Phi:\mathbb C^X\to\mathbb C^Y$ to operator-norm error $\varepsilon$, for input and output codes padded with $|0\rangle$ ancillas, if for every $\psi\in\mathbb C^X$
--   $$\|U V_{\mathrm{in}}\psi-V_{\mathrm{out}}\Phi\psi\|_2\le\varepsilon\,\|\psi\|_2 .$$
--   3. **Uniform family.** One polynomial-time computable map $f$ and one constant $c$, chosen before the data, have the following property for every field data $D$ (in a prescribed class) and every $k\in\mathbb N$. The map $f$ sends the code of $D$ followed by $1^k$ to the wire count and the instruction list of a circuit of at most $c(\lfloor\log_2q\rfloor+k+2)^c$ gates. That circuit implements $\Phi_D$ to error $2^{-k}$.
--
--   Taking $k=\lceil\log_2(1/\varepsilon)\rceil$ gives, for every $\varepsilon>0$, a uniform circuit of size $\mathrm{poly}(\log q,\log(1/\varepsilon))$ with error at most $\varepsilon$.
--
--   **Formalization Note** The gate set $\{H,S,T,X,\mathrm{CNOT}\}$ is the stronger reading of the paper's unnamed "elementary gates": by Solovay–Kitaev any other finite universal set changes the size by a $\mathrm{polylog}(1/\varepsilon)$ factor. The error is measured in the Euclidean norm, with no global phase, and the ancillas must return to $|0\rangle$ (Lemma 6.8: "with all ancillary registers returned to zero"). When $X$ is only part of a register (a partial isometry such as (117)), the bound is required on $\mathbb C^X$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.1 p.34 (PDF p.35), Remark 6.3 p.34, Lemma 6.8 p.41 (PDF p.42), §1.1 p.4 (elementary gates)

import Definitions.Def_GL2QFT_Codes
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Complexity

noncomputable section

open Classical

namespace GL2QFT

open QAlgorithms QAlgorithms.Complexity

/-- The elementary gate set `{H, S, T, X, CNOT}` (Clifford+T) as one- and two-qubit gates of the
published circuit layer.

**Formalization Note** arXiv:2608.28573 counts "elementary gates" ("one- and two-qubit gates",
p.4) without naming a set. The finite set `{H, S, T, X, CNOT}` is the stronger reading: every
circuit over it is a circuit of one- and two-qubit gates, and by Solovay–Kitaev any other finite
universal set costs only a `polylog(1/ε)` factor. -/
def cliffordT : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 phaseS, Gate.ofMatrix1 gateT, Gate.ofMatrix1 pauliX,
    Gate.ofMatrix2 cnot}

/-- The wire embedding of a one-qubit gate on wire `i`. -/
def wire1 {n : ℕ} (i : Fin n) : Fin 1 ↪ Fin n := ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩

/-- The wire embedding of a two-qubit gate on the distinct wires `i` (gate wire 0, the control)
and `j` (gate wire 1). -/
def wire2 {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Fin 2 ↪ Fin n :=
  ⟨![i, j], by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]⟩

/-- An instruction `H, S, T, X` on wire `i`, or `CNOT` with control `i` and target `j`, of the
published syntax `QAlgorithms.Complexity.Instr`, as a gate application of `cliffordT`. -/
def instrApp {n : ℕ} : Instr n → GateApp cliffordT n
  | .h i => ⟨Gate.ofMatrix1 hadamard, by simp [cliffordT], wire1 i⟩
  | .s i => ⟨Gate.ofMatrix1 phaseS, by simp [cliffordT], wire1 i⟩
  | .t i => ⟨Gate.ofMatrix1 gateT, by simp [cliffordT], wire1 i⟩
  | .x i => ⟨Gate.ofMatrix1 pauliX, by simp [cliffordT], wire1 i⟩
  | .cnot i j hij => ⟨Gate.ofMatrix2 cnot, by simp [cliffordT], wire2 i j hij⟩

/-- The unitary of a list of instructions (applied in list order, head first). Its size is the
list length. -/
def circUnitary {n : ℕ} (c : List (Instr n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  Circuit.unitary (c.map instrApp)

/-- The isometric embedding `V : ℂ^X → ℂ^{Qubits n}` of a register code `code : X → Qubits n`:
`V|x⟩ = |code x⟩`, extended linearly (`(Vψ)(y) = Σ_{code x = y} ψ(x)`). -/
def embedVec {X : Type} [Fintype X] {n : ℕ} (code : X → Qubits n) (ψ : EuclideanSpace ℂ X) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun y => ∑ x, if code x = y then ψ x else 0

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 6.1 and Lemma 6.8, pp.34 and 41:
the circuit unitary `U` on `n` wires implements the linear map `Φ : ℂ^X → ℂ^Y` to operator-norm
error at most `ε`, "with all ancillary registers returned to zero", for the input code `cin` and
the output code `cout`: for every `ψ ∈ ℂ^X`,
`‖U (V_in ψ) − V_out (Φ ψ)‖₂ ≤ ε ‖ψ‖₂`.

**Formalization Note** The norms are the Euclidean norms of `EuclideanSpace` (not the sup norm of
`X → ℂ`). There is no global phase: the ancillas (the wires outside the codes) start and must end
in `|0⟩`, and the comparison includes them. When `X` is a proper subset of a register (the
domain of a partial isometry such as (117) or (120)), the bound is required on `ℂ^X` only. -/
def Implements {X Y : Type} [Fintype X] [Fintype Y] {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (cin : X → Qubits n) (cout : Y → Qubits n) (Φ : Matrix Y X ℂ) (ε : ℝ) : Prop :=
  ∀ ψ : EuclideanSpace ℂ X,
    ‖act U (embedVec cin ψ) - embedVec cout (WithLp.toLp 2 (Φ.mulVec (WithLp.ofLp ψ)))‖ ≤ ε * ‖ψ‖

/-- arXiv:2608.28573, Theorem 6.1, p.34, with Remark 6.3: a **uniform** family of circuits of size
`poly(log q, log(1/ε))` implements `Φ D` to operator-norm error `ε`, for every field data `D` with
`P D`. Explicitly, there are a wire count `wires D k`, a `{H,S,T,X,CNOT}` circuit `circ D k`, a
polynomial-time computable `f : {0,1}* → {0,1}*` and a constant `c`, all chosen before `D` and `k`,
such that for every `D` with `P D` and every `k`:
1. `f` maps the binary code of `D` followed by `1^k` to the wire count (unary) followed by the
   instruction list of `circ D k` (`encLayer`, prefix-free by its tags);
2. `circ D k` has at most `c · (⌊log₂ q⌋ + k + 2)^c` gates;
3. the codes fit on the wires (`inW D ≤ wires D k`, `outW D ≤ wires D k`, the rest zero padding);
4. `circ D k` implements `Φ D` to operator-norm error `2^{−k}` (`Implements`).

**Formalization Note** `k` plays `⌈log₂(1/ε)⌉`: for `ε > 0` take `k = ⌈log₂(1/ε)⌉₊`, so the error is
`2^{−k} ≤ ε` and the size is `poly(log q, log(1/ε))`. Uniformity is joint in `(D, ε)`. The
predicate `P` restricts the field data (the goal uses `P = True`; §6.5 uses `q > 2`). -/
def UniformlyImplementsOn (P : FieldData → Prop) {X Y : FieldData → Type}
    [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ}
    (cin : ∀ D, X D → Qubits (inW D)) (cout : ∀ D, Y D → Qubits (outW D))
    (Φ : ∀ D, Matrix (Y D) (X D) ℂ) : Prop :=
  ∃ (wires : FieldData → ℕ → ℕ) (circ : ∀ D k, List (Instr (wires D k))) (f : Str → Str) (c : ℕ),
    PolyTimeComputable f ∧
    (∀ D, P D → ∀ k : ℕ, f (D.encData ++ encNat k) = encNat (wires D k) ++ encLayer (circ D k)) ∧
    (∀ D, P D → ∀ k : ℕ, (circ D k).length ≤ c * (Nat.log 2 D.q + k + 2) ^ c) ∧
    (∀ D, P D → ∀ k : ℕ, inW D ≤ wires D k ∧ outW D ≤ wires D k ∧
      Implements (circUnitary (circ D k)) (fun x => padTo (wires D k) (cin D x))
        (fun y => padTo (wires D k) (cout D y)) (Φ D) ((1 / 2 : ℝ) ^ k))

end GL2QFT


