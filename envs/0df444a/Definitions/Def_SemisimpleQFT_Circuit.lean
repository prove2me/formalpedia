-- Prove2me | Definitions.Def_SemisimpleQFT_Circuit
-- name    : SemisimpleQFT_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-19T15:08:28.977803+00:00
-- url     : https://prove2.me/theorems/bc5c6939-927d-4a82-8a10-95150ae8c3b0
-- title:
--   Implementing the Fourier transform of a diagram algebra by a quantum circuit: encodings, error and gate count
-- statement:
--   This file fixes the conventions under which Theorem 6.12 is stated; the source assumes the standard circuit model without spelling them out. It builds on the shared circuit layer `QAlgorithms.Circuit` (a circuit on $w$ qubits is a list of gates, each applied to an ordered tuple of distinct wires; its size is the number of gates).
--
--   - `localGates` is the gate set of all unitary gates acting on at most two qubits.
--   - `padBits w l` places a bit string $l$ on the first wires of a $w$-qubit register and sets all other wires to $0$. `encMatrix w enc` is the matrix of the linear map $|a\rangle\mapsto|\mathrm{enc}(a),0\cdots0\rangle$.
--   - `Implements w c encIn encOut T err`: the circuit $c$ on $w$ qubits implements the linear map $T$ (from the space with basis $\iota$ to the space with basis $\kappa$) up to operator norm error `err`: all code words have length at most $w$ and
--   $$\big\|U_c\,J_{\mathrm{in}}-J_{\mathrm{out}}\,T\big\|_\infty\le \mathrm{err},$$
--   where $J_{\mathrm{in}}|a\rangle=|\mathrm{encIn}(a),0\cdots0\rangle$ and $J_{\mathrm{out}}|k\rangle=|\mathrm{encOut}(k),0\cdots0\rangle$. In particular all work qubits start and end in $|0\rangle$.
--   - `natBits w x` is the list of the $w$ lowest binary digits of $x$, least significant first.
--   - `diagramBits D`: for each of the $2n$ vertices in the order $1,\dots,n,1',\dots,n'$, the position (counted from $0$ in this order) of the first vertex of its block, written with `Nat.size (2n)` binary digits. This stores a diagram in $O(n\log n)$ qubits.
--   - `shapeBits λ`: the $N$ row lengths of $\lambda$, each with `Nat.size N` binary digits; `pairBits` concatenates the codes of the two components of a pair; `pathBits enc P` concatenates the codes of the entries $\rho_0,\dots,\rho_t$ of a Bratteli path.
--   - `softO C k f` $=C\cdot f\cdot\log(2+f)^k$, the explicit form of $\widetilde O(f)$.
--
--   `HasEfficientQFT m level d B size encV gates err` is the assertion of Theorem 6.12 for one chain $A_0\subseteq\dots\subseteq A_m=A$ of diagram algebras with Bratteli diagram $B$: there exist a subalgebra adapted system of Fourier bases for the chain which is standard (orthogonal form, labelling as in Theorem 4.17), and a circuit over `localGates` with at most `gates` gates that implements, up to operator norm error `err`, the Fourier transform $\mathrm{FT}_A$ of Definition 3.1 taken with respect to the scaled diagram basis $\mathcal B(A)$ and this Fourier basis. The input $|a\rangle$ is stored by `diagramBits` of its diagram and the output $|\rho,P,Q\rangle$ by `pathBits P` followed by `pathBits Q`.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, Section 6, pp. 36, 49–52: input encoding (p. 36), Lemma 6.11 (clean ancillas), Theorem 6.12, Eqs. (6.82)–(6.84); $\widetilde O$ convention p. 14

import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_SemisimpleQFT_Chains

/-!
# Implementing the Fourier transform of a diagram algebra by a quantum circuit

Source: B. Foxman, B. Nehoran, Y. Ding, *Efficient Quantum Fourier Transforms For Semisimple
Algebras*, Section 6 (PDF pp. 36–52).

Conventions (the source assumes "familiarity with the basics of quantum computation, including
... quantum circuits", PDF p. 14, and fixes none of these explicitly):

* A circuit is a list of gates on `w` qubits (the shared layer `QAlgorithms.Circuit`); its gate
  complexity is the number of gates. The gates are arbitrary unitaries on one or two qubits
  (`localGates`).
* A basis element of the algebra is stored by its underlying diagram (PDF p. 36), a diagram by
  a bit string (`diagramBits`); a Fourier basis state `|ρ, P, Q⟩` by the bit strings of the two
  Bratteli paths `P`, `Q` (`pathBits`), `ρ` being their common endpoint. A bit string is placed
  on the first wires of the register and all remaining wires are `|0⟩`.
* A circuit `U` implements a linear map `T` from the input basis to the output basis up to
  operator norm error `err` if `‖U J_in - J_out T‖_∞ ≤ err`, where `J_in`, `J_out` are the
  isometries sending a basis element to its encoded basis state (all other wires `|0⟩`): the
  work wires start and end in `|0⟩` (PDF p. 49, Lemma 6.11: "unentangled ancilla registers").
-/

set_option warn.classDefReducibility false

namespace SemisimpleQFT

open scoped BigOperators ComplexConjugate
open QAlgorithms

/-- The gate set: all unitary gates acting on at most two qubits. -/
def localGates : Set Gate := {g | g.IsUnitary ∧ g.arity ≤ 2}

/-- A bit string placed on the first wires of a `w`-qubit register, the remaining wires being
`0` (`false`). -/
def padBits (w : ℕ) (l : List Bool) : Qubits w := fun i => l.getD i.val false

/-- The linear map `|a⟩ ↦ |enc a, 0…0⟩` from the space with basis `ι` to the `w`-qubit register,
as a matrix. -/
noncomputable def encMatrix {ι : Type*} (w : ℕ) (enc : ι → List Bool) :
    Matrix (Qubits w) ι ℂ :=
  Matrix.of fun x a => if x = padBits w (enc a) then 1 else 0

/-- The circuit `c` on `w` qubits implements the linear map `T` (rows `κ`, columns `ι`) up to
operator norm error `err`, with respect to the encodings `encIn`, `encOut` of the input and
output bases: every code word fits in the register, and
`‖U_c J_in - J_out T‖_∞ ≤ err`, where `J_in |a⟩ = |encIn a, 0…0⟩` and
`J_out |k⟩ = |encOut k, 0…0⟩`. -/
def Implements {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (w : ℕ)
    (c : Circuit localGates w) (encIn : ι → List Bool) (encOut : κ → List Bool)
    (T : Matrix κ ι ℂ) (err : ℝ) : Prop :=
  (∀ a : ι, (encIn a).length ≤ w) ∧ (∀ k : κ, (encOut k).length ≤ w) ∧
    specNorm (c.unitary * encMatrix w encIn - encMatrix w encOut * T) ≤ err

/-- The `w` lowest binary digits of `x`, least significant first. -/
def natBits (w x : ℕ) : List Bool := (List.range w).map fun i => x.testBit i

variable {n : ℕ}

/-- The position of a vertex in the order `1, …, n, 1', …, n'`, counted from `0`. -/
def vertexIndex (v : Vertex n) : ℕ := if v.1 then n + v.2.val else v.2.val

/-- The least position (in the order `1, …, n, 1', …, n'`) of a vertex in the block of `v`. -/
noncomputable def blockMin (D : Diagram n) (v : Vertex n) : ℕ :=
  sInf {k : ℕ | ∃ u : Vertex n, D v u ∧ vertexIndex u = k}

/-- The bit string storing a diagram (PDF p. 36: "`Õ(n)` qubits"): for each of the `2n` vertices
in the order `1, …, n, 1', …, n'`, the least position of a vertex of its block, written with
`Nat.size (2 n)` binary digits. -/
noncomputable def diagramBits (D : Diagram n) : List Bool :=
  ((List.finRange n).map (fun i => ((false, i) : Vertex n)) ++
      (List.finRange n).map (fun i => ((true, i) : Vertex n))).flatMap
    fun v => natBits (Nat.size (2 * n)) (blockMin D v)

/-- The bit string storing a Young diagram: its `N` row lengths, each written with `Nat.size N`
binary digits. -/
def shapeBits {N : ℕ} (s : Shape N) : List Bool :=
  (List.finRange N).flatMap fun i => natBits (Nat.size N) (s.1 i).val

/-- The bit string storing a pair of Young diagrams. -/
def pairBits {N : ℕ} (v : Shape N × Shape N) : List Bool := shapeBits v.1 ++ shapeBits v.2

/-- The bit string storing a Bratteli path `(ρ_0, …, ρ_t)`: the bit strings of its entries, in
order. -/
def pathBits {V : Type} {B : Bratteli V} {t : ℕ} (enc : V → List Bool) (p : B.Path t) :
    List Bool :=
  (List.finRange (t + 1)).flatMap fun i => enc (p.at i)

/-- `C · f · log(2 + f)^k`: the bound abbreviated `Õ(f)` (PDF p. 14: "`Õ(·)` hides
polylogarithmic factors"), with explicit constants `C` and `k`. -/
noncomputable def softO (C : ℝ) (k : ℕ) (f : ℝ) : ℝ := C * f * Real.log (2 + f) ^ k

/-- Theorem 6.12 (PDF p. 52) for one chain of diagram algebras. `level` is the chain
`A_0 ⊆ … ⊆ A_m = A` of diagram sets with parameter `d`, `B` its Bratteli diagram with labels in
`V`, `size` the number of boxes of a label and `encV` the bit string of a label.

The statement: there is a subalgebra adapted system of Fourier bases for the chain, in the
orthogonal form and with the labelling of Theorem 4.17 (`IsStandard`), and a circuit of at most
`gates` one- and two-qubit gates which implements the Fourier transform `FT_A` of Definition 3.1
— taken with respect to the scaled diagram basis `𝓑(A)` and this Fourier basis — up to operator
norm error `err`. The input `|a⟩` is stored by the diagram of `a`, the output `|ρ, P, Q⟩` by the
Bratteli paths `P` and `Q`. -/
def HasEfficientQFT {V : Type} [Finite V] (m : ℕ) (level : ℕ → Set (Diagram n)) (d : ℕ)
    (B : Bratteli V) (size : V → ℕ) (encV : V → List Bool) (gates err : ℝ) : Prop :=
  ∃ G : GTSystem m (fun t => diagramAlgebra (level t) d) B, G.IsStandard size ∧
    ∃ (w : ℕ) (c : Circuit localGates w), (c.size : ℝ) ≤ gates ∧
      Implements w c (fun D : level m => diagramBits D.1)
        (fun p : G.top.Idx => pathBits encV p.row ++ pathBits encV p.col)
        (G.top.FT (diagBasis (level m) d)) err

end SemisimpleQFT


