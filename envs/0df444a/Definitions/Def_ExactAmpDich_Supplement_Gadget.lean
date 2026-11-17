-- Prove2me | Definitions.Def_ExactAmpDich_Supplement_Gadget
-- name    : ExactAmpDich_Supplement_Gadget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:20:31.179196+00:00
-- url     : https://prove2.me/theorems/00073d30-f0ef-41c8-940f-e92cb8a25a28
-- title:
--   Basis-postselected gadgets, their tensors, the three resource outcomes, and the library $\{U,U^\dagger\}$
-- statement:
--   A **basis-postselected gadget** over a library is a circuit on $n$ wires in which some input wires are fixed to computational-basis bits $\eta_{\mathrm{in}}$, some output wires are fixed to bits $\eta_{\mathrm{out}}$, and the remaining $a$ inputs and $b$ outputs are open, listed in a fixed order. Its **tensor** is the submatrix
--   $$T_{y,x}=\langle y,\eta_{\mathrm{out}}|U_F|x,\eta_{\mathrm{in}}\rangle,$$
--   with $x$, $y$ the bits on the open inputs and outputs. A *state gadget* has no open inputs.
--
--   1. A state gadget with one open output produces the one-qubit state $s_0|0\rangle+s_1|1\rangle$, $s_v=T_v$; it is **coherent** when $s_0s_1\ne0$.
--   2. A state gadget with two open outputs produces $|A\rangle=\sum_{i,j}A_{ij}|ij\rangle$, $A_{ij}=T_{ij}$. It is **symmetric entangled** when $A$ is invertible and $A=A^{\mathsf T}$, and **entangled with unequal Schmidt coefficients** when $A$ is invertible and its singular values differ, i.e. $AA^\dagger$ is not a scalar multiple of the identity.
--   3. The gadget's **code** lists $n$, the gate occurrences (gate index and wires), the open wires and the fixed bits; distinct gadgets have distinct codes.
--   4. For a $k$-qubit matrix $U$, the **two-gate library** $\{U,U^\dagger\}$ has gate $0$ equal to $U$ and gate $1$ equal to $U^\dagger$.
--
--   **Formalization Note** Pinned input and output wires may differ, which covers fresh and retired wires.
-- source:
--   Liu–Meng, A Dichotomy for Exact Quantum Circuit Amplitudes, STOC 2027 submission (held manuscript, sha256 40ad9c68…), App. A.3, p.19 (PDF p.20); App. B.1, pp.20–21 (PDF pp.21–22); Theorem C.1, p.27 (PDF p.28)

import Mathlib
import Definitions.Def_ExactAmpDich_Circuit

set_option autoImplicit false

namespace ExactAmpDich.Supplement

open QAlgorithms

/-- A **basis-postselected gadget** over a library `L`: a circuit on `n` wires whose `a` open input
ports sit on the wires `ins 0, …, ins (a-1)` and whose `b` open output ports sit on the wires
`outs 0, …, outs (b-1)` (in this order); every other input wire is fixed to the bit `etaIn i` and
every other output wire is fixed to the bit `etaOut i`. Liu–Meng, *A Dichotomy for Exact Quantum
Circuit Amplitudes*, STOC 2027 submission (held manuscript, sha256 40ad9c68…), App. B.1, pp.20–21
(PDF pp.21–22): "A basis-postselected gadget is a circuit F with selected input and output ports
fixed to bits in the computational basis. The remaining ports are open."

**Formalization Note.** The pinned input and output wires may differ (fresh and retired wires);
the values `etaIn i` (resp. `etaOut i`) at open wires are ignored. -/
structure Gadget (L : Library) where
  /-- The number of wires. -/
  n : ℕ
  /-- The circuit. -/
  c : Circuit L n
  /-- The number of open inputs. -/
  a : ℕ
  /-- The number of open outputs. -/
  b : ℕ
  /-- The wires of the open inputs, in order. -/
  ins : Fin a ↪ Fin n
  /-- The wires of the open outputs, in order. -/
  outs : Fin b ↪ Fin n
  /-- The bits fixed on the other input wires. -/
  etaIn : Fin n → Bool
  /-- The bits fixed on the other output wires. -/
  etaOut : Fin n → Bool

/-- The global bit string with the open bits `y` on the wires `w` and the fixed bits `η`
elsewhere. -/
noncomputable def fillBits {n m : ℕ} (w : Fin m ↪ Fin n) (y : Fin m → Bool) (η : Fin n → Bool) :
    Qubits n :=
  fun i => open Classical in if h : ∃ l, w l = i then y h.choose else η i

/-- The **tensor** of a gadget: `T_{y,x} = ⟨y, η_out|U_F|x, η_in⟩`. Liu–Meng, App. B.1, p.21:
"its entries are Ty,x = ⟨y, ηout|UF |x, ηin⟩, where x, y label the open inputs and outputs". -/
noncomputable def Gadget.tensor {L : Library} (G : Gadget L) (y : Fin G.b → Bool)
    (x : Fin G.a → Bool) : ℂ :=
  G.c.unitary (fillBits G.outs y G.etaOut) (fillBits G.ins x G.etaIn)

/-- The one-qubit state `s₀|0⟩ + s₁|1⟩` of a gadget with no open input and one open output:
`s_v = T_{v}`. -/
noncomputable def Gadget.state1 {L : Library} (G : Gadget L) (v : Bool) : ℂ :=
  G.tensor (fun _ => v) (fun _ => false)

/-- The `2 × 2` coefficient matrix `A_{ij} = T_{ij}` of a gadget with no open input and two open
outputs (`|A⟩ = Σ A_{ij} |ij⟩`, Liu–Meng, App. A.3, p.19). -/
noncomputable def Gadget.state2 {L : Library} (G : Gadget L) : Matrix Bool Bool ℂ :=
  fun i j => G.tensor (fun l => if l.val = 0 then i else j) (fun _ => false)

/-- The gadget is a state gadget producing a **coherent one-qubit state**: no open input, one open
output, and `s₀ s₁ ≠ 0`. Liu–Meng, App. A.3, p.19 (PDF p.20): "A one-qubit state s0|0⟩+ s1|1⟩ is
coherent when s0s1 ≠ 0"; App. B.1, p.21: "A state gadget has no open inputs." -/
def Gadget.IsCoherentState {L : Library} (G : Gadget L) : Prop :=
  G.a = 0 ∧ G.b = 1 ∧ G.state1 false * G.state1 true ≠ 0

/-- The gadget is a state gadget producing a two-qubit state with an **invertible symmetric
coefficient matrix**. -/
def Gadget.IsSymmetricEntangledState {L : Library} (G : Gadget L) : Prop :=
  G.a = 0 ∧ G.b = 2 ∧ IsUnit G.state2.det ∧ G.state2.transpose = G.state2

/-- The gadget is a state gadget producing an **entangled two-qubit state with unequal Schmidt
coefficients**: the coefficient matrix `A` is invertible and `A A†` is not a scalar multiple of
the identity. Liu–Meng, App. A.3, p.19: "An entangled two-qubit state is nonmaximal when its two
Schmidt coefficients, equivalently the singular values of its coefficient matrix, are unequal."

**Formalization Note.** The singular values of `A` are the square roots of the eigenvalues of the
Hermitian matrix `A A†`, so they are equal exactly when `A A†` is scalar. -/
def Gadget.IsUnequalSchmidtState {L : Library} (G : Gadget L) : Prop :=
  G.a = 0 ∧ G.b = 2 ∧ IsUnit G.state2.det ∧
    ¬ ∃ r : ℂ, G.state2 * G.state2.conjTranspose = r • (1 : Matrix Bool Bool ℂ)

/-- Finite code of a gadget: `n`, the occurrences (gate index, wire list), the open input wires,
the open output wires, and the two fixed bit strings. -/
abbrev GadgetCode : Type := ℕ × List (ℕ × List ℕ) × List ℕ × List ℕ × List Bool × List Bool

/-- The code of a gadget. Distinct gadgets have distinct codes. -/
def Gadget.code {L : Library} (G : Gadget L) : GadgetCode :=
  (G.n, G.c.map (fun p => (p.1.val, List.ofFn fun i => (p.2 i).val)),
    List.ofFn (fun i => (G.ins i).val), List.ofFn (fun i => (G.outs i).val),
    List.ofFn G.etaIn, List.ofFn G.etaOut)

/-- The two-gate library `{U, U†}` of a `k`-qubit matrix: gate `0` is `U`, gate `1` is `U†`.
Liu–Meng, Theorem C.1, p.27 (PDF p.28): "a gadget over {U, U†}". -/
def twoGate (k : ℕ) (hk : 1 ≤ k) (U : Matrix (Qubits k) (Qubits k) ℂ) : Library where
  t := 2
  k _ := k
  one_le_k _ := hk
  U j := if j = 0 then U else U.conjTranspose

end ExactAmpDich.Supplement


