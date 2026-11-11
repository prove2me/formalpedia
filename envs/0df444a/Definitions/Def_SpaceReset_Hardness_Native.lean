-- Prove2me | Definitions.Def_SpaceReset_Hardness_Native
-- name    : SpaceReset_Hardness_Native
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:24.135873+00:00
-- url     : https://prove2.me/theorems/49176741-6a01-48ae-a6ff-c3ead2ff7d10
-- title:
--   Native peak-$P$ circuits with RESET and $D_Z$, and the RESET objective
-- statement:
--   A **peak-$P$ online circuit** has $q=P-1$ private qubit wires and one carrier wire; $P$ counts every device wire. The initial private state $\sigma$ is independent of the input, with $\operatorname{rank}\sigma\le 2^h$ and $0\le h\le q$. At each slot the carrier arrives, a fixed finite list of gates acts on the $P$ wires, and the carrier is returned. The gates are arbitrary unitaries on the $P$ wires, named Clifford gates ($H$, $S$, controlled-$X$, $Y$, $Z$), the native one-qubit **RESET**
--   $$\mathcal R(\rho_{AB})=|0\rangle\langle0|_A\otimes\operatorname{Tr}_A\rho_{AB},$$
--   and, in the enlarged gate set, the nonselective measurement $D_Z(\rho)=(\rho+Z\rho Z)/2$. There are no other partial traces, fresh mixed supplies or measurement records. The count $R$ is the number of RESET gates (gate set *RESET only*), or of RESET and $D_Z$ gates together.
--
--   A **Clifford circuit** is an explicit description: each private wire starts in $|0\rangle$ or in $I/2$, and every gate is a named gate.
--
--   For a specification $G$, a peak $P$ and an initial-rank budget $h$,
--   $$\mathrm{OPT}_{\varepsilon,c,\gamma}(G,P,h)=\min\{R:\ \text{some order }\pi\text{ and some peak-}P\text{ circuit in gate set }\gamma\text{ realize contract }c\text{ for }G^\pi\text{ within }\varepsilon\},$$
--   with value $+\infty$ when no such circuit exists, and $P_{\min}(G,h)$ is the least peak at which some order and some circuit (any number of irreversible gates) exist. An instance $(G,P,h,P_{\min},\pi_0)$ is coded by the matrix, the three numbers and the order.
--
--   **Formalization Note** The wires are $\{0,\dots,q\}$ with wire $0$ the carrier. $\mathrm{OPT}$ and $P_{\min}$ are infima in $\mathbb N\cup\{\infty\}$, so an infeasible instance has value $\infty$, never $0$.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), §2.6, pp. 20–21; §1.5.1, p. 6; §1.5.3 and Theorem 2, p. 7

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Quantum
import Definitions.Def_SpaceReset_Hardness_Coding

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness

/-!
Rinka Miura, STOC 2027 submission #1715 (October 2026), §2.6 (Native reset gates at bounded peak
space), pp. 20–21, the RESET objective of §1.5.3 / Theorem 2 (p. 7), and the Clifford
constructions of Theorems 1, 8 and 10 (pp. 7, 16–17, 21).

A peak-`P` online circuit has `q = P − 1` private qubit wires and one input/output carrier wire;
`P` counts every device wire. Here the wires are `Fin (q+1)`, wire `0` is the carrier and wire
`i.succ` is private wire `i`. The initial private state `σ` on the `q` private wires is
independent of the input. At slot `j` the carrier arrives on wire `0`, a fixed finite list of
gates acts on the `q + 1` wires (first gate first), and the carrier is returned. Gates are
arbitrary unitaries on the `q + 1` wires, the native one-qubit `RESET`
`R(ρ_{AB}) = |0⟩⟨0|_A ⊗ Tr_A ρ_{AB}`, the nonselective `Z` measurement `D_Z(ρ) = (ρ + ZρZ)/2`, and
named Clifford gates. There are no other partial traces, fresh mixed supplies or measurement
records.
-/

open Matrix

/-! ### Gate matrices on a register of `P` qubit wires (basis `Fin P → Bool`) -/

section Gates

variable {P : ℕ}

/-- The basis strings `x, y` agree off wire `w`. -/
def AgreeOff (w : Fin P) (x y : Fin P → Bool) : Prop := ∀ v, v ≠ w → x v = y v

open Classical in
/-- Hadamard on wire `w`. -/
def hadamardMat (w : Fin P) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  fun x y => if AgreeOff w x y then
    (if x w = true ∧ y w = true then -1 else 1) / (Real.sqrt 2 : ℂ) else 0

/-- Phase gate `S = diag(1, i)` on wire `w`. -/
def phaseMat (w : Fin P) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  Matrix.diagonal (fun x => if x w then Complex.I else 1)

/-- Pauli `Z` on wire `w`. -/
def pauliZMat (w : Fin P) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  Matrix.diagonal (fun x => if x w then -1 else 1)

open Classical in
/-- Controlled-`X` with control `a` and target `b` (the identity when `a = b`). -/
def cxMat (a b : Fin P) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  fun x y => if x = (if a ≠ b ∧ y a = true then Function.update y b (!y b) else y) then 1 else 0

open Classical in
/-- Controlled-`Z` with control `a` and target `b` (the identity when `a = b`). -/
def czMat (a b : Fin P) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  Matrix.diagonal (fun x => if a ≠ b ∧ x a = true ∧ x b = true then -1 else 1)

open Classical in
/-- Controlled-`Y` with control `a` and target `b` (`Y|0⟩ = i|1⟩`, `Y|1⟩ = −i|0⟩`; the identity
when `a = b`). -/
def cyMat (a b : Fin P) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  fun x y =>
    if a ≠ b ∧ y a = true then
      (if x = Function.update y b (!y b) then (if y b then -Complex.I else Complex.I) else 0)
    else (if x = y then 1 else 0)

open Classical in
/-- Kraus operator `|0⟩⟨b|` on wire `w` (identity elsewhere). -/
def resetKraus (w : Fin P) (b : Bool) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  fun x y => if x w = false ∧ y w = b ∧ AgreeOff w x y then 1 else 0

/-- The native `RESET` channel on wire `w`: `ρ ↦ |0⟩⟨0|_w ⊗ Tr_w ρ`. -/
def resetChannel (w : Fin P) (ρ : Matrix (Fin P → Bool) (Fin P → Bool) ℂ) :
    Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  ∑ b : Bool, resetKraus w b * ρ * (resetKraus w b)ᴴ

/-- The nonselective `Z` measurement on wire `w`: `ρ ↦ (ρ + Z_w ρ Z_w)/2`. -/
def dzChannel (w : Fin P) (ρ : Matrix (Fin P → Bool) (Fin P → Bool) ℂ) :
    Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  (1 / 2 : ℂ) • (ρ + pauliZMat w * ρ * pauliZMat w)

/-- Conjugation `ρ ↦ U ρ U†`. -/
def conjBy (U ρ : Matrix (Fin P → Bool) (Fin P → Bool) ℂ) : Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  U * ρ * Uᴴ

end Gates

/-- The named (encodable) gates: the Clifford gates `H`, `S`, controlled-`X/Y/Z`, and the two
native irreversible one-qubit channels `RESET` and `D_Z`. -/
inductive CGate (P : ℕ)
  | h (w : Fin P)
  | s (w : Fin P)
  | cx (a b : Fin P)
  | cy (a b : Fin P)
  | cz (a b : Fin P)
  | reset (w : Fin P)
  | dz (w : Fin P)

/-- Native gates: a named gate, or an arbitrary unitary on all `P` wires. -/
inductive Gate (P : ℕ)
  | named (g : CGate P)
  | unitary (U : Matrix.unitaryGroup (Fin P → Bool) ℂ)

/-- The channel of a named gate. -/
def CGate.apply {P : ℕ} : CGate P → Matrix (Fin P → Bool) (Fin P → Bool) ℂ →
    Matrix (Fin P → Bool) (Fin P → Bool) ℂ
  | .h w => conjBy (hadamardMat w)
  | .s w => conjBy (phaseMat w)
  | .cx a b => conjBy (cxMat a b)
  | .cy a b => conjBy (cyMat a b)
  | .cz a b => conjBy (czMat a b)
  | .reset w => resetChannel w
  | .dz w => dzChannel w

/-- The channel of a native gate. -/
def Gate.apply {P : ℕ} : Gate P → Matrix (Fin P → Bool) (Fin P → Bool) ℂ →
    Matrix (Fin P → Bool) (Fin P → Bool) ℂ
  | .named g => g.apply
  | .unitary U => conjBy (U : Matrix (Fin P → Bool) (Fin P → Bool) ℂ)

/-- A gate list applied in order (first gate first). -/
def applyGates {P : ℕ} (gs : List (Gate P)) (ρ : Matrix (Fin P → Bool) (Fin P → Bool) ℂ) :
    Matrix (Fin P → Bool) (Fin P → Bool) ℂ :=
  gs.foldl (fun ρ g => g.apply ρ) ρ

/-- The identification `carrier ⊗ (q private wires) ≅ (q+1 wires)`, carrier = wire `0`. -/
def wireEquiv (q : ℕ) : Bool × (Fin q → Bool) ≃ (Fin (q + 1) → Bool) :=
  Fin.consEquiv (fun _ => Bool)

/-- A peak-`(q+1)` native online circuit with `n` slots (§2.6, p. 21): initial private state
`σ` on the `q` private wires and the slot gate lists. -/
structure NativeCircuit (q n : ℕ) where
  σ : Matrix (Fin q → Bool) (Fin q → Bool) ℂ
  gates : Fin n → List (Gate (q + 1))

/-- The initial private state is a state. -/
def NativeCircuit.Valid {q n : ℕ} (C : NativeCircuit q n) : Prop := IsDensity C.σ

/-- The circuit as an online process with memory = the `q` private wires. -/
def NativeCircuit.toProcess {q n : ℕ} (C : NativeCircuit q n) : Process n where
  M := Fin q → Bool
  σ := C.σ
  Φ := fun j ρ => Matrix.reindex (wireEquiv q).symm (wireEquiv q).symm
    (applyGates (C.gates j) (Matrix.reindex (wireEquiv q) (wireEquiv q) ρ))

/-- Number of `RESET` gates in a gate list. -/
def resetCountList {P : ℕ} : List (Gate P) → ℕ
  | [] => 0
  | .named (.reset _) :: gs => resetCountList gs + 1
  | _ :: gs => resetCountList gs

/-- Number of `D_Z` gates in a gate list. -/
def dzCountList {P : ℕ} : List (Gate P) → ℕ
  | [] => 0
  | .named (.dz _) :: gs => dzCountList gs + 1
  | _ :: gs => dzCountList gs

/-- Total number of `RESET` gates of a circuit. -/
def NativeCircuit.resetCount {q n : ℕ} (C : NativeCircuit q n) : ℕ :=
  ∑ j, resetCountList (C.gates j)

/-- Total number of `D_Z` gates of a circuit. -/
def NativeCircuit.dzCount {q n : ℕ} (C : NativeCircuit q n) : ℕ :=
  ∑ j, dzCountList (C.gates j)

/-- The two native gate sets: unitaries plus `RESET`, or unitaries plus `RESET` and `D_Z`. -/
inductive GateSet
  | resetOnly
  | resetAndDZ
  deriving DecidableEq

/-- The circuit uses only gates of the gate set (no `D_Z` in `resetOnly`). -/
def NativeCircuit.InGateSet {q n : ℕ} (C : NativeCircuit q n) : GateSet → Prop
  | .resetOnly => C.dzCount = 0
  | .resetAndDZ => True

/-- The objective `R`: `RESET` gates (`resetOnly`), or `RESET` and `D_Z` gates together
(`resetAndDZ`). -/
def NativeCircuit.irrevCount {q n : ℕ} (C : NativeCircuit q n) : GateSet → ℕ
  | .resetOnly => C.resetCount
  | .resetAndDZ => C.resetCount + C.dzCount

/-! ### Clifford circuits (encodable descriptions) -/

/-- An explicit Clifford circuit at peak `q + 1`: each private wire starts in `|0⟩`
(`cells i = false`) or maximally mixed `I/2` (`cells i = true`), and every gate is a named gate
(Clifford unitaries `H`, `S`, controlled-`X/Y/Z`, or `RESET`/`D_Z`). -/
structure CliffordCircuit (q n : ℕ) where
  cells : Fin q → Bool
  gates : Fin n → List (CGate (q + 1))

/-- The product initial state `⊗ᵢ (cellᵢ)` with `cellᵢ ∈ {|0⟩⟨0|, I/2}`. -/
def cellState {q : ℕ} (cells : Fin q → Bool) : Matrix (Fin q → Bool) (Fin q → Bool) ℂ :=
  Matrix.diagonal (fun x => ∏ i, (if cells i then (1 / 2 : ℂ) else if x i then 0 else 1))

/-- The native circuit described by a Clifford circuit. -/
def CliffordCircuit.toNative {q n : ℕ} (C : CliffordCircuit q n) : NativeCircuit q n where
  σ := cellState C.cells
  gates := fun j => (C.gates j).map Gate.named

/-- A named gate is a carrier-controlled Pauli: controlled-`X`, `Y` or `Z` with the carrier
(wire `0`) as control and another wire as target. -/
def CGate.IsCarrierPauli {P : ℕ} : CGate P → Prop
  | .cx a b => a.val = 0 ∧ b.val ≠ 0
  | .cy a b => a.val = 0 ∧ b.val ≠ 0
  | .cz a b => a.val = 0 ∧ b.val ≠ 0
  | _ => False

open Classical in
/-- Number of carrier-controlled Pauli gates of a Clifford circuit. -/
def CliffordCircuit.carrierPauliCount {q n : ℕ} (C : CliffordCircuit q n) : ℕ :=
  ∑ j, ((C.gates j).filter (fun g => decide g.IsCarrierPauli)).length

/-- Number of Hadamard gates of a Clifford circuit. -/
def CliffordCircuit.hadamardCount {q n : ℕ} (C : CliffordCircuit q n) : ℕ :=
  ∑ j, ((C.gates j).filter (fun g => match g with | .h _ => true | _ => false)).length

/-- Binary layout of a named gate. -/
def CGate.nats {P : ℕ} : CGate P → List ℕ
  | .h w => [0, w.val]
  | .s w => [1, w.val]
  | .cx a b => [2, a.val, b.val]
  | .cy a b => [3, a.val, b.val]
  | .cz a b => [4, a.val, b.val]
  | .reset w => [5, w.val]
  | .dz w => [6, w.val]

/-- Binary layout of a Clifford circuit: `q`, `n`, the cell bits, then for each slot the number
of gates followed by the gates. -/
def CliffordCircuit.nats {q n : ℕ} (C : CliffordCircuit q n) : List ℕ :=
  [q, n] ++ (List.finRange q).map (fun i => if C.cells i then 1 else 0) ++
    (List.finRange n).flatMap (fun j => [(C.gates j).length] ++ (C.gates j).flatMap CGate.nats)

/-- The binary code of a Clifford circuit. -/
def CliffordCircuit.encode {q n : ℕ} (C : CliffordCircuit q n) : List Bool :=
  encNats C.nats

/-! ### The RESET-minimization objective (§1.5.3, p. 7; §2.6, p. 21) -/

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- A peak-`P` native realization of contract `c` for `G^π` within error `ε`, in gate set `γ`,
with initial-rank budget `h` (`0 ≤ h ≤ q = P − 1`) and at most `R` irreversible gates. -/
def FeasibleAt (ε : ℝ) (c : Contract) (γ : GateSet) {n : ℕ} (G : Matrix κ (Fin n) F2)
    (π : Equiv.Perm (Fin n)) (P h R : ℕ) : Prop :=
  1 ≤ P ∧ h ≤ P - 1 ∧
    ∃ C : NativeCircuit (P - 1) n, C.Valid ∧ C.σ.rank ≤ 2 ^ h ∧ C.InGateSet γ ∧
      C.irrevCount γ ≤ R ∧ ErrorLE (reorder G π) c C.toProcess ε

/-- `OPT_{ε,c,γ}(G,P,h)`: the minimum irreversible-gate count over all output orders and all
peak-`P` native circuits with initial rank at most `2^h` realizing contract `c` within `ε`;
`⊤ = +∞` when there is none. -/
def OPT (ε : ℝ) (c : Contract) (γ : GateSet) {n : ℕ} (G : Matrix κ (Fin n) F2) (P h : ℕ) : ℕ∞ :=
  ⨅ (π : Equiv.Perm (Fin n)) (R : ℕ) (_ : FeasibleAt ε c γ G π P h R), (R : ℕ∞)

/-- `P_min`: the least peak `P` at which some order and some native circuit (any number of
irreversible gates) realizes contract `c` within `ε` with initial-rank budget `h`; `⊤` if none. -/
def PMin (ε : ℝ) (c : Contract) (γ : GateSet) {n : ℕ} (G : Matrix κ (Fin n) F2) (h : ℕ) : ℕ∞ :=
  ⨅ (P : ℕ) (_ : ∃ (π : Equiv.Perm (Fin n)) (R : ℕ), FeasibleAt ε c γ G π P h R), (P : ℕ∞)

/-- The binary code of a RESET-minimization instance `(G, P, h, P_min, π₀)`. -/
def instanceCode {k n : ℕ} (G : Matrix (Fin k) (Fin n) F2) (P h Pmin : ℕ)
    (π₀ : Equiv.Perm (Fin n)) : List Bool :=
  encNats (specNats G ++ [P, h, Pmin] ++ permNats π₀)

end SpaceReset.Hardness


