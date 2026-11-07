-- Prove2me | Definitions.Def_RegevRecon_Circ
-- name    : RegevRecon_Circ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:07.595969+00:00
-- url     : https://prove2.me/theorems/1cd501a4-7b3a-48ca-84ef-4130752e6409
-- title:
--   Circuit codes over $\{H,T,\mathrm{CNOT}\}$ and the word codes of circuits and instances
-- statement:
--   A **circuit code** is a wire count with a list of gates $H_a$, $T_a$ and $\mathrm{CNOT}_{a,b}$ ($a\ne b$), denoting a circuit over the published gate set `htcxGateSet`. Its **word code** writes the wire count in self-delimiting unary and then each gate as a tag and its wires. The **input word** of an instance writes $n$, $m$, the entries of $B$, the offsets $\tau$ and the binary digits of $\lfloor2^n\beta\rfloor$.
--
--   **Formalization Note** The codes are injective (verification file), so a machine's output names one circuit and its input names one instance up to the $n$ binary places of $\beta$.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), §6, Corollary 3, p.16; Theorem 4, p.21

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace RegevRecon

open QAlgorithms

/-- The unary word `1ᵏ`. -/
def unary (k : ℕ) : List Bool := List.replicate k true

/-- The self-delimiting unary code `1ᵏ 0`. -/
def unaryD (k : ℕ) : List Bool := unary k ++ [false]

/-- A gate of `{H, T, CNOT}` on `N` wires, with a code. -/
inductive GateCode (N : ℕ) where
  /-- The Hadamard gate on wire `a`. -/
  | H (a : Fin N)
  /-- The `T` gate on wire `a`. -/
  | T (a : Fin N)
  /-- `CNOT` with control `a` and target `b ≠ a`. -/
  | CNOT (a b : Fin N) (h : a ≠ b)

/-- A single wire as an embedding. -/
def wire1 {N : ℕ} (a : Fin N) : Fin 1 ↪ Fin N :=
  ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩

/-- An ordered pair of distinct wires as an embedding. -/
def wire2 {N : ℕ} (a b : Fin N) (h : a ≠ b) : Fin 2 ↪ Fin N :=
  ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij h | exact absurd hij.symm h⟩

/-- The gate application of the published gate set `htcxGateSet` that a code denotes. -/
noncomputable def GateCode.toApp {N : ℕ} : GateCode N → GateApp htcxGateSet N
  | .H a => ⟨Gate.ofMatrix1 hadamard, by simp [htcxGateSet], wire1 a⟩
  | .T a => ⟨Gate.ofMatrix1 gateT, by simp [htcxGateSet], wire1 a⟩
  | .CNOT a b h => ⟨Gate.ofMatrix2 cnot, by simp [htcxGateSet], wire2 a b h⟩

/-- A code of a circuit over `{H, T, CNOT}`: its wires and its gates, first gate first. -/
structure Circ where
  /-- The number of wires. -/
  wires : ℕ
  /-- The gates, in order of application. -/
  gates : List (GateCode wires)

/-- The unitary of a circuit code (the published `Circuit.unitary`). -/
noncomputable def Circ.unitary (c : Circ) : Matrix (Qubits c.wires) (Qubits c.wires) ℂ :=
  Circuit.unitary (c.gates.map GateCode.toApp)

/-- The word code of a gate. -/
def GateCode.enc {N : ℕ} : GateCode N → List Bool
  | .H a => unaryD 0 ++ unaryD a
  | .T a => unaryD 1 ++ unaryD a
  | .CNOT a b _ => unaryD 2 ++ unaryD a ++ unaryD b

/-- **The word code of a circuit**: the wire count in self-delimiting unary, then the gates. Injective
(verification file). -/
def encCirc (c : Circ) : List Bool :=
  unaryD c.wires ++ c.gates.flatMap GateCode.enc

/-- The self-delimited binary digits of `⌊2ⁿ β⌋`: the `n` binary places of `β` a generator of size `n`
reads. -/
noncomputable def encBeta (n : ℕ) (β : ℝ) : List Bool :=
  let a := ⌊(2 : ℝ) ^ n * β⌋₊
  unaryD (Nat.bits a).length ++ Nat.bits a

/-- The self-delimiting code of a matrix over `F_p`: its sizes, then its entries row by row. -/
def encMatrix {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p)) : List Bool :=
  unaryD n ++ unaryD m ++
    (List.finRange m).flatMap fun i => (List.finRange n).flatMap fun j =>
      unaryD (B i j).val

/-- The input word of the Gibbs generator: the code of `B`, then `τ`, then the digits of `β`. -/
noncomputable def encInstance {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p))
    (τ : Fin m → ZMod p) (β : ℝ) : List Bool :=
  encMatrix B ++ (List.finRange m).flatMap (fun i => unaryD (τ i).val) ++ encBeta n β

end RegevRecon


