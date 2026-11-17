-- Prove2me | Definitions.Def_SubspaceConv_Supplement_ArithSLP
-- name    : SubspaceConv_Supplement_ArithSLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:45:41.87887+00:00
-- url     : https://prove2.me/theorems/52fdd714-4a8e-4790-b105-2f863a43e58c
-- title:
--   Ring-uniform arithmetic straight-line programs
-- statement:
--   An **arithmetic straight-line program** with inputs indexed by $\iota$ and outputs indexed by $\kappa$ is a list of gates evaluated in order, gate $k$ producing register $k$, together with an output register for each $o \in \kappa$. The gates are: read input $i$; the constants $0$ and $1$; $x_a + x_b$, $x_a - x_b$ and $x_a \cdot x_b$ for earlier registers $a, b$; $z \cdot x_a$ for an integer $z$; and $x_a \cdot p^{-1}$, where $p$ is the characteristic of $\mathbb F_q$. Reading inputs and the constants $0, 1$ are free; each of the other five gates costs one **arithmetic operation**. One program is evaluated over every commutative ring $A$, given an element $p^{-1} \in A$.
--
--   A program is **well formed** if every operand is an earlier register and every output is a register. The predicate **NoZmul** says that no integer-scaling gate occurs.
--
--   This is the cost model of "arithmetic operations in $R$" for the bilinear kernel product of Theorem 3 and of "arithmetic operations over $\mathbb Q$" for the exact-span counts of Theorem 5.
--
--   **Formalization Note** It extends the published linear model `SubspaceConv.LinSLP` of Theorem 1 by the free constant $1$ and the multiplication gate. Without the NoZmul restriction, a program whose wiring may depend on the data could write every integer output with one scaling gate.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), §2, p.11 (PDF p.12) ("We count ring additions, subtractions, and multiplications"); Theorems 3 and 5, p.3 and p.14–15

import Mathlib

set_option autoImplicit false

namespace SubspaceConv.Supplement

/-!
# Ring-uniform arithmetic straight-line programs

The model of "arithmetic operations" of Theorems 3 and 5 of Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2) (p.3, PDF p.4; p.14–15,
PDF p.15–16), with the count of §2 ("We count ring additions, subtractions, and
multiplications", p.11, PDF p.12).

**Formalization Note** This follows the published `SubspaceConv.LinSLP` gate for gate and adds
two gates: `one` (the constant 1) and `mul a b` (the product of two earlier registers). Gates:
`input i`, `zero`, `one` (free), `add a b`, `sub a b`, `mul a b`, `zmul z a` (integer `z` times a
register) and `invp a` (a register times `p⁻¹`), each of the last five costing one operation
whatever its integer. The only free constants are `0` and `1`. One program is evaluated over every
commutative ring `A` given an element `pinv : A` (the theorems require `p · pinv = 1`).
`WellFormed` requires every operand to be an earlier register and every output to be a register,
so the default value `0` of an out-of-range read never occurs. `NoZmul` says no `zmul` gate
occurs (used by Theorem 5, where integer scalings would make every count a single gate).
-/

/-- A gate of an arithmetic straight-line program with inputs indexed by `ι`. -/
inductive AGate (ι : Type*) where
  | input (i : ι)
  | zero
  | one
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | mul (a b : ℕ)
  | zmul (z : ℤ) (a : ℕ)
  | invp (a : ℕ)

/-- An arithmetic straight-line program with inputs `ι` and outputs `κ`: a list of gates and,
for each output, the register holding it. -/
structure ArithSLP (ι κ : Type*) where
  gates : List (AGate ι)
  out : κ → ℕ

namespace AGate

variable {ι : Type*}

/-- Every operand of the gate is a register below `k`. -/
def RefsBelow : AGate ι → ℕ → Prop
  | input _, _ => True
  | zero, _ => True
  | one, _ => True
  | add a b, k => a < k ∧ b < k
  | sub a b, k => a < k ∧ b < k
  | mul a b, k => a < k ∧ b < k
  | zmul _ a, k => a < k
  | invp a, k => a < k

/-- The gate is an arithmetic operation (it is counted in the cost). -/
def IsOp : AGate ι → Bool
  | input _ => false
  | zero => false
  | one => false
  | _ => true

/-- The gate is an integer scaling `zmul`. -/
def IsZmul : AGate ι → Bool
  | zmul _ _ => true
  | _ => false

/-- The value of the gate given the earlier registers `vals`. -/
def value {A : Type*} [CommRing A] (pinv : A) (inp : ι → A) (vals : List A) : AGate ι → A
  | input i => inp i
  | zero => 0
  | one => 1
  | add a b => vals.getD a 0 + vals.getD b 0
  | sub a b => vals.getD a 0 - vals.getD b 0
  | mul a b => vals.getD a 0 * vals.getD b 0
  | zmul z a => (z : A) * vals.getD a 0
  | invp a => vals.getD a 0 * pinv

end AGate

namespace ArithSLP

variable {ι κ : Type*}

/-- The registers after evaluating the gates in order, starting from the registers `vals`. -/
def evalGates {A : Type*} [CommRing A] (pinv : A) (inp : ι → A) :
    List (AGate ι) → List A → List A
  | [], vals => vals
  | g :: gs, vals => evalGates pinv inp gs (vals ++ [g.value pinv inp vals])

/-- The outputs of the program on the input table `inp`, with `pinv` used as `p⁻¹`. -/
def eval {A : Type*} [CommRing A] (P : ArithSLP ι κ) (pinv : A) (inp : ι → A) (o : κ) : A :=
  (evalGates pinv inp P.gates []).getD (P.out o) 0

/-- Operands refer to earlier registers and outputs to registers. -/
def WellFormed (P : ArithSLP ι κ) : Prop :=
  (∀ (k : ℕ) (h : k < P.gates.length), P.gates[k].RefsBelow k) ∧ ∀ o, P.out o < P.gates.length

/-- The number of arithmetic operations: the gates `add`, `sub`, `mul`, `zmul`, `invp`. -/
def cost (P : ArithSLP ι κ) : ℕ :=
  P.gates.countP AGate.IsOp

/-- No integer-scaling gate `zmul` occurs in the program. -/
def NoZmul (P : ArithSLP ι κ) : Prop :=
  ∀ g ∈ P.gates, g.IsZmul = false

end ArithSLP

end SubspaceConv.Supplement


