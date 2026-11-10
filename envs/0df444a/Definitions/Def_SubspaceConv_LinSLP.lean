-- Prove2me | Definitions.Def_SubspaceConv_LinSLP
-- name    : SubspaceConv_LinSLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:18.16174+00:00
-- url     : https://prove2.me/theorems/14f4be8e-c720-4ea8-afe8-c1b982646a33
-- title:
--   Ring-uniform linear straight-line programs and their operation count
-- statement:
--   The cost model of Theorem 1. A **linear straight-line program** with input index set $\iota$ and output index set $\kappa$ is a finite list of gates, evaluated in order; gate number $k$ writes register $k$. A gate is one of
--
--   1. $\mathrm{input}(i)$: the input entry $f(i)$, $i\in\iota$;
--   2. $\mathrm{zero}$: the constant $0$;
--   3. $\mathrm{add}(a,b)$ and $\mathrm{sub}(a,b)$: the sum or difference of two earlier registers;
--   4. $\mathrm{zmul}(z,a)$: an integer $z\in\mathbb Z$ times an earlier register;
--   5. $\mathrm{invp}(a)$: an earlier register times $p^{-1}$, where $p=\operatorname{char}\mathbb F_q$.
--
--   Each output $o\in\kappa$ names the register holding it. The program is evaluated over any commutative ring $A$, given an element $p^{-1}\in A$ (the theorems assume $p\cdot p^{-1}=1$); a single program is therefore valid over every such ring at once. A program is **well formed** if every operand is an earlier register and every output is a register. Its **cost** is the number of $\mathrm{add}$, $\mathrm{sub}$, $\mathrm{zmul}$ and $\mathrm{invp}$ gates; reading an input and the constant $0$ are free.
--
--   Every such program computes a linear map $A^\iota\to A^\kappa$ with coefficients in $\mathbb Z[1/p]$. This is the circuit model in which §3.3 transposes the zeta-transform circuit (gates $z=x+y$, $z=cx$), and §3.4's remark that "all divisions are by powers of $p$" is why $\mathrm{invp}$ is the only non-integer constant.
--
--   **Formalization Note** Registers are a Lean `List`; reads out of range return $0$, which never happens in a well-formed program.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2, p.10–11 ("We count ring additions, subtractions, and multiplications"); §3.3, p.13 (linear circuit, transposition); §3.4, p.13 (divisions by powers of p)

import Mathlib

namespace SubspaceConv

/-!
# Ring-uniform linear straight-line programs

The model of "arithmetic operations" in Theorem 1 of Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), p.2 (PDF p.3), with the
count of §2 ("We count ring additions, subtractions, and multiplications", p.11) and the linear-circuit
view of the transposition step (§3.3, p.13: gates `z = x + y`, `z = cx`).

**Formalization Note** A program is a list of gates evaluated in order; gate `k` produces
register `k`. Gates: `input i` (the input entry `i`), `zero` (the constant 0), `add a b`,
`sub a b` (sum or difference of earlier registers `a, b`), `zmul z a` (an integer `z` times
register `a`) and `invp a` (register `a` times `p⁻¹`, where `p` is the characteristic of
`F_q`). Reading an input and the zero constant are free; every `add`, `sub`, `zmul` and
`invp` gate costs one operation, whatever its integer. There is no general multiplication and
no free constant other than 0, so every program computes a linear map. One program is evaluated
over every commutative ring `A` given an element `pinv : A` (the theorems require
`p · pinv = 1`); it is therefore ring-uniform. `WellFormed` requires every operand to be an
earlier register and every output to be a register, so the default value `0` of an
out-of-range read never occurs in a well-formed program.
-/

/-- A gate of a linear straight-line program with inputs indexed by `ι`. -/
inductive Gate (ι : Type*) where
  | input (i : ι)
  | zero
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | zmul (z : ℤ) (a : ℕ)
  | invp (a : ℕ)

/-- A linear straight-line program with inputs `ι` and outputs `κ`: a list of gates and,
for each output, the register holding it. -/
structure LinSLP (ι κ : Type*) where
  gates : List (Gate ι)
  out : κ → ℕ

namespace Gate

variable {ι : Type*}

/-- Every operand of the gate is a register below `k`. -/
def RefsBelow : Gate ι → ℕ → Prop
  | input _, _ => True
  | zero, _ => True
  | add a b, k => a < k ∧ b < k
  | sub a b, k => a < k ∧ b < k
  | zmul _ a, k => a < k
  | invp a, k => a < k

/-- The gate is an arithmetic operation (it is counted in the cost). -/
def IsOp : Gate ι → Bool
  | input _ => false
  | zero => false
  | _ => true

/-- The value of the gate given the earlier registers `vals`. -/
def value {A : Type*} [CommRing A] (pinv : A) (inp : ι → A) (vals : List A) : Gate ι → A
  | input i => inp i
  | zero => 0
  | add a b => vals.getD a 0 + vals.getD b 0
  | sub a b => vals.getD a 0 - vals.getD b 0
  | zmul z a => (z : A) * vals.getD a 0
  | invp a => vals.getD a 0 * pinv

end Gate

namespace LinSLP

variable {ι κ : Type*}

/-- The registers after evaluating the gates in order, starting from the registers `vals`. -/
def evalGates {A : Type*} [CommRing A] (pinv : A) (inp : ι → A) :
    List (Gate ι) → List A → List A
  | [], vals => vals
  | g :: gs, vals => evalGates pinv inp gs (vals ++ [g.value pinv inp vals])

/-- The outputs of the program on the input table `inp`, with `pinv` used as `p⁻¹`. -/
def eval {A : Type*} [CommRing A] (P : LinSLP ι κ) (pinv : A) (inp : ι → A) (o : κ) : A :=
  (evalGates pinv inp P.gates []).getD (P.out o) 0

/-- Operands refer to earlier registers and outputs to registers. -/
def WellFormed (P : LinSLP ι κ) : Prop :=
  (∀ (k : ℕ) (h : k < P.gates.length), P.gates[k].RefsBelow k) ∧ ∀ o, P.out o < P.gates.length

/-- The number of arithmetic operations: the gates `add`, `sub`, `zmul`, `invp`. -/
def cost (P : LinSLP ι κ) : ℕ :=
  P.gates.countP Gate.IsOp

end LinSLP

end SubspaceConv


