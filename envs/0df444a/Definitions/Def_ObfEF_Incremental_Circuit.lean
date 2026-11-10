-- Prove2me | Definitions.Def_ObfEF_Incremental_Circuit
-- name    : ObfEF_Incremental_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:55:21.580697+00:00
-- url     : https://prove2.me/theorems/f926a51a-bcd2-4817-af2a-b6e936f2b925
-- title:
--   Circuits over {AND, OR, NOT} with constants: evaluation, size, functional equivalence (Definition 2.1)
-- statement:
--   A **circuit** over the basis $B=\{\mathrm{AND},\mathrm{OR},\mathrm{NOT}\}$ with constants (Definition 2.1) is a finite directed acyclic multigraph whose vertices are of two kinds. The **input vertices** $v_1,\dots,v_{il}$ (here indexed by a type $\iota$; for the circuits of the paper $\iota=\{1,\dots,il\}$ in order) have no in-edges. Every **noninput vertex** is labelled either by a constant $0$ or $1$ (no in-edges) or by a gate type of $B$ whose arity equals its number of in-edges, counted with multiplicity, together with an order of these in-edges; so $a\wedge a$ (two parallel edges) is allowed. Finally there are $ol$ ordered **output vertices** $u_1,\dots,u_{ol}$; an output may be an input vertex, and outputs may repeat.
--
--   Given an input $x\in\{0,1\}^{il}$, every vertex receives a value along a topological order, and $C(x)\in\{0,1\}^{ol}$ is the vector of output values. The **size** $|C|$ is the number of noninput vertices, constants included. Two circuits $C_0,C_1$ with the same numbers of inputs and outputs are **functionally equivalent**, $C_0\equiv C_1$, if
--   $$C_0(x)=C_1(x)\qquad\text{for every }x\in\{0,1\}^{il}.$$
--   An edge $a\to b$ means that $a$ is an operand of $b$; $b$ is **reachable** from $a$ if there is a directed path (of length $\ge0$) from $a$ to $b$.
--
--   This is the single circuit model of the paper: the circuits $C_0,C_1$ being compared, and the describing circuits $\Gamma_o$ of incremental changes, are all of this kind.
--
--   **Formalization Note.** `Circuit ι ol` stores the noninput vertices as `0, …, size − 1` in a topological order; vertex `j` has an `Op (ι ⊕ Fin j)`: `const b`, `not a`, `and a b`, `or a b`, whose operands are inputs or vertices numbered below `j`. Every circuit of Definition 2.1 is of this form once a topological order is fixed, and this numbering is used as the circuit's **canonical topological order** (Definitions 2.7 and 3.3). `FunEquiv` is $\equiv$; `Reaches` is reachability.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), pp. 24-25, Definition 2.1 and 'Circuit Topology'

import Mathlib

/-!
# Circuits over B = {AND, OR, NOT} with constants (Definition 2.1)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), pp. 24–25,
Definition 2.1 and "Circuit Topology".

Representation. A circuit `C : Circuit ι ol` has input vertices indexed by `ι` (for the paper's
circuits `ι = Fin il`, the ordered tuple `(v₁, …, v_il)`), `C.size` noninput vertices numbered
`0, …, C.size - 1` in a topological order (this numbering is the circuit's canonical topological
order), and `ol` ordered output vertices. Noninput vertex `j` carries an operation whose operands
are input vertices or noninput vertices with a smaller number: a constant `0`/`1` (indegree 0),
`NOT a`, `a AND b`, `a OR b` (the operand order is the order of the in-edges; `a AND a` is a
double edge). The size `|C|` is the number of noninput vertices, constants included.
-/

namespace ObfEF.Incremental

/-- The label of a noninput vertex: a constant, or a gate type of `B = {AND, OR, NOT}` with its
ordered operands taken from `V`. -/
inductive Op (V : Type) where
  | const (b : Bool)
  | not (a : V)
  | and (a b : V)
  | or (a b : V)
  deriving DecidableEq

/-- Value of an operation when the operands have values `val`. -/
def Op.eval {V : Type} (val : V → Bool) : Op V → Bool
  | .const b => b
  | .not a => !val a
  | .and a b => val a && val b
  | .or a b => val a || val b

/-- The operands of an operation (its in-neighbours, with multiplicity). -/
def Op.args {V : Type} : Op V → List V
  | .const _ => []
  | .not a => [a]
  | .and a b => [a, b]
  | .or a b => [a, b]

/-- A circuit over `B` with constants (Definition 2.1): inputs indexed by `ι`, noninput vertices
`0, …, size - 1` in topological order, vertex `j` reading inputs or vertices `< j`, and `ol`
ordered output vertices (an output may be an input vertex). -/
structure Circuit (ι : Type) (ol : ℕ) where
  /-- `|C|`: the number of noninput vertices (gates and constant vertices). -/
  size : ℕ
  /-- The label and ordered operands of noninput vertex `j`. -/
  op : (j : Fin size) → Op (ι ⊕ Fin j)
  /-- The ordered output vertices `u₁, …, u_ol`. -/
  out : Fin ol → ι ⊕ Fin size

namespace Circuit

variable {ι : Type} {ol : ℕ}

/-- The values of the first `k` noninput vertices on input `x`, computed along the order. -/
def vals (C : Circuit ι ol) (x : ι → Bool) : (k : ℕ) → k ≤ C.size → Fin k → Bool
  | 0, _ => Fin.elim0
  | k + 1, h =>
      Fin.snoc (C.vals x k (Nat.le_of_succ_le h))
        ((C.op ⟨k, h⟩).eval (Sum.elim x (C.vals x k (Nat.le_of_succ_le h))))

/-- The value of a vertex (input or noninput) on input `x`. -/
def value (C : Circuit ι ol) (x : ι → Bool) : ι ⊕ Fin C.size → Bool :=
  Sum.elim x (C.vals x C.size le_rfl)

/-- The output vector `C(x) ∈ {0,1}^ol`. -/
def eval (C : Circuit ι ol) (x : ι → Bool) : Fin ol → Bool :=
  fun k => C.value x (C.out k)

/-- Functional equivalence `C₀ ≡ C₁`: equal outputs on every input. -/
def FunEquiv (C₀ C₁ : Circuit ι ol) : Prop :=
  ∀ x : ι → Bool, C₀.eval x = C₁.eval x

/-- Embed an operand of vertex `j` into the vertex type of the whole circuit. -/
def liftArg (C : Circuit ι ol) (j : Fin C.size) : ι ⊕ Fin j → ι ⊕ Fin C.size :=
  Sum.map id (Fin.castLE (Nat.le_of_lt j.isLt))

/-- An edge `a → b` of the circuit's graph: `b` is a noninput vertex and `a` one of its operands. -/
def Edge (C : Circuit ι ol) (a b : ι ⊕ Fin C.size) : Prop :=
  ∃ j : Fin C.size, b = Sum.inr j ∧ ∃ a' ∈ (C.op j).args, C.liftArg j a' = a

/-- `b` is reachable from `a` (a directed path of length `≥ 0`). -/
def Reaches (C : Circuit ι ol) (a b : ι ⊕ Fin C.size) : Prop :=
  Relation.ReflTransGen C.Edge a b

end Circuit

end ObfEF.Incremental


