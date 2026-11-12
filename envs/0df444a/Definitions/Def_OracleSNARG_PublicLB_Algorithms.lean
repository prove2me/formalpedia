-- Prove2me | Definitions.Def_OracleSNARG_PublicLB_Algorithms
-- name    : OracleSNARG_PublicLB_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:45:42.965624+00:00
-- url     : https://prove2.me/theorems/faba9a9a-a476-4b92-bbff-23a88499f266
-- title:
--   Polynomial-size randomized oracle circuits (non-uniform) and query-bounded deterministic oracle procedures
-- statement:
--   **Randomized oracle circuits.** A circuit has a number `coins` of random coins, a straight-line list of gates and a list of outputs. Its inputs are a list of bit strings. Each gate computes one wire, numbered by its position; it may read only earlier wires (any other reference reads $0$). The gates are: a constant; bit $j$ of input $k$ ($0$ out of range); "input $k$ has more than $j$ bits"; coin $j$; NOT, AND, OR of earlier wires; and an **oracle gate**, which returns $O(u)$ where $u$ is the bit string carried by a list of earlier wires. Each output is a list of pairs (validity wire, bit wire): the output string is the sequence of bit wires whose validity wire is $1$, so output lengths may vary.
--
--   The **size** of a circuit is
--   $$\text{coins}+\sum_{\text{gates}}(1+\text{fan-in of oracle gates})+\text{number of output entries}.$$
--   With coins $r\in\{0,1\}^{\text{coins}}$ the circuit computes its outputs deterministically; $A^O(\mathrm{inp})$ denotes the output distribution when $r$ is uniform.
--
--   A **polynomial-size randomized oracle algorithm** is a non-uniform family $\lambda\mapsto A_\lambda$ of such circuits with $\mathrm{size}(A_\lambda)\le p(\lambda)$ for one polynomial $p$ and every $\lambda$. Advice and fixed coins can be hardwired as constants, and an oracle gate can be replaced by a constant, at no cost in size.
--
--   **Deterministic oracle procedures.** A deterministic oracle procedure is a decision tree. Each node either returns a value, or asks a query $u\in\{0,1\}^*$ and continues according to the answer bit, so queries may be adaptive. It does no counting of work between queries. Its **depth** is the maximal number of queries along a branch. A procedure of depth $\le\ell$ makes at most $\ell$ oracle queries against every oracle. We write $T.\mathrm{eval}(O)$ for its result against $O$ and $T.\mathrm{queries}(O)$ for the list of its queries against $O$.
--
--   **Formalization Note.** Circuits are the standard non-uniform model for the paper's "polynomial-size (oracle) adversary". Variable-length inputs are read through the length-probe gates.
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), p. 17, Definition 17 ('polynomial-size oracle adversary', 'polynomial-size oracle algorithm'); p. 13, Definition 9 ('poly-size adversary')

import Mathlib
import Definitions.Def_OracleSNARG_PublicLB_Majority

set_option autoImplicit false

namespace OracleSNARG.PublicLB

/-- **A gate of a randomized Boolean circuit with oracle gates.** Wires are numbered by the
position of the gate computing them; a gate may read only wires computed before it (a reference to
any other wire reads `false`).
* `const b`: the constant `b`;
* `input k j`: bit `j` of the `k`-th input string (`false` when out of range);
* `inputLen k j`: whether the `k`-th input string has more than `j` bits;
* `coin j`: the `j`-th random coin (`false` when `j` is not below the circuit's number of coins);
* `not`, `and`, `or`: Boolean gates on earlier wires;
* `oracle q`: an oracle gate, answering `O(u)` where `u` is the bit string carried by the
  wires `q`. -/
inductive Gate : Type where
  | const (b : Bool)
  | input (k j : ℕ)
  | inputLen (k j : ℕ)
  | coin (j : ℕ)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
  | oracle (q : List ℕ)

/-- **A randomized oracle circuit** with several string inputs and several string outputs.
`coins` is the number of random coins; `gates` is the straight-line list of gates; output `k` is
the list `outputs[k]` of pairs `(v, b)`: the output string consists of the bits on the wires `b`
whose validity wire `v` carries `1`, in order (so output lengths may vary). -/
structure RCircuit : Type where
  coins : ℕ
  gates : List Gate
  outputs : List (List (ℕ × ℕ))

/-- Size contribution of one gate: `1`, plus the fan-in for an oracle gate. -/
def Gate.weight : Gate → ℕ
  | .oracle q => q.length + 1
  | _ => 1

/-- **Size** of a circuit: number of coins + gates (oracle gates weighted by fan-in) + output
entries. -/
def RCircuit.size (A : RCircuit) : ℕ :=
  A.coins + (A.gates.map Gate.weight).sum + (A.outputs.map List.length).sum

/-- Value of a gate given the oracle, the inputs, the coins and the earlier wire values. -/
def Gate.eval (O : Oracle) (inp : List (List Bool)) (r : ℕ → Bool) (vals : List Bool) :
    Gate → Bool
  | .const b => b
  | .input k j => (inp.getD k []).getD j false
  | .inputLen k j => decide (j < (inp.getD k []).length)
  | .coin j => r j
  | .not a => !(vals.getD a false)
  | .and a b => vals.getD a false && vals.getD b false
  | .or a b => vals.getD a false || vals.getD b false
  | .oracle q => O (q.map fun a => vals.getD a false)

/-- Evaluate a gate list left to right, appending each gate's value to the wire values. -/
def evalGates (O : Oracle) (inp : List (List Bool)) (r : ℕ → Bool) :
    List Gate → List Bool → List Bool
  | [], vals => vals
  | g :: gs, vals => evalGates O inp r gs (vals ++ [g.eval O inp r vals])

/-- **Deterministic evaluation** of `A` with oracle `O`, inputs `inp` and coin vector `r`: the list
of output strings. -/
def RCircuit.eval (A : RCircuit) (O : Oracle) (inp : List (List Bool))
    (r : Fin A.coins → Bool) : List (List Bool) :=
  let coin : ℕ → Bool := fun j => if h : j < A.coins then r ⟨j, h⟩ else false
  let vals := evalGates O inp coin A.gates []
  A.outputs.map fun out =>
    out.filterMap fun p => if vals.getD p.1 false then some (vals.getD p.2 false) else none

/-- **Output distribution** `A^O(inp)`: the coins are uniform on `{0,1}^{coins}`. -/
noncomputable def RCircuit.run (A : RCircuit) (O : Oracle) (inp : List (List Bool)) :
    PMF (List (List Bool)) :=
  (PMF.uniformOfFintype (Fin A.coins → Bool)).map fun r => A.eval O inp r

/-- **Polynomial-size randomized oracle algorithm** (non-uniform): a family `λ ↦ A λ` of
randomized oracle circuits whose size is at most `p(λ)` for one polynomial `p` and every `λ`. -/
def IsPolySize (A : ℕ → RCircuit) : Prop :=
  ∃ p : Polynomial ℕ, ∀ lam : ℕ, (A lam).size ≤ p.eval lam

/-- **Deterministic oracle procedure** (oracle decision tree): either it stops with a value, or it
asks the oracle a query `u` and continues according to the answer bit. Queries may be adaptive.
No bound on the work between queries. -/
inductive QTree (α : Type) : Type where
  | leaf : α → QTree α
  | query : List Bool → (Bool → QTree α) → QTree α

namespace QTree

variable {α : Type}

/-- Running the procedure against oracle `O`. -/
def eval : QTree α → Oracle → α
  | leaf a, _ => a
  | query u k, O => eval (k (O u)) O

/-- Maximal number of oracle queries along any branch (the query bound for every oracle). -/
def depth : QTree α → ℕ
  | leaf _ => 0
  | query _ k => max (depth (k false)) (depth (k true)) + 1

/-- The queries asked, in order, when running against oracle `O`. -/
def queries : QTree α → Oracle → List (List Bool)
  | leaf _, _ => []
  | query u k, O => u :: queries (k (O u)) O

end QTree

end OracleSNARG.PublicLB


