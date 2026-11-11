-- Prove2me | Definitions.Def_CancelFreeHessian_Formula_Circuit
-- name    : CancelFreeHessian_Formula_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:56:11.803438+00:00
-- url     : https://prove2.me/theorems/afcef1fd-312f-44e6-a08b-1697c58ee8a5
-- title:
--   Monotone circuits over the formal local symbols, the local data of an evaluation, and opaque cancellation-free computation of the Hessian diagonal
-- statement:
--   A **monotone circuit** has binary gates $+$ and $\times$, and its leaves are formal variables or nonnegative constants; it computes polynomials with nonnegative coefficients. Here the formal variables are the **local symbols** of the operation gates $v$ of a graph: $\mathrm{val}(v)$, $\varphi_{v,1}$, $\varphi_{v,2}$, $\varphi_{v,11}$, $\varphi_{v,12}$, $\varphi_{v,22}$. At an evaluation (constant values $c$, $C^2$ local functions $\varphi$, a point $x$) these symbols receive the **local data**: the value of $v$ and the local partials of $\varphi_v$ at the values of its two slots. Numerical local partials may be negative; the restriction is on the operations, with no subtraction, no division, no negative constant and no branching. The **size** of a circuit is its number of $+$ and $\times$ gates.
--
--   A circuit $K$ **computes the Hessian diagonal of the graph structure** $D$ (its DAG with slots) **cancellation-free and opaquely** if for each active input $x_i$ it designates one output $o_i$ such that, for every choice of $C^2$ local functions, every constant values and every point $x$,
--   $$o_i\big(\text{local data of the evaluation}\big)=\frac{\partial^2 f}{\partial x_i^2}(x).$$
--   This is Definition 1 of the source, in its opaque form: one circuit per DAG with slots, correct for all local functions and constants.
--
--   **Formalization Note.** A `Circuit` is a straight-line program: `gates`, a list of `add a b` / `mul a b` whose operands are a symbol (`Sym`), a natural-number constant, or an earlier gate (a forward reference reads $0$), and `outs`, a list of pairs `(i, o)`; the output for $x_i$ is the first such pair (`List.lookup`). An output may be a leaf. `size` is the number of gates. Constants are natural numbers, a special case of nonnegative reals. `localData D c φ x` assigns the local data to the symbols of operation gates and $0$ to symbols of other positions. `ComputesHessianDiagonal D K` quantifies over `c`, `φ` with `LocalC2` and `x` after the circuit and the output are fixed.
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 10, §3 Local data and cost, Cancellation-free computation, Definition 1 and opaque methods

import Mathlib
import Definitions.Def_CancelFreeHessian_Formula_Graph

open Classical

namespace CancelFreeHessian.Formula

/-!
# Monotone circuits over the local symbols and the cancellation-free (opaque) model

Tianlang Chen, *The Cancellation-Free Cost of Hessian Diagonals*, §3 "Local data and cost",
"Cancellation-free computation", Definition 1 and the opaque methods (p. 10).

A monotone circuit has binary gates `+` and `×`; its leaves are formal symbols or nonnegative
constants. Here the circuit is a straight-line program: a list of `+`/`×` gates whose operands are
leaves or earlier gates, and a list of designated outputs `(i, o)`, read as "the operand `o`
computes `∂²f/∂x_i²`". The formal symbols are the local data of an operation gate `v` (§3): its
value `val v` and its local partials `φ_{v,1}, φ_{v,2}, φ_{v,11}, φ_{v,12}, φ_{v,22}` at the values
of its slots. Constant leaves are natural numbers (a special case of nonnegative reals).
There is no subtraction, no division, no negative constant and no branching.
-/

/-- The formal symbols of the local data of the operation gate `v`. -/
inductive Sym where
  | val (v : ℕ)
  | d1 (v : ℕ)
  | d2 (v : ℕ)
  | d11 (v : ℕ)
  | d12 (v : ℕ)
  | d22 (v : ℕ)
  deriving DecidableEq

/-- An operand of a circuit gate: a formal symbol, a nonnegative (natural-number) constant, or
the value of the circuit gate at position `j`. -/
inductive Operand where
  | sym (s : Sym)
  | const (c : ℕ)
  | gate (j : ℕ)
  deriving DecidableEq

/-- A gate of a monotone circuit: an addition or a multiplication of two operands. -/
inductive CGate where
  | add (a b : Operand)
  | mul (a b : Operand)
  deriving DecidableEq

/-- A monotone circuit: its gates in order, and its designated outputs `(i, o)`. -/
structure Circuit where
  gates : List CGate
  outs : List (ℕ × Operand)

/-- The size of a circuit: its number of `+` and `×` gates. -/
def Circuit.size (K : Circuit) : ℕ := K.gates.length

/-- The value of an operand when the symbols receive the values `ρ` and the gates computed so far
have the values `prev`. A gate operand not yet computed (a forward reference) reads `0`. -/
noncomputable def Operand.eval (ρ : Sym → ℝ) (prev : List ℝ) : Operand → ℝ
  | .sym s => ρ s
  | .const c => (c : ℝ)
  | .gate j => prev.getD j 0

/-- The value of a circuit gate. -/
noncomputable def CGate.eval (ρ : Sym → ℝ) (prev : List ℝ) : CGate → ℝ
  | .add a b => a.eval ρ prev + b.eval ρ prev
  | .mul a b => a.eval ρ prev * b.eval ρ prev

/-- The values of all gates of the circuit, computed in order. -/
noncomputable def Circuit.values (K : Circuit) (ρ : Sym → ℝ) : List ℝ :=
  K.gates.foldl (fun acc g => acc ++ [g.eval ρ acc]) []

/-- The value of the operand `o` read off the evaluated circuit. -/
noncomputable def Circuit.outValue (K : Circuit) (ρ : Sym → ℝ) (o : Operand) : ℝ :=
  o.eval ρ (K.values ρ)

/-- The local data of an evaluation (§3): at the point `x`, with constant values `c` and local
functions `φ`, the symbol `val v` receives the value of the operation gate `v`, and `d1 v, d2 v,
d11 v, d12 v, d22 v` receive `φ_{v,1}, φ_{v,2}, φ_{v,11}, φ_{v,12}, φ_{v,22}` at the values of its
slots. Symbols of positions that are not operation gates receive `0`. -/
noncomputable def localData {n : ℕ} (D : Dag n) (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ)
    (x : Fin n → ℝ) : Sym → ℝ
  | .val v => if v < D.size ∧ D.IsOp v then D.value c φ x v else 0
  | .d1 v => if v < D.size ∧ D.IsOp v then lp1 (φ v) 0 (D.args c φ x v) else 0
  | .d2 v => if v < D.size ∧ D.IsOp v then lp1 (φ v) 1 (D.args c φ x v) else 0
  | .d11 v => if v < D.size ∧ D.IsOp v then lp2 (φ v) 0 (D.args c φ x v) else 0
  | .d12 v => if v < D.size ∧ D.IsOp v then lp12 (φ v) (D.args c φ x v) else 0
  | .d22 v => if v < D.size ∧ D.IsOp v then lp2 (φ v) 1 (D.args c φ x v) else 0

/-- **Opaque cancellation-free computation of the Hessian diagonal** by the circuit `K` for the
graph structure `D`: for every active input `i` the circuit designates an output operand `o`
for `i` (the first pair `(i, o)` in its output list), and this one operand evaluates to
`∂²f/∂x_i²(x)` for every choice of `C²` local functions `φ`, every constant values `c` and every
point `x`, when the symbols receive the local data of that evaluation. -/
def ComputesHessianDiagonal {n : ℕ} (D : Dag n) (K : Circuit) : Prop :=
  ∀ i : Fin n, D.Active i → ∃ o : Operand, K.outs.lookup i.val = some o ∧
    ∀ (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ), D.LocalC2 φ → ∀ x : Fin n → ℝ,
      K.outValue (localData D c φ x) o = hessDiag (D.fn c φ) i x

end CancelFreeHessian.Formula


