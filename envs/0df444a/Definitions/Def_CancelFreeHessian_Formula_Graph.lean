-- Prove2me | Definitions.Def_CancelFreeHessian_Formula_Graph
-- name    : CancelFreeHessian_Formula_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:54:55.552547+00:00
-- url     : https://prove2.me/theorems/01ddd5d6-fc07-46ec-9c2f-7df74eac600b
-- title:
--   Computation graphs with ordered slots and C² local functions, scalar formulas, active inputs, the computed function f and its Hessian diagonal
-- statement:
--   A **computation graph** with $n$ inputs is a directed acyclic graph whose sources are **input gates** $x_1,\dots,x_n$ and **constant gates**. Every other gate $v$ is an **operation gate** with two ordered input slots (slot 1 and slot 2) and a **local function** $\varphi_v\in C^2(\mathbb R^2)$. A slot holds one gate, and one gate may fill both slots of a consumer. The **out-degree** of a gate is the number of slots it fills. A **scalar** graph has one output gate, and every gate lies in the cone of the output (has a path to it). The **size** $s$ is the number of gates (input, constant and operation gates). An input $x_i$ is **active** if its gate fills a slot. An operation gate is **reused** if its out-degree is at least $2$; the graph is a **formula** if no operation gate is reused. Input and constant gates may fill any number of slots, so a variable may occur at any number of leaves.
--
--   At a point $x\in\mathbb R^n$, with a real value $c_k$ for each constant gate $k$, the value of a gate is $x_i$ at the input gate of $x_i$, $c_k$ at the constant gate $k$, and
--   $$\mathrm{value}(v)=\varphi_v\big(\mathrm{value}(p),\mathrm{value}(q)\big)$$
--   at an operation gate $v$ whose slots hold $p$ and $q$. The function $f:\mathbb R^n\to\mathbb R$ computed by the graph is the value of the output gate, and the **Hessian diagonal** entry $\partial^2 f/\partial x_i^2(x)$ is its genuine second partial derivative. The local partials of $\varphi_v$ at a point $z=(z_1,z_2)$ are $\varphi_{v,1},\varphi_{v,2}$ (first partials in the two arguments), $\varphi_{v,11},\varphi_{v,22}$ (pure second partials) and $\varphi_{v,12}$ (the mixed partial).
--
--   These objects are the setting of every statement of the mission.
--
--   **Formalization Note.** The DAG with slots is the record `Dag n`: `size` gates at positions $0,\dots,s-1$ numbered in a topological order (every finite DAG has one), `gate k` the kind of gate $k$ (`input i`, `const`, or `op p q` with slot 1 holding $p$ and slot 2 holding $q$; `WellFormed` requires $p,q<k$), and the output position `out`. Slots are indexed by `κ : Fin 2` ($\kappa=0$ is slot 1). `IsScalarFormula` bundles `WellFormed`, one input gate per variable (`InputsDistinct`), every gate in the cone of the output (`InCone`) and out-degree at most $1$ for operation gates (`IsFormula`). The numerical parameters are separate: local functions `φ : ℕ → ℝ × ℝ → ℝ` (with `LocalC2`: `ContDiff ℝ 2` on all of $\mathbb R^2$ for every operation gate) and constant values `c : ℕ → ℝ`. `pd G j z` is the derivative of $u\mapsto G(z \text{ with } z_j:=u)$ at $z_j$, and `hessDiag f i x = pd (pd f i) i x`. `lp1 φ κ`, `lp2 φ κ` and `lp12 φ` are the local partials ($\varphi_{,12}=\partial_2\partial_1\varphi$).
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 10, §3 Computation graphs; p. 2, §1.1

import Mathlib

open Classical

namespace CancelFreeHessian.Formula

/-!
# Computation graphs, scalar formulas and the Hessian diagonal

Tianlang Chen, *The Cancellation-Free Cost of Hessian Diagonals*, §3 "Computation graphs"
(p. 10) and §1.1 (p. 2).

A computation graph is a DAG whose sources are input gates `x_i` and constant gates; every other
gate is an operation gate with two ordered input slots (slot 1, slot 2, here `0, 1 : Fin 2`) and a
local function `φ_v ∈ C²(ℝ²)`. A slot holds one gate, and one gate may fill both slots of a
consumer.

**Encoding.** The gates of a graph are numbered `0, …, size − 1` in a topological order (every
finite DAG has one): an operation gate `op p q` at position `k` has its slots filled by the gates
`p` and `q` with `p, q < k` (`WellFormed`). The values of `gate` at positions `≥ size` are never
read. The *structure* (DAG with slots) is the record `Dag n`; the numerical parameters are kept
apart: the local functions `φ : ℕ → ℝ × ℝ → ℝ` and the constant values `c : ℕ → ℝ` (`c k` is the
value of the constant gate `k`).
-/

/-- A gate of a computation graph with `n` input variables: the input gate of the variable `x_i`,
a constant gate, or an operation gate whose slot 1 holds gate `p` and slot 2 holds gate `q`. -/
inductive Gate (n : ℕ) where
  | input (i : Fin n)
  | const
  | op (p q : ℕ)
  deriving DecidableEq

/-- The DAG with slots of a scalar computation graph: `size` gates at positions
`0, …, size − 1`, the kind and slots of each gate, and the position `out` of the one output
gate. -/
structure Dag (n : ℕ) where
  size : ℕ
  gate : ℕ → Gate n
  out : ℕ

namespace Dag

variable {n : ℕ} (D : Dag n)

/-- Gate `k` is an operation gate. -/
def IsOp (k : ℕ) : Prop := ∃ p q, D.gate k = .op p q

/-- The gate filling slot `κ` of gate `k` (slot 1 is `κ = 0`, slot 2 is `κ = 1`); only read when
gate `k` is an operation gate. -/
def slot (k : ℕ) (κ : Fin 2) : ℕ :=
  match D.gate k with
  | .op p q => if κ = 0 then p else q
  | _ => 0

/-- The numbering is topological: the output is a gate of the graph, and every operation gate
reads only earlier gates. -/
def WellFormed : Prop :=
  D.out < D.size ∧ ∀ k < D.size, ∀ p q : ℕ, D.gate k = .op p q → p < k ∧ q < k

/-- Each variable `x_i` has at most one input gate. -/
def InputsDistinct : Prop :=
  ∀ j < D.size, ∀ k < D.size, ∀ i : Fin n, D.gate j = .input i → D.gate k = .input i → j = k

/-- Gate `k` fills a slot of the operation gate `j`. -/
def Feeds (k j : ℕ) : Prop := j < D.size ∧ D.IsOp j ∧ ∃ κ : Fin 2, D.slot j κ = k

/-- Every gate lies in the cone of the output: it has a path to the output gate (§3: gates with
no path to an output are deleted at the start). -/
def InCone : Prop := ∀ k < D.size, Relation.ReflTransGen D.Feeds k D.out

/-- The out-degree of gate `k`: the number of slots it fills (both slots of one consumer count
twice). -/
noncomputable def outDeg (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range D.size, ∑ κ : Fin 2, if D.IsOp j ∧ D.slot j κ = k then 1 else 0

/-- The graph is a formula: no operation gate is reused, i.e. every operation gate has
out-degree at most 1 (`k = 0` in §3). Input and constant gates may fill any number of slots. -/
def IsFormula : Prop := ∀ k < D.size, D.IsOp k → D.outDeg k ≤ 1

/-- A scalar formula: a well-formed graph, one input gate per variable, every gate in the cone of
the output, and no reused operation gate. -/
def IsScalarFormula : Prop := D.WellFormed ∧ D.InputsDistinct ∧ D.InCone ∧ D.IsFormula

/-- The input `x_i` is active: its gate fills at least one slot. -/
def Active (i : Fin n) : Prop :=
  ∃ j < D.size, D.IsOp j ∧ ∃ κ : Fin 2, D.gate (D.slot j κ) = .input i

/-- Every local function of an operation gate is `C²` on all of `ℝ²`. -/
def LocalC2 (φ : ℕ → ℝ × ℝ → ℝ) : Prop :=
  ∀ k < D.size, D.IsOp k → ContDiff ℝ 2 (φ k)

/-- The value of gate `k` at the point `x ∈ ℝⁿ`: `x_i` at the input gate of `x_i`, `c k` at a
constant gate, and `φ_k(value p, value q)` at an operation gate with slots `(p, q)`. (A slot
pointing forward, excluded by `WellFormed`, gives `0`.) -/
noncomputable def value (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  match D.gate k with
  | .input i => x i
  | .const => c k
  | .op p q =>
    if _h : p < k ∧ q < k then φ k (value c φ x p, value c φ x q) else 0
termination_by k
decreasing_by all_goals omega

/-- The function `f : ℝⁿ → ℝ` computed by the graph: the value of the output gate. -/
noncomputable def fn (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => D.value c φ x D.out

/-- The point `(value p, value q)` at which the local function of the operation gate `k` with
slots `(p, q)` is evaluated. -/
noncomputable def args (c : ℕ → ℝ) (φ : ℕ → ℝ × ℝ → ℝ) (x : Fin n → ℝ) (k : ℕ) : ℝ × ℝ :=
  (D.value c φ x (D.slot k 0), D.value c φ x (D.slot k 1))

end Dag

/-- The partial derivative `∂G/∂z_j` of `G : ℝ^ι → ℝ`, as the derivative of the one-variable
function `u ↦ G(z with z_j := u)` at `u = z_j`. -/
noncomputable def pd {ι : Type*} [DecidableEq ι] (G : (ι → ℝ) → ℝ) (j : ι) : (ι → ℝ) → ℝ :=
  fun z => deriv (fun u => G (Function.update z j u)) (z j)

/-- The Hessian diagonal entry `∂²f/∂x_i²(x)`: the genuine second partial derivative of `f`. -/
noncomputable def hessDiag {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  pd (pd f i) i x

/-- First local partials of `φ : ℝ² → ℝ` at `z`: `φ_{,1}` (`κ = 0`) and `φ_{,2}` (`κ = 1`). -/
noncomputable def lp1 (φ : ℝ × ℝ → ℝ) (κ : Fin 2) (z : ℝ × ℝ) : ℝ :=
  if κ = 0 then deriv (fun t => φ (t, z.2)) z.1 else deriv (fun t => φ (z.1, t)) z.2

/-- Pure second local partials of `φ` at `z`: `φ_{,11}` (`κ = 0`) and `φ_{,22}` (`κ = 1`). -/
noncomputable def lp2 (φ : ℝ × ℝ → ℝ) (κ : Fin 2) (z : ℝ × ℝ) : ℝ :=
  if κ = 0 then deriv (fun t => lp1 φ 0 (t, z.2)) z.1 else deriv (fun t => lp1 φ 1 (z.1, t)) z.2

/-- The mixed local partial `φ_{,12}` at `z`: the derivative in the second argument of `φ_{,1}`
(for `φ ∈ C²` it equals `φ_{,21}`). -/
noncomputable def lp12 (φ : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  deriv (fun t => lp1 φ 0 (z.1, t)) z.2

end CancelFreeHessian.Formula


