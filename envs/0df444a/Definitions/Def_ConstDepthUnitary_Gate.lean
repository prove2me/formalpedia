-- Prove2me | Definitions.Def_ConstDepthUnitary_Gate
-- name    : ConstDepthUnitary_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:17.692442+00:00
-- url     : https://prove2.me/theorems/d03ace55-39e9-49c6-9321-763a2c8949d6
-- title:
--   One-qubit, two-qubit and fan-out gates
-- statement:
--   The gates of the circuit model act on a finite set $W$ of wires, with computational basis states the functions $x:W\to\{0,1\}$. There are exactly three kinds of gate:
--
--   1. an arbitrary unitary $u\in U(2)$ on one wire $q$;
--   2. an arbitrary unitary $u\in U(4)$ on an ordered pair of distinct wires $(p,q)$ (all-to-all connectivity);
--   3. a **fan-out gate** with control $c$ and nonempty target set $T\not\ni c$, acting on every basis state by
--   $$|y\rangle\mapsto|y'\rangle,\qquad y'_v=y_v\oplus y_c\ \ (v\in T),\qquad y'_v=y_v\ \ (v\notin T).$$
--
--   One- and two-qubit gates act as the identity on all other wires. The first two kinds form the standard model; adding the third gives the model $\mathrm{QAC}_f$. The **support** of a gate is the set of wires it acts on, and the size of a fan-out gate is $|T|+1$.
--
--   **Formalization Note** The matrix of a one- or two-qubit gate has entry $u(x|_{\mathrm{supp}},y|_{\mathrm{supp}})$ at $(x,y)$ when $x,y$ agree off the support and $0$ otherwise; a fan-out gate is a permutation matrix on all basis states. The bit $0$ is `false`.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §3.1, p.14; Definition 6.2, p.36

import Mathlib

namespace ConstDepthUnitary

/-- The gates of the circuit model, on a finite set `W` of wires: an arbitrary one-qubit unitary, an
arbitrary two-qubit unitary on two distinct wires, and a fan-out gate with control `c` and nonempty
target set `T` not containing `c`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §3.1, p.14: "the standard quantum circuit model to comprise arbitrary 1- and 2-qubit unitaries
with all-to-all connectivity", and Definition 6.2, p.36 ("For r ≥ 1, the fan-out gate on r + 1 qubits").

**Formalization Note** There are no other constructors. A basis state of the wires is a function
`W → Bool`, with `false` the bit 0. -/
inductive Gate (W : Type) where
  /-- An arbitrary one-qubit unitary on wire `q`. -/
  | one (q : W) (u : Matrix.unitaryGroup Bool ℂ)
  /-- An arbitrary two-qubit unitary on the distinct wires `p`, `q` (in this order). -/
  | two (p q : W) (h : p ≠ q) (u : Matrix.unitaryGroup (Bool × Bool) ℂ)
  /-- The fan-out gate with control `c` and target set `T`. -/
  | fanout (c : W) (T : Finset W) (hc : c ∉ T) (hT : T.Nonempty)

namespace Gate

variable {W : Type} [DecidableEq W]

/-- The wires a gate acts on. -/
def support : Gate W → Finset W
  | one q _ => {q}
  | two p q _ _ => {p, q}
  | fanout c T _ _ => insert c T

/-- A gate of the standard model: anything but a fan-out (§3.1, p.14). -/
def IsStandard : Gate W → Prop
  | fanout _ _ _ _ => False
  | _ => True

/-- The number of qubits a fan-out gate acts on (control included); `0` for the other gates. -/
def fanoutSize : Gate W → ℕ
  | g@(fanout _ _ _ _) => g.support.card
  | _ => 0

/-- The map on basis states of the fan-out gate, §3.1, p.14:
`FANOUT_ℓ |x₁, x₂, …, x_ℓ⟩ = |x₁, x₁ ⊕ x₂, …, x₁ ⊕ x_ℓ⟩`, on **all** basis states: each target wire is
XORed with the control, whatever its value. -/
def fanoutMap (c : W) (T : Finset W) (y : W → Bool) : W → Bool :=
  fun v => if v ∈ T then xor (y v) (y c) else y v

/-- The matrix of a gate on all the wires. A one- or two-qubit gate acts by its unitary on its wires
and as the identity elsewhere: the entry `(x, y)` is the unitary's entry at the restrictions of `x`
and `y` if they agree off the support, and `0` otherwise. A fan-out gate is the permutation matrix of
`fanoutMap`: the entry `(x, y)` is `1` exactly when `x = fanoutMap c T y`. -/
noncomputable def matrix [Fintype W] : Gate W → Matrix (W → Bool) (W → Bool) ℂ
  | one q u => Matrix.of fun x y =>
      if ∀ v, v ≠ q → x v = y v then (u : Matrix Bool Bool ℂ) (x q) (y q) else 0
  | two p q _ u => Matrix.of fun x y =>
      if ∀ v, v ≠ p → v ≠ q → x v = y v then
        (u : Matrix (Bool × Bool) (Bool × Bool) ℂ) (x p, x q) (y p, y q) else 0
  | fanout c T _ _ => Matrix.of fun x y => if x = fanoutMap c T y then 1 else 0

end Gate

end ConstDepthUnitary


