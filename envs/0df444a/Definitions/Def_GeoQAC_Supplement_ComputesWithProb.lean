-- Prove2me | Definitions.Def_GeoQAC_Supplement_ComputesWithProb
-- name    : GeoQAC_Supplement_ComputesWithProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:19:24.914865+00:00
-- url     : https://prove2.me/theorems/08619e60-ab73-4740-aaad-466d3722fb9c
-- title:
--   Bounded-error computation with $|0\rangle$ ancillas
-- statement:
--   Apply a circuit $C$ to $|x\rangle$ on the input qubits and $|0\rangle$ on every ancilla, and measure the designated output qubit. $C$ **computes $f$ with success probability at least $p$** if this gives $f(x)$ with probability at least $p$ for every $x\in\{0,1\}^n$. Bounded-error computation is $p=2/3$.
--
--   This is the decision convention of the classes $\mathrm{QAC}^0$ and 2D-$\mathrm{QAC}^0$.
--
--   **Formalization Note** Inputs at any injective placement, output at any qubit; the published `GeoQAC.inputState` with the one-qubit vector $|0\rangle$ on every ancilla.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.4, p.11; p.10 (ancillas $|0^a\rangle$)

import Mathlib
import Definitions.Def_GeoQAC_ComputesExactly

namespace GeoQAC.Supplement

open GeoQAC Matrix

/-!
# Bounded-error computation with `|0⟩` ancillas

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 2.4, p.11: "apply `C` to `|x⟩`
and its prescribed ancillas, and let `g_C(x)` be the outcome of measuring the designated output qubit
in the computational basis. The circuit computes `f` with success probability at least `p` if
`Pr[g_C(x) = f(x)] ≥ p` for every `x`. … Unless stated otherwise, approximate (bounded-error)
computation means success probability at least `2/3` on every input." p.10: "Unless otherwise
stated, ancillas are initialized to be `|0^a⟩`."

**Formalization Note.** Inputs at any injective placement `inp`, output at any qubit `out`; the
ancillas start in `|0⟩` (`ket0`), via the published `GeoQAC.inputState`.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The one-qubit vector `|0⟩`. -/
def ket0 : Bool → ℂ := fun b => if b then 0 else 1

/-- `C` computes `f` with success probability at least `p`, from `|0⟩` ancillas, inputs at `inp`
and output qubit `out` (Definition 2.4, p.11). -/
def ComputesWithProb {d n : ℕ} (p : ℝ) (C : QACCircuit V d) (inp : Fin n ↪ V) (out : V)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool,
    p ≤ ∑ y ∈ Finset.univ.filter (fun y : V → Bool => y out = f x),
      ‖(C.matrix *ᵥ inputState inp (fun _ => ket0) x) y‖ ^ 2

end GeoQAC.Supplement


