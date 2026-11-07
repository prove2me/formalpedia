-- Prove2me | Definitions.Def_GeoQAC_ComputesExactly
-- name    : GeoQAC_ComputesExactly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:34.007591+00:00
-- url     : https://prove2.me/theorems/5de30072-dc3c-4df3-8ca7-23182187cda9
-- title:
--   Exact computation of a Boolean function from product ancillas
-- statement:
--   Let $C$ be a QAC circuit and $f:\{0,1\}^n\to\{0,1\}$. Apply $C$ to $|x\rangle$ (on $n$ designated input qubits) and its prescribed ancillas, and measure the designated output qubit in the computational basis. $C$ **computes $f$ exactly** if this gives $f(x)$ with probability $1$ for every $x\in\{0,1\}^n$. The remaining registers may contain input-dependent garbage.
--
--   Here the ancillas start in a product state $\bigotimes_{v}|a_v\rangle$ of one-qubit unit vectors; the all-zero ancilla $|0^a\rangle$ is the special case $|a_v\rangle=|0\rangle$.
--
--   **Formalization Note** The inputs are placed by any injective map into the qubits, and the output is any qubit: the paper constrains neither. The input state is $|x\rangle\otimes\bigotimes_{v\notin\mathrm{inputs}}|a_v\rangle$, and exactness is the statement that the Born probability of reading $f(x)$ on the output qubit equals $1$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.4, p.11; p.11 (product ancillas); §3.5, p.26

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit
import Definitions.Def_DHRUniq_IsUnitVec

namespace GeoQAC

open DHRUniq (IsUnitVec)

open Matrix

/-!
# Exact computation of a Boolean function from product ancillas

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 2.4, p.11: "For
f : {0,1}^n → {0,1}, apply C to |x⟩ and its prescribed ancillas, and let g_C(x) be the outcome of
measuring the designated output qubit in the computational basis. The circuit computes f with
success probability at least p if Pr[g_C(x) = f(x)] ≥ p for every x ∈ {0,1}^n. Exact computation
has p = 1." The remaining registers may hold garbage (p.11). §3.5 (p.26) and Theorem 3.14 (p.25)
allow product ancillas; p.11: "A depth-d QAC circuit may have arbitrarily many ancillas initialized
to product states."

**Formalization Note.**
* The `n` inputs sit at any injective placement `inp : Fin n ↪ V`; the output qubit `out` is any
  qubit. The paper constrains neither.
* Every non-input qubit `v` starts in the one-qubit unit vector `anc v` (a product ancilla state;
  `|0⟩` is the special case `anc v = |0⟩`). The values of `anc` at input positions are unused.
* `embedInput inp anc u` is the vector `u ⊗ (⊗_{v ∉ inp} anc_v)`, `u` living on the input qubits.
* Exact computation: for every `x` the Born probability that the output qubit reads `f(x)` is `1`.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `u` on the input qubits `inp`, tensored with the product ancilla state `⊗_{v ∉ inp} anc_v`. -/
noncomputable def embedInput {n : ℕ} (inp : Fin n ↪ V) (anc : V → Bool → ℂ)
    (u : (Fin n → Bool) → ℂ) : (V → Bool) → ℂ :=
  fun y => u (fun i => y (inp i)) *
    ∏ v ∈ Finset.univ.filter (fun v => ∀ i, inp i ≠ v), anc v (y v)

/-- The initial state `|x⟩ ⊗ (⊗_{v ∉ inp} anc_v)` on input `x`. -/
noncomputable def inputState {n : ℕ} (inp : Fin n ↪ V) (anc : V → Bool → ℂ)
    (x : Fin n → Bool) : (V → Bool) → ℂ :=
  embedInput inp anc (basisVec x)

/-- `C` computes `f` exactly from the product ancillas `anc`, with inputs at `inp` and output qubit
`out` (Definition 2.4, p.11): the ancilla factors are unit vectors, and on every input `x` measuring
`out` in the computational basis gives `f(x)` with probability `1`. -/
def ComputesExactly {d n : ℕ} (C : QACCircuit V d) (inp : Fin n ↪ V) (anc : V → Bool → ℂ)
    (out : V) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ v, (∀ i, inp i ≠ v) → IsUnitVec (anc v)) ∧
  ∀ x : Fin n → Bool,
    ∑ y ∈ Finset.univ.filter (fun y : V → Bool => y out = f x),
      ‖(C.matrix *ᵥ inputState inp anc x) y‖ ^ 2 = 1

end GeoQAC


