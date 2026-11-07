-- Prove2me | Definitions.Def_GeoQAC_IsCleanImpl
-- name    : GeoQAC_IsCleanImpl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:39.468686+00:00
-- url     : https://prove2.me/theorems/8e57078c-9a35-403c-bc83-133d5cf524f2
-- title:
--   Exact clean implementations of $U_f$ and of the parity unitary
-- statement:
--   The coherent version of $f:\{0,1\}^n\to\{0,1\}$ is the unitary $U_f|x,b\rangle=|x,b\oplus f(x)\rangle$, where $b$ is a one-qubit accumulator; the parity unitary is $U_{\oplus n}=U_{\mathrm{PARITY}_n}$.
--
--   An **exact clean implementation** of a unitary $U$ satisfies
--   $$
--   C\,|\phi,0^a\rangle=(U|\phi\rangle)\,|0^a\rangle
--   $$
--   for every logical input $|\phi\rangle$, up to a fixed global phase: the ancillas are returned to $|0^a\rangle$.
--
--   **Formalization Note** The $n$ controls and the accumulator are distinct qubits at any positions; all other qubits are ancillas in $|0\rangle$. The definition asks $C|x,b,0^a\rangle=e^{i\theta}|x,b\oplus f(x),0^a\rangle$ for all basis inputs with one $\theta$, which by linearity is the condition for every logical input.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.5 and p.11; §2.4, p.12

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit
import Definitions.Def_GeoQAC_parityFn

namespace GeoQAC

open Matrix

/-!
# Exact clean implementation of `U_f` and of the parity unitary

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), p.11: "The coherent version of f is the
unitary U_f|x, b⟩ = |x, b ⊕ f(x)⟩, where b is a one-qubit accumulator." Definition 2.5, p.11: "An
exact clean implementation of a unitary U satisfies C|ϕ, 0^a⟩ = (U|ϕ⟩)|0^a⟩ for every logical input
|ϕ⟩, up to a fixed global phase." §2.4, p.12: `U_⊕n|x, b⟩ = |x, b ⊕ PARITY_n(x)⟩`.

**Formalization Note.**
* The logical qubits are the `n` controls `ctrl : Fin n ↪ V` and the accumulator `acc ∉ ctrl`, at
  any positions; every other qubit is an ancilla starting and ending in `|0⟩`.
* `load ctrl acc x b` is the basis configuration with `x` on the controls, `b` on the accumulator and
  `0` elsewhere.
* One global phase `e^{iθ}` serves every logical basis input; by linearity this is Definition 2.5 for
  every logical input `|ϕ⟩`.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The basis configuration `|x, b, 0^a⟩`: `x` on the controls, `b` on the accumulator, `0` on every
other qubit. -/
noncomputable def load {n : ℕ} (ctrl : Fin n ↪ V) (acc : V) (x : Fin n → Bool) (b : Bool) :
    V → Bool :=
  fun v => if v = acc then b else if h : ∃ i, ctrl i = v then x h.choose else false

/-- `C` is an exact clean implementation of `U_f` with controls `ctrl` and accumulator `acc`
(Definition 2.5, p.11): `C|x, b, 0^a⟩ = e^{iθ}|x, b ⊕ f(x), 0^a⟩` for all `x, b`, with one fixed
`θ`. -/
def IsCleanImpl {d n : ℕ} (C : QACCircuit V d) (ctrl : Fin n ↪ V) (acc : V)
    (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ i, ctrl i ≠ acc) ∧
  ∃ θ : ℝ, ∀ (x : Fin n → Bool) (b : Bool),
    C.matrix *ᵥ basisVec (load ctrl acc x b) =
      Complex.exp (θ * Complex.I) • basisVec (load ctrl acc x (xor b (f x)))

/-- An exact clean implementation of the parity unitary `U_⊕n` on the `n` controls `ctrl`
(§2.4, p.12; Definition 2.5, p.11). -/
def IsCleanParity {d n : ℕ} (C : QACCircuit V d) (ctrl : Fin n ↪ V) (acc : V) : Prop :=
  IsCleanImpl C ctrl acc (parityFn n)

end GeoQAC


