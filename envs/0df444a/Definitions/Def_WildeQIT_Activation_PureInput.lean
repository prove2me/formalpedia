-- Prove2me | Definitions.Def_WildeQIT_Activation_PureInput
-- name    : WildeQIT_Activation_PureInput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T19:11:44.062674+00:00
-- url     : https://prove2.me/theorems/c0908981-5f23-4e43-8ca0-242f66b95283
-- title:
--   Pure bipartite input state $|\varphi\rangle_{RA'}$
-- statement:
--   A **pure bipartite input state** to a channel with input system $A'$ is a unit vector $|\varphi\rangle_{RA'}$ in $\mathcal H_R\otimes\mathcal H_{A'}$, where the reference system $R$ has any finite dimension. The channel coherent information (24.9) is maximized over these states, and Theorem 24.8.1 asserts the existence of one.
--
--   **Formalization Note** The reference system is `Fin k` with `k` part of the data; the vector is a complex function on `Fin k × a` (reference first) with $\langle\varphi|\varphi\rangle=1$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 24.3.1, eq. (24.9), p. 661

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 24.3.1, p. 661, eq. (24.9) ("all pure, bipartite states `φ_{AA′}`").
-/

namespace WildeQIT.Activation

/-- **A pure bipartite input state** `|φ⟩_{RA′}` (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, (24.9), p. 661): a unit vector on
`R ⊗ A′`, with a reference system `R` of any finite dimension.

**Formalization Note.** The reference is `Fin k` with `k : ℕ` part of the data; the vector is a
function on `Fin k × a` (Kronecker convention, reference first) with `⟨φ|φ⟩ = 1`. -/
structure PureInput (a : Type) [Fintype a] where
  /-- The dimension of the reference system `R`. -/
  k : ℕ
  /-- The state vector `|φ⟩_{RA′}`. -/
  vec : Fin k × a → ℂ
  /-- Normalization `⟨φ|φ⟩ = 1`. -/
  norm_one : star vec ⬝ᵥ vec = 1

end WildeQIT.Activation


