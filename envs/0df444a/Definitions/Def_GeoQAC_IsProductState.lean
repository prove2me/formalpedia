-- Prove2me | Definitions.Def_GeoQAC_IsProductState
-- name    : GeoQAC_IsProductState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:58.51612+00:00
-- url     : https://prove2.me/theorems/b7e328d1-a01c-4933-a84b-598c62506222
-- title:
--   Product states $\rho=\bigotimes_v\rho_v$
-- statement:
--   A state $\rho$ on the qubits $V$ is a **product state** when
--   $$
--   \rho=\bigotimes_{v\in V}\rho_v
--   $$
--   for one-qubit states $\rho_v$ (positive semidefinite $2\times2$ matrices of trace one). Mixed one-qubit factors are allowed.
--
--   **Formalization Note** The matrix entry of $\rho$ at $(x,y)$ is $\prod_v(\rho_v)_{x_v,y_v}$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 3.4, p.14

import Mathlib

namespace GeoQAC

open scoped ComplexOrder

/-- A product state `ρ = ⊗_v ρ_v` (arXiv:2604.07178, version of 2026-11-03, Lemma 3.4, p.14): each
`ρ_v` is a one-qubit state (positive semidefinite, trace one) and the `(x, y)` entry of `ρ` is
`∏_v (ρ_v)_{x_v, y_v}`.

**Formalization Note.** Mixed one-qubit factors are allowed, as in Lemma 3.4. -/
def IsProductState {V : Type} [Fintype V] (ρ : Matrix (V → Bool) (V → Bool) ℂ) : Prop :=
  ∃ σ : V → Matrix Bool Bool ℂ, (∀ v, (σ v).PosSemidef ∧ (σ v).trace = 1) ∧
    ρ = Matrix.of fun x y => ∏ v, σ v (x v) (y v)

end GeoQAC


