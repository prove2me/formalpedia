-- Prove2me | Definitions.Def_ImpuritySim_Krylov
-- name    : ImpuritySim_Krylov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:28:00.499047+00:00
-- url     : https://prove2.me/theorems/d5b67821-5c0a-4acb-99bb-f453af1f8af3
-- title:
--   Krylov spaces $K_{*d}$ and Krylov shells $W_{*d}$ (3.4)–(3.5)
-- statement:
--   Let $E_*$ be an operator on a complex inner-product space $W_*$ and $\mu_{1*},\dots,\mu_{2m*}\in W_*$. With $W_{*0}=\operatorname{span}\{\mu_{1*},\dots,\mu_{2m*}\}$, the **depth-$d$ Krylov space** and the **depth-$d$ Krylov shell** are
--   $$K_{*d}=\operatorname{span}\{W_{*0},E_*W_{*0},\dots,E_*^dW_{*0}\}\quad(3.4),\qquad W_{*d}=K_{*d}\ominus K_{*,d-1}\quad(3.5),$$
--   with $K_{*,-1}=\{0\}$, so $W_{*0}=K_{*0}$.
--
--   Orthonormal bases of the shells, taken in order of depth, block-tridiagonalize a Hermitian $E_*$ (Lemma 3.1); this is the one-dimensional structure behind the bandwise Krylov basis.
--
--   **Formalization Note** $W_*$ is any complex inner-product space and $E_*$ any linear map; $W_{*d}$ for $d\ge1$ is $K_{*d}\cap K_{*,d-1}^{\perp}$.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), (3.4)–(3.5), p.15

import Mathlib

namespace ImpuritySim

/-!
# Krylov spaces and Krylov shells (3.4)–(3.5)

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2): (3.4),
(3.5), p.15.

**Formalization Note.**
* The ambient space `V` plays the role of `W∗`; `E` is a linear map on `V` (the page's Hermitian
  `E∗`, self-adjointness is a hypothesis where used), `μ : Fin (2m) → V` the vectors `μ_{j∗}`.
* `krylov E μ d = K∗d = span{W∗0, E W∗0, …, E^d W∗0}` with `W∗0 = span{μ_1, …, μ_{2m}}`.
* `shell E μ 0 = K∗0 = W∗0`, `shell E μ (d+1) = K∗,d+1 ⊖ K∗d = K∗,d+1 ⊓ (K∗d)ᗮ` (3.5).
-/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The depth-`d` Krylov space `K∗d = span{E^k μ_j : k ≤ d, j}` (3.4). -/
def krylov {m : ℕ} (E : V →ₗ[ℂ] V) (μ : Fin (2 * m) → V) (d : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ k ≤ d, ∃ j, v = (E ^ k) (μ j)}

/-- The depth-`d` Krylov shell `W∗d = K∗d ⊖ K∗,d−1` (3.5), with `K∗,−1 = {0}`. -/
noncomputable def shell {m : ℕ} (E : V →ₗ[ℂ] V) (μ : Fin (2 * m) → V) : ℕ → Submodule ℂ V
  | 0 => krylov E μ 0
  | d + 1 => krylov E μ (d + 1) ⊓ (krylov E μ d)ᗮ

end ImpuritySim


