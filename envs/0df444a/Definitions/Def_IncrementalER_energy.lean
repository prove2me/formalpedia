-- Prove2me | Definitions.Def_IncrementalER_energy
-- name    : IncrementalER_energy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:22.532848+00:00
-- url     : https://prove2.me/theorems/53964885-73f8-45dd-945c-cab4296de2e0
-- title:
--   Electrical energy $d^\top L^\dagger d$ of a demand
-- statement:
--   For a square real matrix $L\in\mathbb R^{V\times V}$ on a finite index set $V$, $L^\dagger$ denotes its Moore–Penrose pseudoinverse, taken with respect to the standard inner product on $\mathbb R^V$. For a Laplacian $L=L_G$ and a demand vector $d\in\mathbb R^V$, the **electrical energy** of $d$ is
--
--   $$\mathcal E_G(d)=d^\top L_G^\dagger d .$$
--
--   This is the quantity the data structure of Theorem 1.1 approximates; with $d=\mathbf 1_u-\mathbf 1_v$ it is the effective resistance $R_{\mathrm{eff}}(u,v)$.
--
--   **Formalization Note** $L^\dagger$ is the published pseudoinverse `HarmonicGames.Decomposition.pinv` of the linear map $x\mapsto Lx$ on the Euclidean space $\mathbb R^V$, converted back to a matrix; it carries no hypothesis on $L$. For a symmetric positive semidefinite $L$ it is $\sum_{\lambda_i\neq0}\lambda_i^{-1}u_iu_i^\top$.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), §1, p.3 ($d^\top L_G^\dagger d$) and §3, p.11 (Reff)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv

open Matrix

namespace IncrementalER

/-!
# Pseudoinverse of a matrix and electrical energy of a demand

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), §1, p.3 (`d⊤L†_G d`), and
§3, p.11 (`Reff(u, v) := (1u − 1v)⊤L†_G(1u − 1v)`).

**Formalization Note.** `L†` is the published Moore–Penrose pseudoinverse
`HarmonicGames.Decomposition.pinv` of the linear map `x ↦ L x` on the Euclidean space `ℝ^V`
(standard inner product), turned back into a matrix with `Matrix.toEuclideanLin`. It carries no
hypothesis on `L`; for the symmetric positive semidefinite Laplacians used here it is the spectral
pseudoinverse `∑_{λ ≠ 0} λ⁻¹ u uᵀ`.
-/

/-- The Moore–Penrose pseudoinverse `L†` of a square real matrix, as a matrix. -/
noncomputable def pinvMat {V : Type*} [Fintype V] [DecidableEq V] (L : Matrix V V ℝ) :
    Matrix V V ℝ :=
  Matrix.toEuclideanLin.symm (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin L))

/-- The electrical energy `d⊤ L† d` of the demand `d` in the network with Laplacian `L`
(p.3, p.11). -/
noncomputable def energy {V : Type*} [Fintype V] [DecidableEq V] (L : Matrix V V ℝ)
    (d : V → ℝ) : ℝ :=
  d ⬝ᵥ (pinvMat L *ᵥ d)

end IncrementalER


