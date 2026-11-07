-- Prove2me | Definitions.Def_IterRoundDet_Covariance
-- name    : IterRoundDet_Covariance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:21.042195+00:00
-- url     : https://prove2.me/theorems/2cd02789-ab85-4582-917f-84b7f6242a06
-- title:
--   The covariance matrix $C$, the form $v^\top C^\dagger v$, and graph Laplacians
-- statement:
--   For a law $\mu$ with marginals $a$,
--
--   $$C=\mathbb E_\mu\big[(\mathbf 1_S-a)(\mathbf 1_S-a)^\top\big].$$
--
--   The file defines this matrix, the quadratic form $v^\top C^\dagger v$ of its Moore–Penrose inverse, and graph Laplacians: symmetric matrices with $L_{ij}\le 0$ for $i\neq j$ and $L\mathbf 1=0$. The curvature of the entropy is governed by these objects.
--
--   **Formalization Note** $C^\dagger$ is the published `HarmonicGames.Decomposition.pinv`, on the matrix as a linear map of Euclidean space. The sanity file proves $v^\top L^\dagger v=u^\top Lu$ for $v=Lu$ and $L$ symmetric, which is how the paper uses it.
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.5, p.14; Lemma 2.9, p.11

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_HarmonicGames_Decomposition_Pinv

set_option autoImplicit false

namespace IterRoundDet

/-!
# The covariance matrix, the form `v⊤C†v`, and graph Laplacians

Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…): Lemma 3.5, p.14; Lemma 2.9,
p.11.
-/

variable {n : ℕ}

/-- `C = E_μ[(1_S − a)(1_S − a)⊤]`, Lemma 3.5, p.14. -/
noncomputable def covMat (μ : Finset (Fin n) → ℝ) (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ S, μ S * (ind S i - a i) * (ind S j - a j)

/-- `v⊤C†v`, with `C†` the Moore–Penrose inverse of the linear map `C` on Euclidean space.

**Formalization Note.** `C†` is the published `HarmonicGames.Decomposition.pinv`, which adds no
condition on the map. -/
noncomputable def pinvForm {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  v ⬝ᵥ WithLp.ofLp
    (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin C) (WithLp.toLp 2 v))

/-- A graph Laplacian, Lemma 2.9, p.11: `L` is symmetric, `L_ij ≤ 0` for `i ≠ j`, and `L1 = 0`. -/
def IsGraphLaplacian {m : ℕ} (L : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  L.IsSymm ∧ (∀ i j, i ≠ j → L i j ≤ 0) ∧ L.mulVec (fun _ => 1) = 0

end IterRoundDet


