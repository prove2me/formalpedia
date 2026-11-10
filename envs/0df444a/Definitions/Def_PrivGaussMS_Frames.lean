-- Prove2me | Definitions.Def_PrivGaussMS_Frames
-- name    : PrivGaussMS_Frames
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:44.826168+00:00
-- url     : https://prove2.me/theorems/b32cd0b9-40d3-44fa-858d-58a2b0c3f1e4
-- title:
--   Uniform frames (Gaussian polar factor) and uniform centered frames
-- statement:
--   A frame $Q\in\mathbb R^{N\times p}$ satisfies $Q^TQ=I_p$. The **uniform frame** is the law of the polar factor $G(G^TG)^{-1/2}$ of an $N\times p$ matrix $G$ with independent standard Gaussian entries; for $N=p$ it is the Haar law on the orthogonal group. A frame $U\in\mathbb R^{n\times d}$ is **centered** if $1_n^TU=0$; the **uniform centered frame** is the law of $EQ$, where $Q$ is a uniform $(n-1)\times d$ frame and the columns of $E\in\mathbb R^{n\times(n-1)}$ form an orthonormal basis of $1_n^\perp$.
--
--   Every random reference dataset of the construction is the rows of a uniform centered frame: it has empirical mean $0$ and scatter $I_d$.
--
--   **Formalization Note** $E$ is the Helmert basis; the paper notes the law does not depend on the basis. On the null event where $G^TG$ is singular the polar map returns $0$. `firstRows r` keeps the first $r$ rows.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Appendix A.3, 'Uniform frames and block densities', p.28

import Mathlib
import Definitions.Def_PrivGaussMS_Statistics

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace PrivGaussMS

/-!
# Uniform frames and uniform centered frames

Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission
(manuscript sha256 1838c582…), Appendix A.3, "Uniform frames and block densities", p.28.

"A frame `Q ∈ ℝ^{N×p}` satisfies `QᵀQ = I_p`. A uniform frame has the unique distribution invariant
under left multiplication by every orthogonal `N × N` matrix … For `N ≥ p`, Gaussian polar
factorization gives `Q = G(GᵀG)^{−1/2}`, where `G` has independent standard Gaussian entries. …
An `n × d` frame `U` is centered if `1ᵀ_n U = 0`. For the basis matrix `E` above and a uniform
`(n − 1) × d` frame `Q`, `U = EQ` is a uniform centered frame." (p.28)

**Formalization Note.**
* `uniformFrame N p` is defined as the paper's polar construction, the pushforward of the i.i.d.
  `N(0,1)` matrix under `G ↦ G(GᵀG)^{−1/2}`; on the null set where `GᵀG` is singular the map returns
  `0`. A uniform orthogonal matrix of order `N` (Haar measure on `O(N)`) is `uniformFrame N N`.
* `uniformCenteredFrame n d = (Q ↦ EQ)_* uniformFrame (n−1) d` with `E` the Helmert basis of
  `1_n^⊥` (column `j` is `(1, …, 1, −(j+1), 0, …, 0)/√((j+1)(j+2))`). The paper notes the law does not
  depend on the choice of basis (p.28).
* `firstRows r M` keeps the first `r` rows of `M` (the paper's subscript `[r]`); rows beyond the
  height of `M` are `0` (never used: every statement has `r ≤ N`).
-/

/-- An `N × p` matrix with independent standard Gaussian entries. -/
noncomputable def gaussMatrix (N p : ℕ) : Measure (Matrix (Fin N) (Fin p) ℝ) :=
  Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin p => gaussianReal 0 1

/-- The polar factor `G(GᵀG)^{−1/2}` (`0` when `GᵀG` is singular, a null event). -/
noncomputable def polar {N p : ℕ} (G : Matrix (Fin N) (Fin p) ℝ) : Matrix (Fin N) (Fin p) ℝ :=
  if (Gᵀ * G).det = 0 then 0 else G * (CFC.sqrt (Gᵀ * G))⁻¹

/-- The uniform `N × p` frame (p.28), by Gaussian polar factorization. -/
noncomputable def uniformFrame (N p : ℕ) : Measure (Matrix (Fin N) (Fin p) ℝ) :=
  (gaussMatrix N p).map polar

/-- The Helmert matrix: its `n − 1` columns are an orthonormal basis of `1_n^⊥`. -/
noncomputable def helmert (n : ℕ) : Matrix (Fin n) (Fin (n - 1)) ℝ := fun i j =>
  if (i : ℕ) ≤ (j : ℕ) then 1 / Real.sqrt (((j : ℝ) + 1) * ((j : ℝ) + 2))
  else if (i : ℕ) = (j : ℕ) + 1 then -((j : ℝ) + 1) / Real.sqrt (((j : ℝ) + 1) * ((j : ℝ) + 2))
  else 0

/-- The uniform centered `n × d` frame `U = EQ` (p.28). -/
noncomputable def uniformCenteredFrame (n d : ℕ) : Measure (Matrix (Fin n) (Fin d) ℝ) :=
  (uniformFrame (n - 1) d).map fun Q => helmert n * Q

/-- The first `r` rows of a matrix (the paper's subscript `[r]`). -/
def firstRows {N p : ℕ} (r : ℕ) (M : Matrix (Fin N) (Fin p) ℝ) : Matrix (Fin r) (Fin p) ℝ :=
  fun i j => if h : (i : ℕ) < N then M ⟨i, h⟩ j else 0

/-- The rows of an `n × d` matrix viewed as a dataset of `n` records in `ℝ^d`. -/
noncomputable def rowsOf {N p : ℕ} (U : Matrix (Fin N) (Fin p) ℝ) : Fin N → Vec p :=
  fun i => WithLp.toLp 2 (U i)

end PrivGaussMS


