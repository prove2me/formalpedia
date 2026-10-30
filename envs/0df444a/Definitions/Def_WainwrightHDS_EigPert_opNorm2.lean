-- Prove2me | Definitions.Def_WainwrightHDS_EigPert_opNorm2
-- name    : WainwrightHDS_EigPert_opNorm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:00.18955+00:00
-- url     : https://prove2.me/theorems/65107704-9929-41ba-bc4f-41df9a6176be
-- title:
--   The $\ell_2$ operator norm $|||M|||_2$ of a square matrix
-- statement:
--   For a real $d \times d$ matrix $M$, the **$\ell_2$ operator norm** (spectral norm) is
--
--   $$
--   |||M|||_2 \;=\; \sup_{u \neq 0} \frac{\|Mu\|_2}{\|u\|_2},
--   $$
--
--   where $\|\cdot\|_2$ is the Euclidean norm on $\mathbb{R}^d$. For a symmetric matrix it equals $\max_{v \in \mathbb{S}^{d-1}} |\langle v, Mv\rangle|$, the largest absolute value of an eigenvalue.
--
--   This is the norm in which the size of a perturbation is measured in Weyl's inequality (8.9) and in the eigenvector perturbation bound of Theorem 8.5.
--
--   **Formalization Note** The value is the operator norm of the continuous linear map $u \mapsto Mu$ on `EuclideanSpace ℝ (Fin d)` (`Matrix.toEuclideanCLM`). It is not Mathlib's default entrywise sup norm on matrices, nor the Frobenius norm.
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, p. 6 (PDF p. 26), Eq. (1.9)

import Mathlib

namespace WainwrightHDS.EigPert

/-- **The ℓ₂ operator norm of a square matrix**, `|||M|||₂ := sup_{u ≠ 0} ‖Mu‖₂ / ‖u‖₂`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, p. 6 (PDF p. 26), Eq. (1.9); used throughout Chapter 8 (e.g. Theorem 8.5, p. 243,
PDF p. 263).

**Formalization Note.** The value is the operator norm of the continuous linear map `u ↦ M u` on
Euclidean space `EuclideanSpace ℝ (Fin d)` (`Matrix.toEuclideanCLM`), i.e. the spectral norm. It is
*not* Mathlib's default entrywise sup norm on `Matrix`, nor the Frobenius norm. Indices are
0-based (`Fin d`), the book's are `1, …, d`. -/
noncomputable def opNorm2 {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) M‖

end WainwrightHDS.EigPert


