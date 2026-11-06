-- Prove2me | Definitions.Def_GlobalSinkhorn_potential
-- name    : GlobalSinkhorn_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T04:22:05.83159+00:00
-- url     : https://prove2.me/theorems/2fb4ec77-9043-445d-9489-802a675a2bbd
-- title:
--   The scale-invariant potential $\Phi(w)=\langle w^2\rangle\langle w^{-2}\rangle-1$
-- statement:
--   For a vector $w\in\mathbb R^n_{>0}$ the **scale-invariant potential** is
--   $$
--   \Phi(w)=\langle w^2\rangle\,\langle w^{-2}\rangle-1,
--   $$
--   where $w^2$ and $w^{-2}$ are taken componentwise and $\langle\cdot\rangle$ is the average of the entries. By Cauchy–Schwarz $\Phi(w)\ge0$, with equality exactly when $w$ is a constant vector, and $\Phi(cw)=\Phi(w)$ for every $c>0$. It measures how far the column-scaling vector of a Sinkhorn–Knopp iterate is from constant, and Lemma 3.2 shows it contracts geometrically.
--
--   **Formalization Note** The paper uses $\Phi$ only on positive vectors; Lean's total inverse is used for $w_j^{-1}$, and every statement of the mission assumes $w>0$.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Eq. (23), p.15

import Mathlib
import Definitions.Def_GlobalSinkhorn_avg

open Matrix

namespace GlobalSinkhorn

/-- The scale-invariant potential `Φ(w) = ⟨w²⟩⟨w⁻²⟩ − 1`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Eq. (23), p.15.

**Formalization Note.** The paper uses `Φ` only on positive vectors; `(w j)⁻¹` is Lean's total
inverse, and every statement of the mission assumes `w > 0`. -/
noncomputable def potential {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  avg (fun j => w j ^ 2) * avg (fun j => (w j)⁻¹ ^ 2) - 1

end GlobalSinkhorn


