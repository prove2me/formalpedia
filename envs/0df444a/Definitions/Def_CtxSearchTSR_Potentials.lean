-- Prove2me | Definitions.Def_CtxSearchTSR_Potentials
-- name    : CtxSearchTSR_Potentials
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:44.943412+00:00
-- url     : https://prove2.me/theorems/1c66b6fd-0a25-4120-a453-8cc5413436dd
-- title:
--   The potentials $\Phi(\mathbf m,R,\mathbf z)=\operatorname{Tr}R+(\mathbf z-\mathbf m)^\top R^{-1}(\mathbf z-\mathbf m)$ and $\varphi(m,r,z)=r+(m-z)^2/r$
-- statement:
--   The analysis of Algorithm 2 uses the **trace-square-root potential**
--
--   $$\Phi(\mathbf m,R,\mathbf z)=\operatorname{Tr}R+(\mathbf z-\mathbf m)^\top R^{-1}(\mathbf z-\mathbf m) \tag{12}$$
--
--   for $\mathbf m,\mathbf z\in\mathbb R^d$ and a positive definite $R$, and its one-dimensional version
--
--   $$\varphi(m,r,z)=r+\frac{(m-z)^2}{r}\qquad(m,z\in\mathbb R,\ r>0).$$
--
--   Neither is computed by the algorithm; they serve only in the proof that its expected total loss is at most $12\sqrt d$.
--
--   **Formalization Note** $R^{-1}$ is Mathlib's matrix inverse, the true inverse for every invertible $R$ (all uses have $R\succ0$). $\varphi$ is defined for every real $r$; at $r=0$ Lean's $c/0=0$ gives the value $0$, which the paper never uses.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), proof of Theorem 2.4, p.11, (12); Lemma C.1, p.19

import Mathlib

open Matrix

namespace CtxSearchTSR

/-!
# The potentials Φ and φ

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…).

* Φ(**m**, R, **z**) = Tr R + (**z** − **m**)ᵀ R⁻¹ (**z** − **m**), proof of Theorem 2.4, p.11, (12).
* φ(m, r, z) = r + (m − z)²/r, Lemma C.1, p.19 (for r > 0).

**Formalization Note.** `R⁻¹` is Mathlib's `Matrix.inv`, the true inverse whenever R is invertible
(every use has R ≻ 0). φ is written for every real r; Lean's `/ 0 = 0` gives φ(m, 0, z) = 0, a value
the paper never uses (it assumes r > 0).
-/

/-- The potential (12): Φ(**m**, R, **z**) = Tr R + (**z** − **m**)ᵀ R⁻¹ (**z** − **m**). -/
noncomputable def Phi {d : ℕ} (m : Fin d → ℝ) (R : Matrix (Fin d) (Fin d) ℝ) (z : Fin d → ℝ) : ℝ :=
  Matrix.trace R + (z - m) ⬝ᵥ (R⁻¹ *ᵥ (z - m))

/-- The one-dimensional potential of Lemma C.1: φ(m, r, z) = r + (m − z)²/r. -/
noncomputable def phi (m r z : ℝ) : ℝ := r + (m - z) ^ 2 / r

end CtxSearchTSR


