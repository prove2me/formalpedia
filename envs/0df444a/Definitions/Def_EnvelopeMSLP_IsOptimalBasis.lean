-- Prove2me | Definitions.Def_EnvelopeMSLP_IsOptimalBasis
-- name    : EnvelopeMSLP_IsOptimalBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:44.864441+00:00
-- url     : https://prove2.me/theorems/b532d2d5-6e86-4e00-8385-c036e6ea87b7
-- title:
--   Optimal basis of the LP (4)
-- statement:
--   The basis $\beta$ is optimal for the data $(D,b,c)$ of form (4) when
--   $$\det(D_\beta)\ne0,\qquad D_\beta^{-1}b\ge0,\qquad c_\beta D_\beta^{-1}D\ge c.$$
--   The first condition makes $x_\beta=D_\beta^{-1}b$, $x_{[n]\setminus\beta}=0$ a basic solution, the second makes $\beta$ primal feasible, and the third makes it dual feasible. This is the set $R_\beta$ of Lemma 1, in which the paper's proof writes $c$ for the objective $d$ of (4).
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_basisMatrix
open Matrix

namespace EnvelopeMSLP

/-- **Optimal basis of form (4).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9:
`R_β = {D : det(D_β) ≠ 0} ∩ {D : D_β⁻¹ b ≥ 0} ∩ {D : c_β D_β⁻¹ D ≥ c}`.
The first condition makes `β` a basis, the second makes it primal feasible, the third makes it
dual feasible.

**Formalization Note.** The proof of Lemma 1 writes `c` for the objective `d` of form (4). All
three conditions are invariant under reordering the columns of `β`. -/
def IsOptimalBasis {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (β : Fin m ↪ Fin n) : Prop :=
  (basisMatrix D β).det ≠ 0 ∧ 0 ≤ (basisMatrix D β)⁻¹ *ᵥ b ∧
    c ≤ ((c ∘ β) ᵥ* (basisMatrix D β)⁻¹) ᵥ* D

end EnvelopeMSLP


