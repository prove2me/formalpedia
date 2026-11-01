-- Prove2me | Definitions.Def_DelayedGLCB_Vmat
-- name    : DelayedGLCB_Vmat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:13.423191+00:00
-- url     : https://prove2.me/theorems/303d3889-1752-4fbb-8aa2-a40d18a1ef29
-- title:
--   Design matrices $V_t=\sum_{s<t}X_sX_s'$, $W_t=\sum_{s\in T_t}X_sX_s'$ and the weighted norm $\|v\|_A$
-- statement:
--   For a sequence of feature vectors $X_1,X_2,\dots\in\mathbb R^d$:
--
--   1. the **design matrix** is $V_t=\sum_{s=1}^{t-1}X_sX_s'$, built from every feature played before round $t$;
--   2. the **complete-sample matrix** is $W_t=\sum_{s\in T_t}X_sX_s'$, built only from rounds whose reward has arrived;
--   3. for a square matrix $A$, the **weighted norm** is $\|v\|_A=\sqrt{v'Av}$.
--
--   DUCB-GLCB normalizes its exploration bonus by $V_t$, while the estimator only uses the samples behind $W_t$.
--
--   **Formalization Note** The weighted norm is defined for every matrix, with $\sqrt{\cdot}$ of a negative number equal to $0$; it is only applied to positive semidefinite matrices and their inverses.
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, §2, p.4 (‖x‖_A); §3.2, p.7 (W_t, V_t)

import Mathlib
import Definitions.Def_DelayedGLCB_completeSet

namespace DelayedGLCB

open Matrix

/-- The outer product `v v'` of a vector `v ∈ ℝ^d`. -/
def outer {d : ℕ} (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.vecMulVec v v

/-- The weighted norm `‖v‖_A = √(v'Av)` (Blanchet, Xu, Zhou, arXiv:2003.05174v1, §2, p.4).

**Formalization Note.** Defined for every square matrix; the square root of a negative number is
`0` in Lean, which never happens for the positive semidefinite matrices it is applied to. -/
noncomputable def wnorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ (A *ᵥ v))

/-- **The design matrix `V_t = Σ_{s=1}^{t−1} X_s X_s'`** of a feature sequence `X`
(Blanchet, Xu, Zhou, arXiv:2003.05174v1, §3.2, p.7: "`V_t = Σ_{s=1}^{t−1} X_s X_s'` as the matrix
consisting all available features at the end of round `t − 1`"). -/
noncomputable def Vmat {d : ℕ} (X : ℕ → Fin d → ℝ) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ s ∈ Finset.Ico 1 t, outer (X s)

/-- **The complete-sample matrix `W_t = Σ_{s ∈ T_t} X_s X_s'`**
(Blanchet, Xu, Zhou, arXiv:2003.05174v1, §3.2, p.7: "`W_t = Σ_{s∈T_t} X_s X_s'` as the matrix
consisting feature information with timestamps in `T_t`"), with `T_t = completeSet D ω t`. -/
noncomputable def Wmat {Ω : Type*} {d : ℕ} (D : ℕ → Ω → ℝ) (ω : Ω) (X : ℕ → Fin d → ℝ) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ s ∈ completeSet D ω t, outer (X s)

end DelayedGLCB


