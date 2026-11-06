-- Prove2me | Definitions.Def_NondualOpt_Vmax
-- name    : NondualOpt_Vmax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:55.02877+00:00
-- url     : https://prove2.me/theorems/3904f1bb-795a-4c92-af64-e91e872a7f7c
-- title:
--   The minimax value $V^{\max}_{X,H,T}$ of the affine max-regret game
-- statement:
--   The **minimax value** of the $T$-round affine max-regret game is
--   $$
--   V^{\max}_{X,H,T}=\Big\langle\!\Big\langle\inf_{x_t\in X}\sup_{\ell_t\in\mathcal F}\Big\rangle\!\Big\rangle_{t=1}^T\Big\{\sum_{t=1}^T\ell_t(x_t)-\inf_{u\in X}T\max_{t\in[T]}\ell_t(u)\Big\},
--   $$
--   the backward recursion started from the empty history. Through Lemma 2 it bounds the first-order optimization error, and Theorem 6 bounds it above and below through sequential fat-shattering.
--
--   **Formalization Note** Extended-real valued.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (8), p.9

import Mathlib
import Definitions.Def_NondualOpt_vmaxStage

namespace NondualOpt

/-- The minimax value of the `T`-round affine max-regret game,
`V^max_{X,H,T} = ⟪inf_{x_t ∈ X} sup_{ℓ_t ∈ F}⟫_{t=1}^T {∑_t ℓ_t(x_t) − inf_{u ∈ X} T max_t ℓ_t(u)}`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (8), first line, p.9.

**Formalization Note.** `vmaxStage` started from the empty history; `EReal`-valued. -/
noncomputable def Vmax {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) (T : ℕ) : EReal :=
  vmaxStage pair X H T 0 Fin.elim0

end NondualOpt


