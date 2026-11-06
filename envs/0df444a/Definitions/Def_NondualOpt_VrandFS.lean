-- Prove2me | Definitions.Def_NondualOpt_VrandFS
-- name    : NondualOpt_VrandFS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:27.438706+00:00
-- url     : https://prove2.me/theorems/ee885518-acca-4c36-8eed-625bd7282531
-- title:
--   The value of the randomized max-regret game (right side of ①)
-- statement:
--   The **randomized game value** is
--   $$
--   \Big\langle\!\Big\langle\sup_{r_t}\inf_{s_t}\mathbb E_{x_t\sim s_t,\ \ell_t\sim r_t}\Big\rangle\!\Big\rangle_{t=1}^T\Big\{\sum_{t=1}^T\ell_t(x_t)-\inf_{u\in X}T\max_{t\in[T]}\ell_t(u)\Big\},
--   $$
--   the backward recursion of the randomized game started from the empty history, with finitely supported laws $r_t$ on $Z_{X,H}$ and $s_t$ on $X$. Assumption 3 requires that it equals $V^{\max}_{X,H,T}$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (8), p.9, footnote 6

import Mathlib
import Definitions.Def_NondualOpt_vrandStage

namespace NondualOpt

/-- The value of the randomized affine max-regret game, the right side of ① in (8):
`⟪sup_{r_t} inf_{s_t} E_{x_t ∼ s_t, ℓ_t ∼ r_t}⟫_{t=1}^T {∑_t ℓ_t(x_t) − inf_{u ∈ X} T max_t ℓ_t(u)}`,
with finitely supported laws.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (8), p.9, and footnote 6. -/
noncomputable def VrandFS {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) (T : ℕ) : EReal :=
  vrandStage pair X H T 0 Fin.elim0

end NondualOpt


