-- Prove2me | Definitions.Def_NondualOpt_vrandStage
-- name    : NondualOpt_vrandStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:51.673303+00:00
-- url     : https://prove2.me/theorems/76a5e435-ebf9-4a26-a2f4-ab368c5015a3
-- title:
--   The backward recursion of the randomized max-regret game
-- statement:
--   With $k$ rounds left after a history $h$ of length $n$, the **randomized (minimax-swapped) game value** is defined by
--   $$
--   W_0(h)=R^{\max}_{X,n}(h),\qquad W_{k+1}(h)=\sup_{r}\ \inf_{s}\ \mathbb E_{x\sim s,\ z\sim r}\,W_k\big(h,(x,z)\big),
--   $$
--   where the adversary first announces a law $r$ on $Z_{X,H}$, the player then picks a law $s$ on $X$, and $x,z$ are drawn independently.
--
--   **Formalization Note** The laws are finitely supported (footnote 6), so expectations are finite sums and no measurability is needed. Extended-real valued.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (8), second line, p.9

import Mathlib
import Definitions.Def_NondualOpt_affineZ
import Definitions.Def_NondualOpt_affLoss
import Definitions.Def_NondualOpt_maxRegret
import Definitions.Def_NondualOpt_FinLaw_expect

namespace NondualOpt

/-- The backward recursion of the randomized (minimax-swapped) affine max-regret game: with `k`
rounds left after the history `h`, the adversary announces a law `r` on `Z_{X,H}`, then the
player picks a law `s` on `X`, and `x ∼ s`, `z ∼ r` are drawn independently:
`sup_r inf_s E_{x ∼ s, z ∼ r} vrandStage pair X H k (n+1) (h, (x, z))`; with no round left it is
the max-regret of `h`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (8), second line (after ①), p.9.

**Formalization Note.** The laws are finitely supported (footnote 6, p.9), so expectations are
finite sums and no measurability is needed. `EReal`-valued. -/
noncomputable def vrandStage {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) :
    (k n : ℕ) → (Fin n → E × (F × ℝ)) → EReal
  | 0, _, h => maxRegret X (fun t => (h t).1) (fun t u => affLoss pair (h t).2 u)
  | k + 1, n, h => ⨆ r : FinLaw (affineZ pair X H), ⨅ s : FinLaw X,
      s.expect (fun x => r.expect (fun z =>
        vrandStage pair X H k (n + 1) (Fin.snoc (α := fun _ => E × (F × ℝ)) h (x, z))))

end NondualOpt


