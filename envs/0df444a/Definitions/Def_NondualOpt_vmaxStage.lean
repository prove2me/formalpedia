-- Prove2me | Definitions.Def_NondualOpt_vmaxStage
-- name    : NondualOpt_vmaxStage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:44.298431+00:00
-- url     : https://prove2.me/theorems/5f5d9fd8-c7d3-47c0-9c29-5fd1765a4dab
-- title:
--   The backward recursion of the deterministic max-regret game
-- statement:
--   Let $h=((x_1,z_1),\dots,(x_n,z_n))$ be a history of actions $x_s\in E$ and loss indices $z_s$. With $k$ rounds still to play, the **deterministic game value** after $h$ is defined by
--   $$
--   V_0(h)=R^{\max}_{X,n}\big((x_s)_s,(\ell_{z_s})_s\big),\qquad V_{k+1}(h)=\inf_{x\in X}\ \sup_{z\in Z_{X,H}}V_k\big(h,(x,z)\big).
--   $$
--   The player moves first in each round, then the adversary picks an affine loss.
--
--   **Formalization Note** Extended-real valued; infima and suprema range over $X$ and $Z_{X,H}$ as types, so there are no junk values.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (8), first line, p.9

import Mathlib
import Definitions.Def_NondualOpt_affineZ
import Definitions.Def_NondualOpt_affLoss
import Definitions.Def_NondualOpt_maxRegret

namespace NondualOpt

/-- The backward recursion defining the deterministic value of the affine max-regret game.
`vmaxStage pair X H k n h` is the value with `k` rounds still to play after the history
`h = ((x_1, z_1), …, (x_n, z_n))` of actions and loss indices: with no round left it is the
max-regret of `h`; otherwise the player chooses `x ∈ X`, then the adversary chooses
`z ∈ Z_{X,H}`: `inf_{x ∈ X} sup_{z ∈ Z_{X,H}} vmaxStage pair X H k (n+1) (h, (x, z))`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (8), first line, p.9.

**Formalization Note.** Valued in `EReal` (complete lattice: no junk values for empty or unbounded
ranges). Infima and suprema range over the subtypes `X` and `Z_{X,H}`. -/
noncomputable def vmaxStage {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) :
    (k n : ℕ) → (Fin n → E × (F × ℝ)) → EReal
  | 0, _, h => maxRegret X (fun t => (h t).1) (fun t u => affLoss pair (h t).2 u)
  | k + 1, n, h => ⨅ x : X, ⨆ z : affineZ pair X H,
      vmaxStage pair X H k (n + 1)
        (Fin.snoc (α := fun _ => E × (F × ℝ)) h ((x : E), (z : F × ℝ)))

end NondualOpt


