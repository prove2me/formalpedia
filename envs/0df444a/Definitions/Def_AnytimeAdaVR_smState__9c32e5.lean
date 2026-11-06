-- Prove2me | Definitions.Def_AnytimeAdaVR_smState__9c32e5
-- name    : AnytimeAdaVR_smState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:44.129671+00:00
-- url     : https://prove2.me/theorems/9c32e5dd-01e2-4c10-b440-17665729b58c
-- title:
--   The continuing S or M path, block by block
-- statement:
--   An S or M path starts at $x=x_{\mathrm{init}}$ with $a=1$, $b=2$. Each block runs from the current point with the current $(a,b)$ on the next $b$ samples of the path's stream; the next block starts at the block's endpoint, with $(a,b)$ updated by Table 2, and if the block failed the stored point $Y$ is replaced by the block's candidate $y$.
--
--   The definition gives the state at the start of every block.
--
--   **Formalization Note** Blocks are indexed from $0$. The initial stored point is never read: a stored point is used as a label only when $b>2$, which first requires a failed block.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.1, p.7; Algorithm 2, p.8

import Mathlib
import Definitions.Def_AnytimeAdaVR_SMState
import Definitions.Def_AnytimeAdaVR_paramStep
import Definitions.Def_AnytimeAdaVR_blockOutcome

namespace AnytimeAdaVR

/-- **The continuing S or M path, block by block.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.1, p.7, and Algorithm 2, p.8:
"Each path starts at x = xinit and maintains a block length b = 2 and a scale a = 1. … In both cases,
the next block starts from x_{b+1}, with parameters updated by Table 2." and "if m < b/2 then Y ← y".

`smState k g xinit ξ j` is the state at the start of block `j` (0-based: `j = 0` is the paper's
block 1), for the optimization sample stream `ξ : ℕ → Ξ`, consumed in order: block `j` uses
`ξ (off_j), …, ξ (off_j + b_j − 1)`, one sample per step (the two queries of an M pair share it).

**Formalization Note.** The initial stored point `Y = xinit` is never read: a label `Y` is used
only when `b > 2`, which first requires a failed block, which overwrites `Y` (a failed block always
has its `y`; the fallback `getD` is never used). -/
noncomputable def smState {d : ℕ} {Ξ : Type*} (k : SMKind)
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ξ) : ℕ → SMState d
  | 0 => ⟨xinit, 1, 2, xinit, 0⟩
  | j + 1 =>
      let s := smState k g xinit ξ j
      let o := blockOutcome k g s.x s.a s.b (fun i => ξ (s.off + i))
      let p := paramStep k (s.a, s.b) o.2.1
      ⟨o.1, p.1, p.2, if 2 * o.2.1 < s.b then o.2.2.getD s.Y else s.Y, s.off + s.b⟩

end AnytimeAdaVR


