-- Prove2me | Definitions.Def_MaskingHardness_Supplement_lossCS
-- name    : MaskingHardness_Supplement_lossCS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:28:43.391405+00:00
-- url     : https://prove2.me/theorems/9efd756b-be61-4f4d-ae66-2464caedbda6
-- title:
--   Crammer–Singer hinge loss $\ell_{\mathrm{CS}}(e_i,a)=(1-a_i+\max_{j\neq i}a_j)_+$ (Definition 5.1)
-- statement:
--   For a label $i\in[k]$ and an action $a\in\mathbb R^k$, the **Crammer–Singer hinge loss** is
--
--   $$
--   \ell_{\mathrm{CS}}(e_i,a)=\Big(1-\tilde a_i+\max_{j\neq i}\tilde a_j\Big)_+,\qquad \tilde a=\pi(a),
--   $$
--
--   the hinge of the margin by which the score of the correct label exceeds the largest wrong score. The formula is invariant under adding a constant vector to $a$, so centering does not change it. When $k=1$ the maximum over $j\neq i$ is empty, i.e. $-\infty$, and the loss is $0$.
--
--   Its hardness is characterized by the largest total variation distance of indistinguishable modified labels (Theorem 1.13).
--
--   **Formalization Note** The loss is written in the equivalent total form $1-\tilde a_i+\max_{j\in[k]}\big(\tilde a_j-[j=i]\big)$: since $\max_j(\tilde a_j-[j=i])=\max(\tilde a_i-1,\max_{j\neq i}\tilde a_j)$, this equals the displayed formula for $k\ge2$ and is $0$ for $k=1$, as the empty maximum $-\infty$ prescribes. A real supremum over the empty set $\{j\neq i\}$ (which Lean evaluates to $0$) is deliberately avoided.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 5.1, p.24 (PDF p.26); also p.8 (PDF p.10) and footnote 10

import Mathlib
import Definitions.Def_MaskingHardness_centered

namespace MaskingHardness.Supplement

/-- **Crammer–Singer hinge loss** `ℓCS` (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 5.1, printed p.24 = PDF p.26; also
p.8 = PDF p.10): for a label `i ∈ [k]` and a mean-zero action `a ∈ ℝᵏ`,
`ℓCS(e_i, a) = (1 − a_i + max_{j ≠ i} a_j)₊`; a general `a` is centered first (with
`ã = π(a)`, `ℓCS(e_i, a) = (1 − ã_i + max_{j≠i} ã_j)₊`, which equals the same formula in `a`
since it is invariant under adding a constant vector).

**Formalization Note** Lean writes the loss in the total form
`ℓCS(e_i, a) = 1 − ã_i + max_{j ∈ [k]} (ã_j − [j = i])`, where the maximum runs over all
`j` (a nonempty finite set). Since `max_j (ã_j − [j = i]) = max(ã_i − 1, max_{j≠i} ã_j)`, this
equals `max(0, 1 − ã_i + max_{j≠i} ã_j)`, the paper's formula, for `k ≥ 2`; for `k = 1` the
maximum over `j ≠ i` is empty, i.e. `−∞`, and both forms give `0`. (A real `⨆` over the
empty set `j ≠ i` would give `0` instead and is avoided.) -/
noncomputable def lossCS {k : ℕ} (i : Fin k) (a : Fin k → ℝ) : ℝ :=
  1 - MaskingHardness.centered a i +
    ⨆ j : Fin k, (MaskingHardness.centered a j - if j = i then (1 : ℝ) else 0)

end MaskingHardness.Supplement


