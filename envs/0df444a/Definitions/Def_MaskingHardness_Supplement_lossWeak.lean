-- Prove2me | Definitions.Def_MaskingHardness_Supplement_lossWeak
-- name    : MaskingHardness_Supplement_lossWeak
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:27:48.737505+00:00
-- url     : https://prove2.me/theorems/1f3043c1-7db9-4573-aeb6-d826934a1152
-- title:
--   Weak hinge loss $\ell_{\mathrm{weak}}(e_i,a)=(1-\pi(a)_i)_+$ (Definition 5.1)
-- statement:
--   For a label $i\in[k]$, identified with the basis vector $e_i$, and a mean-zero action $a\in\mathbb R^k$, the **weak hinge loss** is $\ell_{\mathrm{weak}}(e_i,a)=(1-a_i)_+$. A general action is first centered, $\pi(a)=a-\tfrac1k\big(\sum_j a_j\big)\vec 1$, so
--
--   $$
--   \ell_{\mathrm{weak}}(e_i,a)=\big(1-\pi(a)_i\big)_+ ,\qquad (t)_+=\max(0,t).
--   $$
--
--   It is the loss whose hardness is characterized by dense measures masking the labels with uniform noise (Theorem 1.11).
--
--   **Formalization Note** $\pi$ is the published `MaskingHardness.centered`.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 5.1, p.24 (PDF p.26); also p.7 (PDF p.9)

import Mathlib
import Definitions.Def_MaskingHardness_centered

namespace MaskingHardness.Supplement

/-- **Weak hinge loss** `ℓweak` (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 5.1, printed p.24 = PDF p.26; also p.7 =
PDF p.9): for a label `i ∈ [k]` (the one-hot vector `e_i`) and a mean-zero action `a ∈ ℝᵏ`,
`ℓweak(e_i, a) = (1 − a_i)₊`; a general `a` is centered first, so
`ℓweak(e_i, a) = (1 − π(a)_i)₊`.

**Formalization Note** The label `e_i` is the index `i : Fin k`; `π` is the published
`MaskingHardness.centered`; `(t)₊ = max 0 t`. -/
noncomputable def lossWeak {k : ℕ} (i : Fin k) (a : Fin k → ℝ) : ℝ :=
  max 0 (1 - MaskingHardness.centered a i)

end MaskingHardness.Supplement


