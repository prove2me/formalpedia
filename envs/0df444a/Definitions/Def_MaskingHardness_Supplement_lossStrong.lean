-- Prove2me | Definitions.Def_MaskingHardness_Supplement_lossStrong
-- name    : MaskingHardness_Supplement_lossStrong
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:28:22.536837+00:00
-- url     : https://prove2.me/theorems/bf4c689d-5b88-40c5-970b-a82b5fd277c0
-- title:
--   Strong hinge loss $\ell_{\mathrm{strong}}(e_i,a)=\max_j(e_i-\pi(a))_j$ (Definition 5.1)
-- statement:
--   For a label $i\in[k]$ and a mean-zero action $a\in\mathbb R^k$, the **strong hinge loss** is $\ell_{\mathrm{strong}}(e_i,a)=\max_{j\in[k]}(e_i-a)_j$. A general action is first centered:
--
--   $$
--   \ell_{\mathrm{strong}}(e_i,a)=\max_{j\in[k]}\big(e_i-\pi(a)\big)_j .
--   $$
--
--   It is a pointwise upper bound on the weak hinge loss, and its hardness is characterized by the fidelity $\mathbb E[\langle y,W(x)y\rangle]$ of masking channels (Theorem 1.12).
--
--   **Formalization Note** The maximum over the nonempty finite set $[k]$ is the real supremum over `Fin k` (nonempty because a label $i$ exists).
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 5.1, p.24 (PDF p.26); also p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MaskingHardness_centered

namespace MaskingHardness.Supplement

/-- **Strong hinge loss** `ℓstrong` (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 5.1, printed p.24 = PDF p.26; also p.8 =
PDF p.10): for a label `i ∈ [k]` and a mean-zero action `a ∈ ℝᵏ`,
`ℓstrong(e_i, a) = max_{j ∈ [k]} (e_i − a)_j`; a general `a` is centered first, so
`ℓstrong(e_i, a) = max_j (e_i − π(a))_j`.

**Formalization Note** The label `e_i` is the index `i : Fin k` and `(e_i)_j` is
`if j = i then 1 else 0`. The maximum is the real `⨆ j : Fin k`; since a label `i : Fin k`
exists, `Fin k` is nonempty and finite, so the supremum is the maximum of finitely many
reals. -/
noncomputable def lossStrong {k : ℕ} (i : Fin k) (a : Fin k → ℝ) : ℝ :=
  ⨆ j : Fin k, ((if j = i then (1 : ℝ) else 0) - MaskingHardness.centered a j)

end MaskingHardness.Supplement


