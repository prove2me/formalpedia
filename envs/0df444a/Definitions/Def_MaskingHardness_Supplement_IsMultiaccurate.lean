-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsMultiaccurate
-- name    : MaskingHardness_Supplement_IsMultiaccurate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:29:36.074009+00:00
-- url     : https://prove2.me/theorems/4edeeb4d-b4fe-40fa-9b5b-8b8987e8610f
-- title:
--   $(\mathcal C,\varepsilon)$-multiaccuracy of a model (Definition 2.16)
-- statement:
--   Given finite $\mathcal X$, $\mathcal Y=[k]$, a distribution $\mathcal D$ over $(x,y)\in\mathcal X\times\mathcal Y$ and a collection $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$, a model $p:\mathcal X\to\Delta_k$ is **$(\mathcal C,\varepsilon)$-multiaccurate** if
--
--   $$
--   \Big|\,\mathbb E\big[\langle c(x),\,y-p(x)\rangle\big]\Big|\le\varepsilon\qquad\text{for all }c\in\mathcal C,
--   $$
--
--   with labels viewed as one-hot vectors. No test in $\mathcal C$ distinguishes the true label $y$ from a label simulated from $p(x)$ by more than $\varepsilon$. In Theorem 1.22 this is what "$p(x)$ is $(\mathcal C,\varepsilon)$-indistinguishable from $y$" means.
--
--   **Formalization Note** $\mathcal C$ is an indexed family `c : ι → X → Fin k → ℝ`, the label $y$ is `Pi.single y 1`, and the condition $p(x)\in\Delta_k$ is stated separately wherever the predicate is used.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 2.16, p.19 (PDF p.21); proof of Theorem 1.22, p.36 (PDF p.38)

import Mathlib

namespace MaskingHardness.Supplement

/-- **`(C, ε)`-multiaccuracy** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 2.16, printed p.19 = PDF p.21; read as
"`p(x)` is `(C, ε)`-indistinguishable from `y`" in Theorem 1.22, printed p.35 = PDF p.37, as its
proof on p.36 = PDF p.38 does): a model `p : X → Δ_k` is `(C, ε)`-multiaccurate if for all
`c ∈ C`, `|E[⟨c(x), y − p(x)⟩]| ≤ ε`.

**Formalization Note** `D` is given by weights `D x y` and the expectation is the weighted finite
sum; `C` is an indexed family `c : ι → X → ℝᵏ`; the label `y` is the one-hot vector
`Pi.single y 1`. Membership `p x ∈ Δ_k` is a separate hypothesis wherever the predicate is
used. -/
def IsMultiaccurate {X ι : Type*} [Fintype X] {k : ℕ} (D : X → Fin k → ℝ)
    (c : ι → X → Fin k → ℝ) (ε : ℝ) (p : X → Fin k → ℝ) : Prop :=
  ∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ ((Pi.single y (1 : ℝ) : Fin k → ℝ) - p x))| ≤ ε

end MaskingHardness.Supplement


