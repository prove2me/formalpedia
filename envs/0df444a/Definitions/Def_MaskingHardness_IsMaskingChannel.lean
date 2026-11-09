-- Prove2me | Definitions.Def_MaskingHardness_IsMaskingChannel
-- name    : MaskingHardness_IsMaskingChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:49:19.419075+00:00
-- url     : https://prove2.me/theorems/f3e37239-147f-43e8-bff6-f92f393ab055
-- title:
--   $(\mathcal C,\varepsilon)$-masking channel for a distribution $\mathcal D$
-- statement:
--   Let $\mathcal D$ be a distribution over $(x,y)\in\mathcal X\times[k]$, $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ a finite collection, and $\varepsilon\ge0$. A noisy channel $W:\mathcal X\to\Delta_k^k$ is a **$(\mathcal C,\varepsilon)$-masking channel** for $\mathcal D$ if for every $c\in\mathcal C$
--
--   $$
--   \Bigl|\,\mathbb E_{(x,y)\sim\mathcal D}\bigl[\langle c(x),\,W(x)y-\vec 1/k\rangle\bigr]\Bigr|\le\varepsilon ,
--   $$
--
--   where $\vec 1/k$ is the vector with all entries $1/k$ and $W(x)y$ is the $y$-th column of $W(x)$. The noisy label $W(x)y$ is then indistinguishable from the uniform label by the tests in $\mathcal C$, up to $\varepsilon$.
--
--   **Formalization Note** The expectation is the $\mathcal D$-weighted finite sum; $\mathcal C$ is an indexed family `c : ι → X → (Fin k → ℝ)`.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.3, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_MaskingHardness_IsNoisyChannel

namespace MaskingHardness

/-- **`(C, ε)`-masking channel** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking
Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.3, printed p.5 =
PDF p.7): a noisy channel `W : X → Δ_k^k` such that for all `c ∈ C`,
`|E_D[⟨c(x), W(x)y − 1⃗/k⟩]| ≤ ε`.

**Formalization Note** `D` is given by weights `D x y`, the expectation is the weighted finite
sum, `C` is an indexed family `c : ι → X → ℝᵏ`, `W(x)y` is the `y`-th column of `W(x)`, and `1⃗/k`
is the vector with all entries `1/k`. -/
def IsMaskingChannel {X ι : Type*} [Fintype X] {k : ℕ} (D : X → Fin k → ℝ)
    (c : ι → X → Fin k → ℝ) (ε : ℝ) (W : X → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  IsNoisyChannel W ∧
    ∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ (fun j => W x j y - (k : ℝ)⁻¹))| ≤ ε

end MaskingHardness


