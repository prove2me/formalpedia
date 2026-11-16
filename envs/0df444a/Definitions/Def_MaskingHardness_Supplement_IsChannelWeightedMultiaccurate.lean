-- Prove2me | Definitions.Def_MaskingHardness_Supplement_IsChannelWeightedMultiaccurate
-- name    : MaskingHardness_Supplement_IsChannelWeightedMultiaccurate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:31:10.11417+00:00
-- url     : https://prove2.me/theorems/54260ee3-a164-4e30-9c11-16a50ae28f38
-- title:
--   Channel-weighted $(\mathcal C,\varepsilon)$-multiaccuracy (Definition 6.2)
-- statement:
--   Given finite $\mathcal X$, $\mathcal Y=[k]$, a distribution over $(x,y)$, a finite $\mathcal C\subseteq\{\mathcal X\to\mathbb R^k\}$ and a response $\widehat W_h:\Delta_k\to\Delta_k^k$, a model $p:\mathcal X\to\Delta_k$ satisfies **$\widehat W_h$-weighted $(\mathcal C,\varepsilon)$-multiaccuracy** if
--
--   $$
--   \Big|\,\mathbb E\big[\langle \widehat W_h(p(x))^{\top}c(x),\ y-p(x)\rangle\big]\Big|\le\varepsilon\qquad\text{for all }c\in\mathcal C .
--   $$
--
--   When $\widehat W_h(p(x))p(x)=\vec1/k$ this says that the channel $W(x)=\widehat W_h(p(x))$ is $\mathcal C$-masking.
--
--   **Formalization Note** $\mathcal C$ is an indexed family and the label $y$ is a one-hot vector.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 6.2, p.29 (PDF p.31)

import Mathlib
open Matrix

namespace MaskingHardness.Supplement

/-- **Channel-weighted multiaccuracy** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 6.2, printed p.29 = PDF p.31): given a
response `Ŵ_h : Δ_k → Δ_k^k`, a model `p : X → Δ_k` satisfies `Ŵ_h`-weighted `(C, ε)`-multiaccuracy
if for all `c ∈ C`, `|E[⟨Ŵ_h(p(x))ᵀ c(x), y − p(x)⟩]| ≤ ε`.

**Formalization Note** `D` is given by weights, `C` is an indexed family `c : ι → X → ℝᵏ`, the
label `y` is `Pi.single y 1`, `Ŵ_h(p(x))ᵀ c(x)` is `(What (p x))ᵀ *ᵥ c i x`. -/
def IsChannelWeightedMultiaccurate {X ι : Type*} [Fintype X] {k : ℕ} (D : X → Fin k → ℝ)
    (c : ι → X → Fin k → ℝ) (What : (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) (ε : ℝ)
    (p : X → Fin k → ℝ) : Prop :=
  ∀ i, |∑ x, ∑ y, D x y *
    (((What (p x))ᵀ *ᵥ c i x) ⬝ᵥ ((Pi.single y (1 : ℝ) : Fin k → ℝ) - p x))| ≤ ε

end MaskingHardness.Supplement


