-- Prove2me | Definitions.Def_MaskingHardness_constraintS
-- name    : MaskingHardness_constraintS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:45.158783+00:00
-- url     : https://prove2.me/theorems/889e4186-5535-4db9-9ac5-0b5843ddabf0
-- title:
--   Indistinguishability constraint functional $S(b)$ (Definition 3.1)
-- statement:
--   Let $\mathcal D$, $\mathcal C=\{c_i\}$ and $\varepsilon\ge0$ be as in Definition 3.1. For $b:\mathcal X\times\mathcal Y\to\mathbb R^k$,
--
--   $$
--   S(b)=\begin{cases}0 & \text{if } \bigl|\mathbb E[\langle c(x),b(x,y)\rangle]\bigr|\le\varepsilon \text{ for all } c\in\mathcal C,\\ -\infty & \text{otherwise.}\end{cases}
--   $$
--
--   $S$ is the concave functional enforcing that $b$ is approximately uncorrelated with every $c\in\mathcal C$.
--
--   **Formalization Note** The expectation is the $\mathcal D$-weighted finite sum; $\mathcal C$ is an indexed family.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 3.1, p.20 (PDF p.22)

import Mathlib

namespace MaskingHardness

open Classical in
/-- **The indistinguishability constraint functional `S`** (Gopalan–Prabhakaran–Tankala,
*Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d,
Definition 3.1, printed p.20 = PDF p.22): for `b : X × Y → ℝᵏ`,
`S(b) = 0` if `|E[⟨c(x), b(x, y)⟩]| ≤ ε` for all `c ∈ C`, and `S(b) = −∞` otherwise.

**Formalization Note** `C` is an indexed family `c : ι → X → ℝᵏ`; the expectation is the
`D`-weighted finite sum. -/
noncomputable def constraintS {X Y ι : Type*} [Fintype X] [Fintype Y] {k : ℕ} (D : X → Y → ℝ)
    (c : ι → X → Fin k → ℝ) (ε : ℝ) (b : X → Y → Fin k → ℝ) : EReal :=
  if ∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ b x y)| ≤ ε then 0 else ⊥

end MaskingHardness


