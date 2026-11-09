-- Prove2me | Definitions.Def_MaskingHardness_IsNoisyChannel
-- name    : MaskingHardness_IsNoisyChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:47.966976+00:00
-- url     : https://prove2.me/theorems/6238febd-5e4a-4bab-97a1-ca74cb6c55c7
-- title:
--   Noisy channel $W:\mathcal X\to\Delta_k^k$ (column-stochastic matrices)
-- statement:
--   Let $\Delta_k\subseteq\mathbb R^k$ be the probability simplex (nonnegative coordinates summing to $1$) and $\Delta_k^k$ the set of $k\times k$ **column-stochastic** matrices, whose columns lie in $\Delta_k$. Given a finite set $\mathcal X$ and labels $\mathcal Y=[k]$, a **noisy channel** is a function $W:\mathcal X\to\Delta_k^k$.
--
--   A label $y$ is identified with the standard basis vector $e_y$, so $W(x)y$ is the $y$-th column of $W(x)$: the distribution of the noisy label when the true label is $y$ and the features are $x$.
--
--   **Formalization Note** `W : X → Matrix (Fin k) (Fin k) ℝ`; the condition is that for all $x$ and $j$ the column `fun i => W x i j` lies in `stdSimplex ℝ (Fin k)`.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Definition 1.2, p.4 (PDF p.6)

import Mathlib

namespace MaskingHardness

/-- **Noisy channel** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*,
arXiv:2611.05296, held version sha256 31134e8d…3e8d, Definition 1.2, printed p.4 = PDF p.6): a
function `W : X → Δ_k^k`, i.e. every `W(x)` is a `k × k` column-stochastic matrix whose columns
lie in the probability simplex `Δ_k`.

**Formalization Note** A label `y ∈ [k]` is identified with the basis vector `e_y`, so `W(x)y`
is the `y`-th column `fun i => W x i y`. -/
def IsNoisyChannel {X : Type*} {k : ℕ} (W : X → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ x j, (fun i => W x i j) ∈ stdSimplex ℝ (Fin k)

end MaskingHardness


