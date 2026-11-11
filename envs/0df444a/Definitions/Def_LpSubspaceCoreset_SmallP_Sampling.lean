-- Prove2me | Definitions.Def_LpSubspaceCoreset_SmallP_Sampling
-- name    : LpSubspaceCoreset_SmallP_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:46:27.845413+00:00
-- url     : https://prove2.me/theorems/e860d729-81d5-4694-a59e-0346ebc40f3c
-- title:
--   Sampling with replacement (Definition 2.3) and the law of the sample
-- statement:
--   Let $q$ be a probability distribution on $[N]$ and draw $I_1,\dots,I_m$ independently from $q$. The **sampling matrix** $S\in\mathbb R^{m\times N}$ has rows
--   $$S_{s,*}=(m\,q_{I_s})^{-1/p}\,e_{I_s}^\top,\qquad s\in[m],$$
--   so that $\|SM\|_{p,2}^p=\frac1m\sum_{s}\|z_{I_s}\|_2^p/q_{I_s}$ when $M$ has rows $z_i^\top$. The probability of an event $E$ of the sample is $\sum_{I\in[N]^m}\big(\prod_s q_{I_s}\big)\mathbf 1[E(I)]$, the product law $q^{\otimes m}$ on the finite set $[N]^m$. This is the sampling scheme of Theorem 3.1.
--
--   **Formalization Note** A sample is a function `Fin m → Fin N`; probabilities are finite sums, so no measurability question arises.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 9, Definition 2.3

import Mathlib

namespace LpSubspaceCoreset.SmallP

/-!
# Sampling with replacement (Definition 2.3) and its law

Lin, Mirrokni, Woodruff, arXiv:2608.26047, Definition 2.3, p. 9.

`q` is a probability distribution on `[N]` (`Fin N`); `I_1, …, I_m` are drawn independently from
`q`. A sample is a function `I : Fin m → Fin N`; its law is the product measure `q^{⊗m}` on the
finite set `[N]^m`, so the probability of an event `E` is the finite sum
`Σ_{I ∈ [N]^m} (Π_s q_{I_s}) · 1[E(I)]`. The sampling matrix `S ∈ ℝ^{m×N}` has rows
`S_{s,*} = (m q_{I_s})^{−1/p} e_{I_s}^⊤`.
-/

/-- `q` is a probability distribution on `[N]`. -/
def IsProbVec {N : ℕ} (q : Fin N → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1

/-- Definition 2.3: the sampling matrix of the sample `I`, with rows
`S_{s,*} = (m q_{I_s})^{−1/p} e_{I_s}^⊤`. -/
noncomputable def samplingMatrix {N m : ℕ} (p : ℝ) (q : Fin N → ℝ) (I : Fin m → Fin N) :
    Matrix (Fin m) (Fin N) ℝ :=
  fun s i => if i = I s then ((m : ℝ) * q (I s)) ^ (-1 / p) else 0

/-- The probability, under `m` independent draws from `q`, of the event `E` on samples. -/
noncomputable def sampleProb {N : ℕ} (q : Fin N → ℝ) (m : ℕ) (E : (Fin m → Fin N) → Prop) : ℝ :=
  by classical exact ∑ I : Fin m → Fin N, (∏ s, q (I s)) * if E I then 1 else 0

end LpSubspaceCoreset.SmallP


