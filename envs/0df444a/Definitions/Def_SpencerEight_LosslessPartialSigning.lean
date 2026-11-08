-- Prove2me | Definitions.Def_SpencerEight_LosslessPartialSigning
-- name    : SpencerEight_LosslessPartialSigning
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:11.946961+00:00
-- url     : https://prove2.me/theorems/5b5264bb-ea4f-457a-9a32-d4b345b95a28
-- title:
--   Partial-signing statement of Lemma 8.3 at amplitude $s$
-- statement:
--   For every $m\ge1$, every symmetric convex $K\subseteq\mathbb R^m$ with $\gamma_m(K)\ge e^{-Em}$, and every $0<q<1$ with $\log2-E>h((1-q)/2)$, there is $y\in\{-1,0,1\}^m$ supported on more than $(1-q)m$ coordinates with $sy\in K$. Here $h$ is the binary entropy with natural logarithms, $h(0)=h(1)=0$.
--
--   **Formalization Note** No Borel condition on $K$, as in the source.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.3, p.71 (PDF p.71)

import Mathlib
import Definitions.Def_SpencerEight_gammaM

namespace SpencerEight

/-- The partial-signing statement of Lemma 8.3 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.71 (PDF p.71)) at amplitude `s`: if `K ⊆ ℝ^m` is symmetric and convex with `γ_m(K) ≥ e^{−Em}`, `0 < q < 1` and `log 2 − E > h((1 − q)/2)`, there is `y ∈ {−1, 0, 1}^m` supported on more than `(1 − q)m` coordinates with `s y ∈ K`.

**Formalization Note** `h` is `Real.binEntropy` (natural logarithms, `h(0) = h(1) = 0`). `m ≥ 1` as in the lemma's last sentence: at `m = 0` "more than `(1 − q)m` coordinates" cannot hold. No Borel condition, as printed: a convex set is null-measurable, and `gammaM` of it is its Gaussian mass. -/
def LosslessPartialSigning (s : ℝ) : Prop :=
  ∀ (m : ℕ) (K : Set (Fin m → ℝ)) (E q : ℝ), 1 ≤ m → Convex ℝ K → (∀ x ∈ K, -x ∈ K) →
    ENNReal.ofReal (Real.exp (-(E * m))) ≤ gammaM (Fin m) K →
    0 < q → q < 1 → Real.binEntropy ((1 - q) / 2) < Real.log 2 - E →
    ∃ y : Fin m → ℝ, (∀ i, y i = -1 ∨ y i = 0 ∨ y i = 1) ∧
      (1 - q) * m < ((Finset.univ.filter fun i => y i ≠ 0).card : ℝ) ∧
      s • y ∈ K

end SpencerEight


