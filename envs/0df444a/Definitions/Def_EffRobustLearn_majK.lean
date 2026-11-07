-- Prove2me | Definitions.Def_EffRobustLearn_majK
-- name    : EffRobustLearn_majK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:27.720995+00:00
-- url     : https://prove2.me/theorems/5cab0638-db27-4feb-a1b8-c839e96caee8
-- title:
--   Rademacher law $\mathrm{Rad}(t)$ and the expected majority vote $\mathrm{maj}_k$ (2.2)
-- statement:
--   For $t\in[-1,1]$, $\mathrm{Rad}(t)$ assigns probabilities $(1+t)/2$ and $(1-t)/2$ to $1$ and $-1$. For an integer $k\ge1$, the expected majority vote of $k$ independent draws is
--   $$\mathrm{maj}_k(t)=\mathbb E_{z_1,\dots,z_k\sim\mathrm{Rad}(t)}\Big[\mathrm{sign}\Big(\frac1k\sum_{i=1}^k z_i\Big)\Big].$$
--
--   Algorithm 1 sets $h_t=\mathrm{maj}_k\circ\bar\mu_t$.
--
--   **Formalization Note** The expectation is the exact finite sum over the $2^k$ outcomes, each with its product probability.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), §2 and eq. (2.2), p.11 (PDF p.12)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_signPM

namespace EffRobustLearn

/-- The point mass of `Rad(t)` at the sign `z` (`true` is `+1`), Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), §2, p.11: `Rad(t)` assigns probabilities `(1 + t)/2` and `(1 - t)/2` to `1` and `-1`. -/
noncomputable def radPmf (t : ℝ) (z : Bool) : ℝ := (1 + t * pm z) / 2

/-- The expected majority vote (2.2), p.11:
`maj_k(t) = E_{z_1,…,z_k ∼ Rad(t)} [ sign((1/k) ∑_i z_i) ]`.

**Formalization Note.** The expectation is the exact finite sum over the `2^k` outcomes `z : Fin k → Bool`, each with its
product probability. The paper defines `maj_k` for an integer `k ≥ 1` and `t ∈ [-1, 1]`, the only arguments used. Sign per `signPM`
(`sign 0 = +1`). -/
noncomputable def majK (k : ℕ) (t : ℝ) : ℝ :=
  ∑ z : Fin k → Bool, (∏ i, radPmf t (z i)) * signPM ((1 / (k : ℝ)) * ∑ i, pm (z i))

end EffRobustLearn


