-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_ScaledNoise
-- name    : BorkarMeynODE_Tapering_ScaledNoise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:41:09.359673+00:00
-- url     : https://prove2.me/theorems/15fc74f2-5255-4312-ab41-402201c9f10a
-- title:
--   Scaled iterates $\tilde X(n)$, scaled noise $\tilde M(n+1)$, and the noise sum $\xi(n)$
-- statement:
--   Keep the notation of the scaled interpolation: blocks $m(j)$ and block scales $r(j)=\max(1,\|X(m(j))\|)$. For $j\ge0$ and $m(j)\le n<m(j+1)$ define the **scaled iterates** and the **scaled noise**
--   $$
--   \tilde X(n) = \frac{X(n)}{r(j)}, \qquad \tilde M(n+1) = \frac{M(n+1)}{r(j)},
--   $$
--   and the **scaled noise sum**
--   $$
--   \xi(n) = \sum_{m=0}^{n-1} a(m)\,\tilde M(m+1), \qquad n\ge 0 .
--   $$
--   These quantities appear in Lemma 4.5, where $\xi$ is shown to be an $L^2$-bounded martingale under (TS); its almost sure convergence then controls the noise in the comparison of Lemma 4.6.
--
--   **Formalization Note** Defined along sample paths `x` of $X$ and `mseq` of $M$. The paper defines $\xi(n)$ for $n\ge1$; here $\xi(0)=0$ is the empty sum. $\tilde M(0)$ is not used by the paper and is set to $0$.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 462, definitions of tilde X, tilde M and xi (before Lemma 4.5)

import Mathlib
import Definitions.Def_BorkarMeynODE_Tapering_TimeGrid
import Definitions.Def_BorkarMeynODE_Tapering_ScaledInterpolation

namespace BorkarMeynODE.Tapering

/-- The scaled iterates `X̃(n) = X(n)/r(j)` for `m(j) ≤ n < m(j+1)` (p. 462), along the sample
path `x`. -/
noncomputable def scaledIterate {d : ℕ} (a : ℕ → ℝ) (T : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (n : ℕ) : EuclideanSpace ℝ (Fin d) :=
  (blockScale a T x (blockOfIndex a T n))⁻¹ • x n

/-- The scaled noise (p. 462): `M̃(n+1) = M(n+1)/r(j)` for `m(j) ≤ n < m(j+1)`, along the
sample paths `x` of `X` and `mseq` of `M`. The paper does not use `M̃(0)`; it is set to `0`. -/
noncomputable def scaledNoise {d : ℕ} (a : ℕ → ℝ) (T : ℝ)
    (x mseq : ℕ → EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => 0
  | n + 1 => (blockScale a T x (blockOfIndex a T n))⁻¹ • mseq (n + 1)

/-- The scaled noise sum (p. 462): `ξ(n) = ∑_{m=0}^{n-1} a(m) M̃(m+1)` (so `ξ(0) = 0`). -/
noncomputable def noiseSum {d : ℕ} (a : ℕ → ℝ) (T : ℝ)
    (x mseq : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : EuclideanSpace ℝ (Fin d) :=
  ∑ m ∈ Finset.range n, a m • scaledNoise a T x mseq (m + 1)

end BorkarMeynODE.Tapering


