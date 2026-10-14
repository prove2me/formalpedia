-- Prove2me | Definitions.Def_ThomsonCampaign_Polynomials
-- name    : ThomsonCampaign_Polynomials
-- status  : Definition
-- author  : @vatsj
-- created : 2026-10-13T22:05:42.712869+00:00
-- url     : https://prove2.me/theorems/64a22f74-46f6-43ed-8e4b-3b4cc0d8b3ec
-- title:
--   Legendre polynomials and the three-point kernel $Q_k$
-- statement:
--   `legendreP k t` is the Legendre polynomial $P_k(t)$, defined by $P_0 = 1$, $P_1 = t$ and Bonnet's recurrence $(k+2)P_{k+2}(t) = (2k+3)\,t\,P_{k+1}(t) - (k+1)P_k(t)$.
--
--   `threePointQ k u v t` is the polynomial
--   $$Q_k(u,v,t) = \sum_{j=0}^{\lfloor k/2\rfloor} (-1)^j \binom{k}{2j} s^{k-2j}\,(r^2 - s^2)^j, \qquad s = t - uv,\quad r^2 = (1-u^2)(1-v^2).$$
--   When $u, v, t$ are the inner products of three unit vectors, $r^k\cos(k\sigma) = Q_k(u,v,t)$, where $\sigma$ is the angle between the two outer vectors after projecting onto the plane orthogonal to the base vector. This is the kernel of the Bachoc–Vallentin three-point bound.
-- source:
--   C. Bachoc, F. Vallentin, New upper bounds for kissing numbers from semidefinite programming, J. Amer. Math. Soc. 21 (2008), https://arxiv.org/abs/math/0608426; H. Cohn, J. Woo, Three-point bounds for energy minimization, J. Amer. Math. Soc. 25 (2012), https://arxiv.org/abs/1103.0485.

import Mathlib

open Real

namespace ThomsonCampaign

/-- Legendre polynomials by Bonnet's recurrence `(k+1) P_{k+1} = (2k+1) t P_k - k P_{k-1}`. -/
noncomputable def legendreP : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => t
  | (k + 2), t => ((2 * (k : ℝ) + 3) * t * legendreP (k + 1) t - (k + 1) * legendreP k t) / (k + 2)

/-- `Q_k(u,v,t) = r^k cos(kσ)` where `s = t - uv`, `r² = (1-u²)(1-v²)` and `cos σ = s / r`,
written as the polynomial `∑_j (-1)^j C(k,2j) s^(k-2j) (r² - s²)^j`. -/
noncomputable def threePointQ (k : ℕ) (u v t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k / 2 + 1),
    (-1 : ℝ) ^ j * (Nat.choose k (2 * j) : ℝ) * (t - u * v) ^ (k - 2 * j) *
      ((1 - u ^ 2) * (1 - v ^ 2) - (t - u * v) ^ 2) ^ j

end ThomsonCampaign


