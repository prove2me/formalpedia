-- Prove2me | Definitions.Def_LogRegretOCO_EWOO_shrunkSet
-- name    : LogRegretOCO_EWOO_shrunkSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:43:04.555964+00:00
-- url     : https://prove2.me/theorems/614d69c8-802d-4399-b92b-c179c72dceb8
-- title:
--   The shrunken set S = {T/(T+1) x* + 1/(T+1) y : y ∈ P} (§3.4)
-- statement:
--   Let $P \subseteq \mathbb{R}^n$, $x^* \in \mathbb{R}^n$ and $T \in \mathbb{N}$. The set of **nearby points** around $x^*$ is
--
--   $$
--   S = \Bigl\{ \tfrac{T}{T+1}\, x^* + \tfrac{1}{T+1}\, y \;:\; y \in P \Bigr\},
--   $$
--
--   the image of $P$ under the homothety with centre $x^*$ and ratio $1/(T+1)$. It is a translate of $\frac{1}{T+1}P$, and when $P$ is convex and $x^* \in P$ it is contained in $P$.
--
--   In the proof of Theorem 7 this set (following Blum and Kalai) carries a lower bound on the product of the functions $e^{-\alpha f_\tau}$ in terms of their value at $x^*$, and its volume is an explicit fraction of the volume of $P$.
--
--   **Formalization Note** The paper prints the definition as $S = \{x \in S \mid x = \tfrac{T}{T+1}x^* + \tfrac{1}{T+1}y,\ y \in P\}$, which defines $S$ in terms of itself; the intended set, used here, is the set of all such $x$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 187, §3.4, proof of Theorem 7 (display defining S)

import Mathlib

namespace LogRegretOCO.EWOO

/-- The set of "nearby points" in the proof of Theorem 7 (Hazan–Agarwal–Kale 2007, §3.4,
p. 187): `S = {T/(T+1) x* + 1/(T+1) y : y ∈ P}`, the image of `P` under the homothety with
centre `x*` and ratio `1/(T+1)`. -/
def shrunkSet {n : ℕ} (P : Set (EuclideanSpace ℝ (Fin n))) (xstar : EuclideanSpace ℝ (Fin n))
    (T : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∃ y ∈ P, x = ((T : ℝ) / ((T : ℝ) + 1)) • xstar + (1 / ((T : ℝ) + 1)) • y}

end LogRegretOCO.EWOO


