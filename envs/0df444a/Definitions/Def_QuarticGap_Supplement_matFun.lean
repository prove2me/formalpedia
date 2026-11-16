-- Prove2me | Definitions.Def_QuarticGap_Supplement_matFun
-- name    : QuarticGap_Supplement_matFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:52:13.487192+00:00
-- url     : https://prove2.me/theorems/8bd35749-c226-422a-a03e-4a202c4f71d3
-- title:
--   Matrix functions $g(P_W)$ and the constants (19)
-- statement:
--   Let $g$ be a complex function, analytic near $1$, with Taylor coefficients $a_k = g^{(k)}(1)/k!$, so that $g(1+z) = \sum_{k\ge0} a_k z^k$. For $t_* > 0$ the constants of (19) are
--   $$
--   A_g = \sum_{k\ge1}|a_{2k}|(65t_*^2)^{k-1},\quad B_g = \sum_{k\ge2}|a_{2k}|\,65^{k-1}t_*^{2k-4},\quad L_g = \sum_{k\ge0}|a_{2k+1}|(65t_*^2)^{k},\quad L_g' = \sum_{k\ge1}|a_{2k+1}|\,3^k t_*^{2k-2},
--   $$
--   $$
--   K_g = 2|a_0|A_g + 65t_*^2A_g^2 + L_g^2,\qquad c_g = \frac{|a_2|^2}{|a_0|^2},\qquad M_g = \frac{4B_g(A_g+|a_2|)}{|a_0|^2} + \frac{12|a_2|^2K_g}{|a_0|^4}.
--   $$
--   The matrix function is $g(P_W) = \sum_{k\ge0} a_k(-tT_W)^k$, and the output vector of Theorem 5.5 is $g(P_W)b$ with $b = (u,0,0)$.
--
--   These constants control the terms of even order, the terms of even order beyond two, the terms of odd order, the deviation of the squared norm of the output, and the error of the transfer theorem in the proof of Theorem 5.5.
--
--   **Formalization Note** The series are tsums of nonnegative reals, reindexed to start at $0$; under the hypotheses of Theorem 5.5 ($9t_* < r_g$) they converge. $g(P_W)$ is the power series, which on the promise set ($\|tT_W\| \le 9t < r_g$) converges absolutely to the matrix function of the symmetric matrix $P_W$; statements use it only there.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), §5.3, (19), p.35; proof of Theorem 5.5, p.36

import Mathlib
import Definitions.Def_QuarticGap_Supplement_Pmat

open QAlgorithms

namespace QuarticGap.Supplement

/-- The Taylor coefficient `a_k = g^{(k)}(1)/k!` of `g` at `1`, so that `g(1 + z) = ∑_k a_k z^k` near
`0` (arXiv:2610.42069 (file sha256 9f68aaf9…), §5.3, p.35). -/
noncomputable def taylorA (g : ℂ → ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv k g 1 / (k.factorial : ℂ)

/-- `A_g = ∑_{k≥1} |a_{2k}| (65 t∗²)^{k−1}` of (19) (arXiv:2610.42069, p.35), reindexed from `k = 0`. -/
noncomputable def Ag (g : ℂ → ℂ) (ts : ℝ) : ℝ :=
  ∑' k : ℕ, ‖taylorA g (2 * (k + 1))‖ * (65 * ts ^ 2) ^ k

/-- `B_g = ∑_{k≥2} |a_{2k}| 65^{k−1} t∗^{2k−4}` of (19) (arXiv:2610.42069, p.35), reindexed from
`k = 0`. -/
noncomputable def Bg (g : ℂ → ℂ) (ts : ℝ) : ℝ :=
  ∑' k : ℕ, ‖taylorA g (2 * (k + 2))‖ * 65 ^ (k + 1) * ts ^ (2 * k)

/-- `L_g = ∑_{k≥0} |a_{2k+1}| (65 t∗²)^k` of (19) (arXiv:2610.42069, p.35). -/
noncomputable def Lg (g : ℂ → ℂ) (ts : ℝ) : ℝ :=
  ∑' k : ℕ, ‖taylorA g (2 * k + 1)‖ * (65 * ts ^ 2) ^ k

/-- `L′_g = ∑_{k≥1} |a_{2k+1}| 3^k t∗^{2k−2}` of (19) (arXiv:2610.42069, p.35), reindexed from
`k = 0`. -/
noncomputable def Lg' (g : ℂ → ℂ) (ts : ℝ) : ℝ :=
  ∑' k : ℕ, ‖taylorA g (2 * (k + 1) + 1)‖ * 3 ^ (k + 1) * ts ^ (2 * k)

/-- `K_g = 2|a₀|A_g + 65 t∗² A_g² + L_g²` of (19) (arXiv:2610.42069, p.35). -/
noncomputable def Kg (g : ℂ → ℂ) (ts : ℝ) : ℝ :=
  2 * ‖taylorA g 0‖ * Ag g ts + 65 * ts ^ 2 * Ag g ts ^ 2 + Lg g ts ^ 2

/-- `c_g = |a₂|²/|a₀|²` of (19) (arXiv:2610.42069, p.35). -/
noncomputable def cg (g : ℂ → ℂ) : ℝ :=
  ‖taylorA g 2‖ ^ 2 / ‖taylorA g 0‖ ^ 2

/-- `M_g = 4B_g(A_g + |a₂|)/|a₀|² + 12|a₂|²K_g/|a₀|⁴` (arXiv:2610.42069, p.35). -/
noncomputable def Mg (g : ℂ → ℂ) (ts : ℝ) : ℝ :=
  4 * Bg g ts * (Ag g ts + ‖taylorA g 2‖) / ‖taylorA g 0‖ ^ 2 +
    12 * ‖taylorA g 2‖ ^ 2 * Kg g ts / ‖taylorA g 0‖ ^ 4

/-- The matrix function `g(P_W) = ∑_k a_k (P_W − I)^k = ∑_k a_k (−tT_W)^k` (arXiv:2610.42069, §5.3,
p.35, and proof of Theorem 5.5, p.36), as a complex matrix.

**Formalization Note** The source uses this series on `G`, where `∥tT_W∥ ≤ 9t < r_g` and it converges
absolutely to the matrix function of the Hermitian matrix `P_W`; every statement uses it only for
`W ∈ G`. Off `G` the Lean value of a non-summable series is `0`. -/
noncomputable def gMat {ℓ : ℕ} (g : ℂ → ℂ) (t : ℚ) (W : SignMat ℓ) : Matrix (Ix3 ℓ) (Ix3 ℓ) ℂ :=
  ∑' k : ℕ, taylorA g k • ((-(t : ℂ)) • (Tmat W).map (fun x : ℝ => (x : ℂ))) ^ k

/-- The output vector `g(P_W)b` of Theorem 5.5 (arXiv:2610.42069, p.35), `b = (u, 0, 0)`. -/
noncomputable def gVec {ℓ : ℕ} (g : ℂ → ℂ) (t : ℚ) (W : SignMat ℓ) : Ix3 ℓ → ℂ :=
  (gMat g t W).mulVec (fun i => (bVec ℓ i : ℂ))

end QuarticGap.Supplement


