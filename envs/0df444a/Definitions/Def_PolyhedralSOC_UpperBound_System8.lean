-- Prove2me | Definitions.Def_PolyhedralSOC_UpperBound_System8
-- name    : PolyhedralSOC_UpperBound_System8
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:45:56.72634+00:00
-- url     : https://prove2.me/theorems/7a581a7d-df72-4331-b1e8-8df374a2404e
-- title:
--   The system (8) approximating $L^2$ and its accuracy $\delta(\nu)$
-- statement:
--   Let $\nu$ be a natural number (the paper takes a positive integer). The system (8) is the following system of linear constraints in the variables $x_1,x_2,x_3$ and $\xi^j,\eta^j$, $j=0,\dots,\nu$:
--
--   (a) $\xi^0\ge|x_1|$, $\eta^0\ge|x_2|$;
--
--   (b) for $j=1,\dots,\nu$,
--   $$\xi^j=\cos\Big(\frac{\pi}{2^{j+1}}\Big)\xi^{j-1}+\sin\Big(\frac{\pi}{2^{j+1}}\Big)\eta^{j-1},\qquad \eta^j\ge\Big|-\sin\Big(\frac{\pi}{2^{j+1}}\Big)\xi^{j-1}+\cos\Big(\frac{\pi}{2^{j+1}}\Big)\eta^{j-1}\Big|;$$
--
--   (c) $\xi^\nu\le x_3$, $\eta^\nu\le\tan\big(\frac{\pi}{2^{\nu+1}}\big)\xi^\nu$.
--
--   Each $|a|\le b$ is two linear inequalities, so (8) is a system of homogeneous linear inequalities $\Pi^{(\nu)}(x_1,x_2,x_3,u)\ge0$ with $u$ the $2(\nu+1)$ variables $\xi^j,\eta^j$. Its accuracy is
--   $$\delta(\nu)=\frac{1}{\cos\big(\frac{\pi}{2^{\nu+1}}\big)}-1.$$
--
--   This is the building block of the construction: a polyhedral approximation of the three-dimensional cone $L^2$ of size linear in $\nu$ and accuracy decaying like $4^{-\nu}$.
--
--   **Formalization Note** The variables are sequences `ξ η : ℕ → ℝ`; entries with index above $\nu$ are unconstrained. The system is stated as a proposition with the absolute values written out, not as a matrix.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), §2, p. 199, system (8) and Eq. (9)

import Mathlib

namespace PolyhedralSOC.UpperBound

/-- The system of linear inequalities (8) of Ben-Tal & Nemirovski, *On Polyhedral
Approximations of the Second-Order Cone*, Math. Oper. Res. 26(2):193–205 (2001), §2,
p. 199 (PDF p. 7), with parameter `ν`, in the variables `x₁, x₂, x₃` and `ξ^j, η^j`
(`j = 0, …, ν`; `ξ j`, `η j` for `j > ν` are never constrained):
(a) `ξ^0 ≥ |x₁|`, `η^0 ≥ |x₂|`;
(b) `ξ^j = cos(π/2^{j+1}) ξ^{j−1} + sin(π/2^{j+1}) η^{j−1}`,
    `η^j ≥ |−sin(π/2^{j+1}) ξ^{j−1} + cos(π/2^{j+1}) η^{j−1}|`, `j = 1, …, ν`;
(c) `ξ^ν ≤ x₃`, `η^ν ≤ tan(π/2^{ν+1}) ξ^ν`. -/
def System8 (ν : ℕ) (x₁ x₂ x₃ : ℝ) (ξ η : ℕ → ℝ) : Prop :=
  (ξ 0 ≥ |x₁| ∧ η 0 ≥ |x₂|) ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ ν →
    ξ j = Real.cos (Real.pi / 2 ^ (j + 1)) * ξ (j - 1)
            + Real.sin (Real.pi / 2 ^ (j + 1)) * η (j - 1) ∧
    η j ≥ |-Real.sin (Real.pi / 2 ^ (j + 1)) * ξ (j - 1)
            + Real.cos (Real.pi / 2 ^ (j + 1)) * η (j - 1)|) ∧
  (ξ ν ≤ x₃ ∧ η ν ≤ Real.tan (Real.pi / 2 ^ (ν + 1)) * ξ ν)

/-- The accuracy `δ(ν) = 1 / cos(π/2^{ν+1}) − 1` of the system (8)
(Ben-Tal & Nemirovski 2001, Proposition 2.1, Eq. (9), p. 199 (PDF p. 7)). -/
noncomputable def delta (ν : ℕ) : ℝ :=
  1 / Real.cos (Real.pi / 2 ^ (ν + 1)) - 1

end PolyhedralSOC.UpperBound


