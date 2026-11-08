-- Prove2me | Definitions.Def_LowDimMeanEst_ChernoffF
-- name    : LowDimMeanEst_ChernoffF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:51:26.27421+00:00
-- url     : https://prove2.me/theorems/40d4f674-ac71-4957-a783-ce89f353c18f
-- title:
--   The linearized error functional $F(x,A,z,a,b,t)$ (Definition 10)
-- statement:
--   Fix $\delta$, $\eta$ and a vector $\mu\in\mathbb R^d$. For samples $x=(x_1,\dots,x_n)$, a matrix $A$, a direction $z$ and reals $a,b,t$, write $m_i=\min(1,x_i^\top Ax_i)$ and define
--
--   $$\begin{aligned}F(x,A,z,a,b,t)={}&a\Big(\sum_i m_i-\tfrac13\log\tfrac1\delta\Big)+b\Big(\sum_i(1-m_i)\,x_i^\top Ax_i-\mathrm{Tr}(A)\sum_i(1-m_i)(x_i\cdot z)^2\Big)\\&+t\Big(\frac1n\sum_i(1-m_i)(x_i\cdot z)-\Big((1+\eta)\sqrt{\tfrac{2\log(1/\delta)}n}+\mu\cdot z\Big)\Big).\end{aligned}$$
--
--   This is the left-hand side of (12). It linearizes the event "the trimmed mean errs by more than $(1+\eta)\sqrt{2\log(1/\delta)/n}$ in direction $z$ and $A$ is the trimming matrix", and is the quantity to which the Chernoff bounds of Lemmas 9 and 12 apply.
--
--   **Formalization Note** The paper leaves $n$, $\delta$, $\eta$ implicit; here $\delta$, $\eta$, $\mu$ are explicit arguments and $n$ is the number of samples.
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Definition 10 and display (12), p.16

import Mathlib
import Definitions.Def_LowDimMeanEst_Basic

namespace LowDimMeanEst

/-!
# The linearized error functional F (Definition 10)

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…), Definition 10, p.16: "Define F(x, A, z, a, b, t) as a
function representing the left-hand side of inequality in the probability term of (12), where x
represents n samples in ℝᵈ, A ∈ ℝ^{d×d}, z ∈ ℝᵈ, and a, b, t ∈ ℝ." The left-hand side of (12) is

  a(Σᵢ min(1, xᵢ⊤Axᵢ) − (1/3) log(1/δ))
  + b(Σᵢ (1 − min(1, xᵢ⊤Axᵢ)) xᵢ⊤Axᵢ − Tr(A) Σᵢ (1 − min(1, xᵢ⊤Axᵢ))(xᵢ · z)²)
  + t((1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ))(xᵢ · z) − ((1 + η)√(2 log(1/δ)/n) + µ · z)).

**Formalization Note.** "n, δ, and η are implicit parameters" (p.16), and so is the mean `µ`; here
`δ`, `η` and `µ` (`mu`) are explicit arguments and `n` is the length of the sample vector
`x : Fin n → E d`.
-/

/-- `F(x, A, z, a, b, t)` of Definition 10, with `δ`, `η`, `µ` explicit. -/
noncomputable def chernoffF {d n : ℕ} (δ η : ℝ) (mu : E d) (x : Fin n → E d) (A : E d →L[ℝ] E d)
    (z : E d) (a b t : ℝ) : ℝ :=
  a * (∑ i, trim A (x i) - logInv δ / 3) +
    b * (∑ i, (1 - trim A (x i)) * quad A (x i) -
      tr A * ∑ i, (1 - trim A (x i)) * (inner ℝ (x i) z) ^ 2) +
    t * ((1 / (n : ℝ)) * ∑ i, (1 - trim A (x i)) * inner ℝ (x i) z -
      ((1 + η) * Real.sqrt (2 * logInv δ / n) + inner ℝ mu z))

end LowDimMeanEst


