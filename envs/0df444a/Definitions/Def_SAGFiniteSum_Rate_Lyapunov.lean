-- Prove2me | Definitions.Def_SAGFiniteSum_Rate_Lyapunov
-- name    : SAGFiniteSum_Rate_Lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:21.174157+00:00
-- url     : https://prove2.me/theorems/0ecd23ff-9a28-4043-b354-6e0c9965d061
-- title:
--   App. B.2–B.5 — the Lyapunov function ℒ(θ), its B.5 constants, and the coefficients B₀–B₉, C₀–C₂ of the B.3 bound
-- statement:
--   **The Lyapunov function (App. B.2).** Let $e=(I;\dots;I)\in\mathbb R^{np\times p}$, so that $e^\top y=\sum_i y_i$, and $\theta^*=(f'(x^*),x^*)$ with $f'(x)=(f'_1(x);\dots;f'_n(x))$. For parameters $a_1,a_2,b,c,d,h$ and a state $\theta=(y,x)$,
--   $$
--   \mathcal L(\theta)=2h\,g(x+de^\top y)-2h\,g(x^*)+(\theta-\theta^*)^\top\begin{pmatrix}A&B\\B^\top&C\end{pmatrix}(\theta-\theta^*),\qquad A=a_1ee^\top+a_2I,\ B=be,\ C=cI .
--   $$
--   With $u_i=y_i-f'_i(x^*)$ and $w=x-x^*$ the quadratic form equals $a_1\|\sum_iu_i\|^2+a_2\sum_i\|u_i\|^2+2b\langle\sum_iu_i,w\rangle+c\|w\|^2$.
--
--   **The constants of B.5.** With step size $\alpha=\frac1{16L}$:
--   $$
--   a_1=\tfrac{1}{32nL}\big(1-\tfrac1{2n}\big),\quad a_2=\tfrac{1}{16nL}\big(1-\tfrac1{2n}\big),\quad b=-\tfrac1{4n}\big(1-\tfrac1n\big),\quad c=\tfrac{4L}n,\quad h=\tfrac12-\tfrac1n,\quad d=\tfrac\alpha n,
--   $$
--   $\delta=\min\big(\frac1{8n},\frac\mu{16L}\big)$ and $C_3=\frac1{32n}$. $\mathcal L$ with these constants is the Lyapunov function of the proof of Theorem 1.
--
--   **The coefficients of B.3.** For parameters $(\alpha,a_1,a_2,b,c,d,h,\delta)$, $n$, $L$ and $\mu$:
--   $$
--   \begin{aligned}
--   B_0&=2\delta h,\quad B_1=2\big(b-\tfrac\alpha nc\big),\quad B_2=2\big(\tfrac\alpha n-d\big)h,\\
--   B_3&=-\Big[\big(1-\tfrac2n\big)a_2+\tfrac1n\big[a_1+a_2-2\tfrac\alpha nb+\tfrac{\alpha^2}{n^2}c\big]-(1-\delta)a_2+Lh\tfrac1n\big(d-\tfrac\alpha n\big)^2\Big],\\
--   B_4&=B_3-n\Big[\big(1-\tfrac2n\big)\big(a_1-2\tfrac\alpha nb+\tfrac{\alpha^2}{n^2}c\big)-(1-\delta)a_1+L\big(1-\tfrac2n\big)h\big(d-\tfrac\alpha n\big)^2-(1-\delta)\mu hd^2\Big],\\
--   B_5&=2\Big[\big(\delta-\tfrac1n\big)b-\tfrac\alpha n\big(1-\tfrac1n\big)c\Big],\\
--   B_6&=-\tfrac2n\Big(hL\big(d-\tfrac\alpha n\big)^2+a_1-\tfrac{2\alpha}nb+\tfrac{\alpha^2}{n^2}c\Big),\\
--   B_7&=2\Big(hL\big(d-\tfrac\alpha n\big)^2+a_1-\tfrac{2\alpha}nb+\tfrac{\alpha^2}{n^2}c\Big)+2\Big(h\big(d-\tfrac\alpha n\big)\big(1-\tfrac1n\big)-h(1-\delta)d\Big),\\
--   B_8&=\tfrac1n\big(a_1+a_2-2\tfrac\alpha nb+\tfrac{\alpha^2}{n^2}c\big)+\tfrac Lnh\big(d-\tfrac\alpha n\big)^2,\qquad B_9=c\delta,
--   \end{aligned}
--   $$
--   and
--   $$
--   C_0=-B_0\tfrac\mu2+B_9+\tfrac n4\tfrac{B_5^2}{B_4},\quad
--   C_1=B_0+B_1+\tfrac{nL}4\tfrac{B_6^2}{B_3}+\tfrac{2n}4\tfrac{B_5(B_6+B_7)}{B_4}+nLB_8,\quad
--   C_2=-B_2-\tfrac n4\tfrac{B_6^2}{B_3}+\tfrac n4\tfrac{(B_6+B_7)^2}{B_4}.
--   $$
--   This $C_0$ (a coefficient of $\|x-x^*\|^2$) is not Theorem 1's initial constant $C_0$.
--
--   These coefficients express the one-step change of $\mathcal L$ in expectation (App. B.3), and the constraints of B.5 on them are what the constants above are chosen to satisfy.
--
--   **Formalization Note** The block quadratic form is written out in the expanded form above. The B.5 constants are functions of $n$ (cast to $\mathbb R$), $L$ and $\mu$; the parameters of B.3 are bundled in a structure `LyapParams`, and `sagParams n L μ` is the B.5 choice. The quotients $B_5^2/B_4$, $B_6^2/B_3$ use Lean's real division, which returns $0$ when the denominator is $0$; every theorem that uses them assumes $B_3,B_4>0$ or proves it.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.2 (ℒ, A, B, C), p. 37; App. B.3 (B₀–B₉), p. 40; (C₀, C₁, C₂), p. 41; App. B.5 (constants), p. 43

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- The general Lyapunov function of App. B.2 (p. 37), for a state `θ = (y, x)`:
`ℒ(θ) = 2h g(x + d eᵀy) − 2h g(x*) + (θ − θ*)ᵀ (A B; Bᵀ C) (θ − θ*)` with
`A = a₁eeᵀ + a₂I`, `B = be`, `C = cI`, `θ* = (f'(x*), x*)` and `e = (I; …; I)`.
Writing `uᵢ = yᵢ − f'ᵢ(x*)` and `w = x − x*`, the quadratic form is
`a₁‖∑ᵢ uᵢ‖² + a₂ ∑ᵢ ‖uᵢ‖² + 2b⟨∑ᵢ uᵢ, w⟩ + c‖w‖²`. -/
noncomputable def lyap {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (xstar : EuclideanSpace ℝ (Fin p)) (a1 a2 b c d h : ℝ)
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  2 * h * SAGA.Convex.fAvg f (θ.2 + d • ∑ i, θ.1 i) - 2 * h * SAGA.Convex.fAvg f xstar
    + (a1 * ‖∑ i, (θ.1 i - f' i xstar)‖ ^ 2 + a2 * ∑ i, ‖θ.1 i - f' i xstar‖ ^ 2
      + 2 * b * ⟪∑ i, (θ.1 i - f' i xstar), θ.2 - xstar⟫ + c * ‖θ.2 - xstar‖ ^ 2)

/-- B.5 (p. 43): `a₁ = (1/(32nL))(1 − 1/(2n))`. -/
noncomputable def sagA1 (n : ℕ) (L : ℝ) : ℝ := 1 / (32 * (n : ℝ) * L) * (1 - 1 / (2 * (n : ℝ)))

/-- B.5 (p. 43): `a₂ = (1/(16nL))(1 − 1/(2n))`. -/
noncomputable def sagA2 (n : ℕ) (L : ℝ) : ℝ := 1 / (16 * (n : ℝ) * L) * (1 - 1 / (2 * (n : ℝ)))

/-- B.5 (p. 43): `b = −(1/(4n))(1 − 1/n)`. -/
noncomputable def sagB (n : ℕ) : ℝ := -(1 / (4 * (n : ℝ))) * (1 - 1 / (n : ℝ))

/-- B.5 (p. 43): `c = 4L/n`. -/
noncomputable def sagC (n : ℕ) (L : ℝ) : ℝ := 4 * L / (n : ℝ)

/-- B.5 (p. 43): `h = 1/2 − 1/n`. -/
noncomputable def sagH (n : ℕ) : ℝ := 1 / 2 - 1 / (n : ℝ)

/-- B.5 (p. 43): the step size `α = 1/(16L)`. -/
noncomputable def sagAlpha (L : ℝ) : ℝ := 1 / (16 * L)

/-- B.5 (p. 43): `d = α/n`. -/
noncomputable def sagD (n : ℕ) (L : ℝ) : ℝ := sagAlpha L / (n : ℝ)

/-- B.5 (p. 43): `δ = min(1/(8n), μ/(16L))`. -/
noncomputable def sagDelta (n : ℕ) (L μ : ℝ) : ℝ := min (1 / (8 * (n : ℝ))) (μ / (16 * L))

/-- B.5 (p. 43): `C₃ = 1/(32n)`. -/
noncomputable def sagC3 (n : ℕ) : ℝ := 1 / (32 * (n : ℝ))

/-- The Lyapunov function of App. B.2 with the constants of B.5. -/
noncomputable def sagLyap {p n : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (L : ℝ)
    (xstar : EuclideanSpace ℝ (Fin p))
    (θ : (Fin n → EuclideanSpace ℝ (Fin p)) × EuclideanSpace ℝ (Fin p)) : ℝ :=
  lyap f f' xstar (sagA1 n L) (sagA2 n L) (sagB n) (sagC n L) (sagD n L) (sagH n) θ

/-- The algorithm parameter `α`, the six Lyapunov parameters `a₁, a₂, b, c, d, h` and the
rate parameter `δ` of App. B.2–B.3. -/
structure LyapParams where
  α : ℝ
  a1 : ℝ
  a2 : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  h : ℝ
  δ : ℝ

/-- The B.5 parameter choice (p. 43) as a `LyapParams`. -/
noncomputable def sagParams (n : ℕ) (L μ : ℝ) : LyapParams :=
  ⟨sagAlpha L, sagA1 n L, sagA2 n L, sagB n, sagC n L, sagD n L, sagH n, sagDelta n L μ⟩

/-- B.3 (p. 40): `B₀ = 2δh`. -/
noncomputable def coefB0 (P : LyapParams) : ℝ := 2 * P.δ * P.h

/-- B.3 (p. 40): `B₁ = 2(b − (α/n)c)`. -/
noncomputable def coefB1 (n : ℕ) (P : LyapParams) : ℝ := 2 * (P.b - P.α / (n : ℝ) * P.c)

/-- B.3 (p. 40): `B₂ = 2(α/n − d)h`. -/
noncomputable def coefB2 (n : ℕ) (P : LyapParams) : ℝ := 2 * (P.α / (n : ℝ) - P.d) * P.h

/-- B.3 (p. 40): `B₃ = −[(1 − 2/n)a₂ + (1/n)[a₁ + a₂ − 2(α/n)b + (α²/n²)c] − (1 − δ)a₂
+ Lh(1/n)(d − α/n)²]`. -/
noncomputable def coefB3 (n : ℕ) (L : ℝ) (P : LyapParams) : ℝ :=
  -((1 - 2 / (n : ℝ)) * P.a2
      + 1 / (n : ℝ) * (P.a1 + P.a2 - 2 * (P.α / (n : ℝ)) * P.b + P.α ^ 2 / (n : ℝ) ^ 2 * P.c)
      - (1 - P.δ) * P.a2 + L * P.h * (1 / (n : ℝ)) * (P.d - P.α / (n : ℝ)) ^ 2)

/-- B.3 (p. 40): `B₄ = B₃ − n[(1 − 2/n)(a₁ − 2(α/n)b + (α²/n²)c) − (1 − δ)a₁
+ L(1 − 2/n)h(d − α/n)² − (1 − δ)μhd²]`. -/
noncomputable def coefB4 (n : ℕ) (L μ : ℝ) (P : LyapParams) : ℝ :=
  coefB3 n L P
    - (n : ℝ) * ((1 - 2 / (n : ℝ)) * (P.a1 - 2 * (P.α / (n : ℝ)) * P.b + P.α ^ 2 / (n : ℝ) ^ 2 * P.c)
      - (1 - P.δ) * P.a1 + L * (1 - 2 / (n : ℝ)) * P.h * (P.d - P.α / (n : ℝ)) ^ 2
      - (1 - P.δ) * μ * P.h * P.d ^ 2)

/-- B.3 (p. 40): `B₅ = 2[(δ − 1/n)b − (α/n)(1 − 1/n)c]`. -/
noncomputable def coefB5 (n : ℕ) (P : LyapParams) : ℝ :=
  2 * ((P.δ - 1 / (n : ℝ)) * P.b - P.α / (n : ℝ) * (1 - 1 / (n : ℝ)) * P.c)

/-- B.3 (p. 40): `B₆ = −(2/n)(hL(d − α/n)² + a₁ − (2α/n)b + (α²/n²)c)`. -/
noncomputable def coefB6 (n : ℕ) (L : ℝ) (P : LyapParams) : ℝ :=
  -(2 / (n : ℝ)) * (P.h * L * (P.d - P.α / (n : ℝ)) ^ 2 + P.a1 - 2 * P.α / (n : ℝ) * P.b
      + P.α ^ 2 / (n : ℝ) ^ 2 * P.c)

/-- B.3 (p. 40): `B₇ = 2(hL(d − α/n)² + a₁ − (2α/n)b + (α²/n²)c)
+ 2(h(d − α/n)(1 − 1/n) − h(1 − δ)d)`. -/
noncomputable def coefB7 (n : ℕ) (L : ℝ) (P : LyapParams) : ℝ :=
  2 * (P.h * L * (P.d - P.α / (n : ℝ)) ^ 2 + P.a1 - 2 * P.α / (n : ℝ) * P.b
      + P.α ^ 2 / (n : ℝ) ^ 2 * P.c)
    + 2 * (P.h * (P.d - P.α / (n : ℝ)) * (1 - 1 / (n : ℝ)) - P.h * (1 - P.δ) * P.d)

/-- B.3 (p. 40): `B₈ = (1/n)(a₁ + a₂ − 2(α/n)b + (α²/n²)c) + (L/n)h(d − α/n)²`. -/
noncomputable def coefB8 (n : ℕ) (L : ℝ) (P : LyapParams) : ℝ :=
  1 / (n : ℝ) * (P.a1 + P.a2 - 2 * (P.α / (n : ℝ)) * P.b + P.α ^ 2 / (n : ℝ) ^ 2 * P.c)
    + L / (n : ℝ) * P.h * (P.d - P.α / (n : ℝ)) ^ 2

/-- B.3 (p. 40): `B₉ = cδ`. -/
noncomputable def coefB9 (P : LyapParams) : ℝ := P.c * P.δ

/-- B.3 (p. 41): `C₀ = −B₀(μ/2) + B₉ + (n/4)(B₅²/B₄)` (not Theorem 1's `C₀`). -/
noncomputable def coefC0 (n : ℕ) (L μ : ℝ) (P : LyapParams) : ℝ :=
  -(coefB0 P) * (μ / 2) + coefB9 P + (n : ℝ) / 4 * (coefB5 n P ^ 2 / coefB4 n L μ P)

/-- B.3 (p. 41): `C₁ = B₀ + B₁ + (nL/4)(B₆²/B₃) + (2n/4)(B₅(B₆ + B₇)/B₄) + nLB₈`. -/
noncomputable def coefC1 (n : ℕ) (L μ : ℝ) (P : LyapParams) : ℝ :=
  coefB0 P + coefB1 n P + (n : ℝ) * L / 4 * (coefB6 n L P ^ 2 / coefB3 n L P)
    + 2 * (n : ℝ) / 4 * (coefB5 n P * (coefB6 n L P + coefB7 n L P) / coefB4 n L μ P)
    + (n : ℝ) * L * coefB8 n L P

/-- B.3 (p. 41): `C₂ = −B₂ − (n/4)(B₆²/B₃) + (n/4)((B₆ + B₇)²/B₄)`. -/
noncomputable def coefC2 (n : ℕ) (L μ : ℝ) (P : LyapParams) : ℝ :=
  -(coefB2 n P) - (n : ℝ) / 4 * (coefB6 n L P ^ 2 / coefB3 n L P)
    + (n : ℝ) / 4 * ((coefB6 n L P + coefB7 n L P) ^ 2 / coefB4 n L μ P)

end SAGFiniteSum.Rate


