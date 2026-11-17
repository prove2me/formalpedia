-- Prove2me | Definitions.Def_HoneycombCodes_Supplement_wigner6j
-- name    : HoneycombCodes_Supplement_wigner6j
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:34:09.701227+00:00
-- url     : https://prove2.me/theorems/e84d0f1c-0f01-4f3c-96ea-c924bbea45f4
-- title:
--   Wigner $6j$ symbol by Racah's formula and the squared Racah factor $R^2_{\sigma\tau}$ of a box transfer
-- statement:
--   Spins are half-integers $j\in\tfrac12\mathbb N$. A triad $(a,b,c)$ is admissible when $a+b+c\in\mathbb Z$ and $|a-b|\le c\le a+b$. With $\Delta(a,b,c)=\sqrt{(a+b-c)!(a-b+c)!(-a+b+c)!/(a+b+c+1)!}$, the **Wigner $6j$ symbol** is given by Racah's formula
--
--   $$
--   \begin{Bmatrix} j_1 & j_2 & j_3\\ j_4 & j_5 & j_6\end{Bmatrix}
--   =\Delta(j_1j_2j_3)\Delta(j_1j_5j_6)\Delta(j_4j_2j_6)\Delta(j_4j_5j_3)\sum_t\frac{(-1)^t(t+1)!}{\prod_{i=1}^4(t-\alpha_i)!\prod_{k=1}^3(\beta_k-t)!},
--   $$
--
--   with $\alpha_1=j_1+j_2+j_3$, $\alpha_2=j_1+j_5+j_6$, $\alpha_3=j_4+j_2+j_6$, $\alpha_4=j_4+j_5+j_3$, $\beta_1=j_1+j_2+j_4+j_5$, $\beta_2=j_2+j_3+j_5+j_6$, $\beta_3=j_3+j_1+j_6+j_4$, summed over the integers $\max\alpha_i\le t\le\min\beta_k$; it is $0$ unless the four triads $(j_1j_2j_3)$, $(j_1j_5j_6)$, $(j_4j_2j_6)$, $(j_4j_5j_3)$ are admissible.
--
--   For the box transfer of type $(\sigma,\tau)$ leaving the triple $\omega=(i,j,\ell)$ at stabilizer type $(n-k,k)$, introduce the spins (26)
--
--   $$
--   a=\tfrac{n-i-1}{2}-(j-\sigma),\quad c=\tfrac{n-i}{2}-j,\quad d=\tfrac i2-\ell,\quad f=\tfrac{i+1}{2}-(\ell+\tau),\quad e=\tfrac n2-k,
--   $$
--
--   and set
--
--   $$
--   R^2_{\sigma\tau}=(2c+1)(2f+1)\begin{Bmatrix} a & \tfrac12 & c\\ d & e & f\end{Bmatrix}^2 .
--   $$
--
--   Only the square enters, so the phase convention of the $6j$ symbol is irrelevant. This is the recoupling factor of the exact transition coefficients of Theorem 4.4.
--
--   **Formalization Note** Spins are encoded by doubled values $2j\in\mathbb N$; on admissible triads every factorial argument is a natural number. $R^2_{\sigma\tau}$ is computed from the $6j$ symbol itself, not from the closed form of Remark 4.7 used by the published `HoneycombCodes.pDir`.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §4.3, eq. (26) and the definition of R_στ, p.18 (PDF 20); Racah's formula as in [VMK88, Ch. 9], cited on p.22 (PDF 24)

import Mathlib

set_option autoImplicit false

namespace HoneycombCodes.Supplement

/-- A **triad** of doubled spins `(2a, 2b, 2c)`: `a + b + c` is an integer and the triangle
inequalities `|a − b| ≤ c ≤ a + b` hold. This is the admissibility condition of each of the four
couplings of a Wigner 6j symbol (Racah's formula, cited in Gay, Granha Jeronimo, Liu, *The Honeycomb
Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), §4.3, p.18 (PDF 20), via
[VMK88, Ch. 9]).

**Formalization Note.** Spins `j ∈ ½ℕ` are encoded by `J = 2j ∈ ℕ`. -/
def IsTriad (A B C : ℕ) : Prop :=
  (A + B + C) % 2 = 0 ∧ A ≤ B + C ∧ B ≤ A + C ∧ C ≤ A + B

/-- The **triangle coefficient** `Δ(a, b, c) = √((a+b−c)!(a−b+c)!(−a+b+c)!/(a+b+c+1)!)` of
Racah's formula, on doubled spins (used only on triads, where every subtraction is exact). -/
noncomputable def triangleCoef (A B C : ℕ) : ℝ :=
  Real.sqrt (((A + B - C) / 2).factorial * ((A + C - B) / 2).factorial *
      ((B + C - A) / 2).factorial / ((A + B + C) / 2 + 1).factorial)

open Classical in
/-- The **Wigner 6j symbol** `{j₁ j₂ j₃; j₄ j₅ j₆}` by **Racah's formula** [VMK88, Ch. 9, eq. 9.2.1],
arXiv:2608.20287v2, §4.3, p.18 (PDF 20):

`{j₁ j₂ j₃; j₄ j₅ j₆} = Δ(j₁j₂j₃)Δ(j₁j₅j₆)Δ(j₄j₂j₆)Δ(j₄j₅j₃)
  Σ_t (−1)^t (t+1)! / [(t−α₁)!(t−α₂)!(t−α₃)!(t−α₄)!(β₁−t)!(β₂−t)!(β₃−t)!]`

with `α₁ = j₁+j₂+j₃`, `α₂ = j₁+j₅+j₆`, `α₃ = j₄+j₂+j₆`, `α₄ = j₄+j₅+j₃`, `β₁ = j₁+j₂+j₄+j₅`,
`β₂ = j₂+j₃+j₅+j₆`, `β₃ = j₃+j₁+j₆+j₄`, the sum over the integers `t` with
`max αᵢ ≤ t ≤ min βⱼ`; the symbol is `0` unless all four triads are admissible.

**Formalization Note.** Arguments are doubled spins `Jᵢ = 2jᵢ ∈ ℕ`; on admissible triads every
`αᵢ`, `βⱼ` is an integer and every factorial argument is a natural number, so `ℕ` subtraction is
exact on the summation range. The sign convention is Racah's; only the square enters this mission. -/
noncomputable def sixJ (J1 J2 J3 J4 J5 J6 : ℕ) : ℝ :=
  if IsTriad J1 J2 J3 ∧ IsTriad J1 J5 J6 ∧ IsTriad J4 J2 J6 ∧ IsTriad J4 J5 J3 then
    let a1 := (J1 + J2 + J3) / 2
    let a2 := (J1 + J5 + J6) / 2
    let a3 := (J4 + J2 + J6) / 2
    let a4 := (J4 + J5 + J3) / 2
    let b1 := (J1 + J2 + J4 + J5) / 2
    let b2 := (J2 + J3 + J5 + J6) / 2
    let b3 := (J3 + J1 + J6 + J4) / 2
    triangleCoef J1 J2 J3 * triangleCoef J1 J5 J6 * triangleCoef J4 J2 J6 *
        triangleCoef J4 J5 J3 *
      ∑ t ∈ Finset.Icc (max (max a1 a2) (max a3 a4)) (min b1 (min b2 b3)),
        (-1 : ℝ) ^ t * (t + 1).factorial /
          ((t - a1).factorial * (t - a2).factorial * (t - a3).factorial * (t - a4).factorial *
            (b1 - t).factorial * (b2 - t).factorial * (b3 - t).factorial)
  else 0

/-- The **squared Racah factor** of the box transfer of type `(σ, τ)` leaving `ω = (i, j, ℓ)` at
`(n, k)`, `R²_{στ} = (2c + 1)(2f + 1) {a ½ c; d e f}²` with the half-integer spins (26)
`a = (n−i−1)/2 − (j−σ)`, `c = (n−i)/2 − j`, `d = i/2 − ℓ`, `f = (i+1)/2 − (ℓ+τ)`, `e = n/2 − k`,
arXiv:2608.20287v2, §4.3, eq. (26) and the display after it, p.18 (PDF 20).

**Formalization Note.** Doubled spins `2a = n−i−1−2(j−σ)`, `2c = n−i−2j`, `2d = i−2ℓ`,
`2f = i+1−2(ℓ+τ)`, `2e = n−2k`, `2·½ = 1` in `ℕ`; on a forward edge between valid triples
(Theorem 4.4) all of them are nonnegative, so the truncated subtraction is exact there. The 6j
symbol is `sixJ` (Racah's formula), not the closed form of Remark 4.7. -/
noncomputable def RsqSixJ (n k : ℕ) (σ τ : Fin 2) (ω : ℕ × ℕ × ℕ) : ℝ :=
  let A := n - ω.1 - 1 - 2 * (ω.2.1 - σ.val)
  let Cc := n - ω.1 - 2 * ω.2.1
  let Dd := ω.1 - 2 * ω.2.2
  let Ff := ω.1 + 1 - 2 * (ω.2.2 + τ.val)
  let Ee := n - 2 * k
  ((Cc : ℝ) + 1) * ((Ff : ℝ) + 1) * sixJ A 1 Cc Dd Ee Ff ^ 2

end HoneycombCodes.Supplement


