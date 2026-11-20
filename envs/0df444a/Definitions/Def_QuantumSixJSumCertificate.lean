-- Prove2me | Definitions.Def_QuantumSixJSumCertificate
-- name    : QuantumSixJSumCertificate
-- status  : Definition
-- author  : @igor.kh
-- created : 2026-11-13T09:29:34.379816+00:00
-- url     : https://prove2.me/theorems/2fd44741-19e9-4588-82eb-f0ee9909da19
-- title:
--   Finite-sum weights and coefficients for the quantum Tet certificate
-- statement:
--   Auxiliary rational functions over $\mathbb Q(q)$ for the finite-sum certificate of the Appendix Tet recurrence. The bundle specifies the raw summand, common factorial weight, cleared three-term coefficients, flux multiplier, flux, raw and finite-sum residuals, finite summation length, Appendix prefactor, and clearing factor. The diagonal and two step-2 entry functions are branch-expanded expressions used for factorial shifts; their identification with the symmetric two-index matrix is a proof obligation, not assumed. All factorials retain their signed-index zero convention and division is total in the rational-function field. No identity or recurrence is assumed.
--
--   ### Independent mathematical read-back
--
--   # Read-back: finite-sum certificate declarations
--
--   ## Explicit notation used in the paragraphs
--
--   All scalar values below belong to the rational-function field $K=\mathbb Q(q)$, where $q$ is the image of the polynomial indeterminate. For every integer $n$, write
--   $$
--   [n]=\frac{q^n-q^{-n}}{q-q^{-1}},\qquad
--   F(n)=\begin{cases}0&n<0,\\ \prod_{r=1}^{n}[r]&n\geq0.\end{cases}
--   $$
--   In particular $F(0)=1$. Powers with integer exponents are field powers. All division and inversion are total field operations: $0^{-1}=0$ and $u/0=0$. All label subtraction is integer subtraction, not truncated subtraction. Every division of integer labels by $2$ means Euclidean integer division (for divisor $2$, the floor of the half), including when the numerator is negative or odd. No evaluation at a numerical value of $q$ is involved.
--
--   The predicate $T(u,v,w)$ means that $u,v,w$ are nonnegative integers, each is at most the sum of the other two, and $u+v+w$ is even. Write $H_r=T(a,d,r)\land T(b,c,r)$ and $V_s=T(a,b,s)\land T(c,d,s)$, always with the external labels $a,b,c,d$ of the paragraph in question. The following explicitly specified scalar expressions provide notation for expanded dependency quantities:
--   $$
--   \delta(r)=\begin{cases}(-1)^r[r+1]&r\geq0,\\0&r<0,\end{cases}\qquad
--   \vartheta(u,v,w)=\begin{cases}
--   \displaystyle\frac{(-1)^z F(z+1)F(z-u)F(z-v)F(z-w)}{F(u)F(v)F(w)},\quad z=(u+v+w)/2&T(u,v,w),\\
--   0&\text{otherwise},
--   \end{cases}
--   $$
--   $$
--   N_r=\begin{cases}\vartheta(a,d,r)\vartheta(b,c,r)/\delta(r)&H_r,\\0&\neg H_r,\end{cases}\qquad
--   E(u,v,w)=\begin{cases}
--   \displaystyle\frac{[(u-v+w)/2][(-u+v+w)/2]-[(u+v-w)/2][(u+v+w)/2+2]}{[2]}&T(u,v,w),\\0&\text{otherwise}.
--   \end{cases}
--   $$
--   For external integers $a,b,c,d$ and integer channels $r,s$, let the four-entry and three-entry lists be
--   $$
--   \alpha^{r,s}=\big((a+d+r)/2,(b+c+r)/2,(a+b+s)/2,(c+d+s)/2\big),\quad
--   \beta^{r,s}=\big((b+d+r+s)/2,(a+c+r+s)/2,(a+b+c+d)/2\big).
--   $$
--   List indices start at $0$. Put
--   $$
--   P_{r,s}=\frac{\prod_{i=0}^{3}\prod_{k=0}^{2}F(\beta_k^{r,s}-\alpha_i^{r,s})}{F(a)F(b)F(c)F(d)F(r)F(s)},
--   $$
--   $$
--   U_{r,s}=\frac{1}{N_r}\begin{cases}
--   \displaystyle P_{r,s}\sum_{z=0}^{a+b+c+d+r+s}
--   \frac{(-1)^zF(z+1)}{\big(\prod_{i=0}^{3}F(z-\alpha_i^{r,s})\big)\big(\prod_{k=0}^{2}F(\beta_k^{r,s}-z)\big)}&H_r\land V_s,\\
--   0&\text{otherwise}.
--   \end{cases}
--   $$
--   Here an integer-indexed sum from $0$ to a negative upper endpoint is empty and equals zero. Thus $U$ includes both the admissibility guard on the finite sum and total division by $N_r$; it is not a separate unspecified coefficient.
--
--   ## Declaration paragraphs
--
--   **`QuantumSixJ.diagonalEntry`.** For all integers $a,b,c,d,j$, this defines a scalar equal to $-N_j[2]E(a,j,d)E(b,j,c)/([j][j+2])$ if $H_j$ and $j\ne0$, and equal to zero otherwise, with $H,N,E$ expanded above. In particular the value at $j=0$ is zero even if both triples in $H_0$ satisfy the triangle and parity conditions; inadmissible and negative horizontal labels also take the zero branch. There is no additional nonvanishing or positivity hypothesis.
--
--   **`QuantumSixJ.Lp2`.** For all integers $a,b,c,d,j$, this defines the scalar $N_{j+2}[(a+d-j)/2][(b+c-j)/2]$ when both $H_j$ and $H_{j+2}$ hold, and zero otherwise, where $N$ is the explicitly guarded product of the two $\vartheta$ expressions divided by $\delta$ given above. Both horizontal channels must satisfy nonnegative triangle and even-sum conditions; no separate hypothesis restricts any input integer, and the formula includes $j=0$.
--
--   **`QuantumSixJ.Lm2`.** For all integers $a,b,c,d,j$, this defines the scalar $N_j[(a+d-(j-2))/2][(b+c-(j-2))/2]$ when both $H_j$ and $H_{j-2}$ hold, and zero otherwise, where $N$ is the explicitly guarded expression above. In particular $j=0$ and $j=1$ give zero because the channel $j-2$ is negative; neither subtraction is natural-number subtraction. There are no hypotheses on the input labels.
--
--   **`QuantumSixJ.Certificate.rawSummand`.** For any eight integers $A,B,C,D,E,F,G,S$, this defines the scalar
--   $$
--   \frac{(-1)^S F(S+1)}{F(S-A)F(S-B)F(S-C)F(S-D)F(E-S)F(F-S)F(G-S)}.
--   $$
--   Here $F(\cdot)$ denotes the explicitly defined signed-index quantum factorial above, while the bare letter $F$ inside an argument is the sixth integer parameter. There is no admissibility or support guard and no restriction $S\geq0$; a negative factorial argument in the denominator makes the quotient zero by total field division, and $S<-1$ makes the numerator factorial zero.
--
--   **`QuantumSixJ.Certificate.commonWeight`.** For any seven integers $A,B,C,E,F,j,S$, set $D=E+F-C-j$ and $G=A+B-j$; this defines the scalar
--   $$
--   (-1)^S F(S+1)\,F(S-A+1)^{-1}F(S-B+1)^{-1}F(S-C)^{-1}F(S-D)^{-1}F(E-S+1)^{-1}F(F-S+1)^{-1}F(G-S)^{-1}.
--   $$
--   The function $F(\cdot)$ is the signed-index quantum factorial, distinct from the integer parameter $F$. The definition has no hypotheses, including no support, admissibility, or positivity restriction, and inverses of zero factorial values are zero.
--
--   **`QuantumSixJ.Certificate.lowerCoefficient`.** For any integers $A,B,j$, this defines the scalar $[A-j+1][B-j+1][A+1][B+1][2][j+2]$, with every bracket the rational-function quotient specified above. There are no sign, parity, or nonzero assumptions on the parameters; the definition includes $j=0$ and negative inputs.
--
--   **`QuantumSixJ.Certificate.upperCoefficient`.** For any integers $C,E,F,j$, set $D=E+F-C-j$; this defines the scalar $[E-C+1][F-D+1][F-C+1][E-D+1][2][j]$. Every bracket is the specified rational-function quotient; the integer parameter $F$ is not a factorial here. There are no hypotheses, and at $j=0$ the final factor is $[0]=0$.
--
--   **`QuantumSixJ.Certificate.centerCoefficient`.** For any integers $A,B,C,E,F,j$, set $D=E+F-C-j$ and $G=A+B-j$; this defines the scalar
--   $$
--   -\Big(\big([A-j][E-C]-[F-D][A+2]\big)\big([B-j][F-C]-[E-D][B+2]\big)
--   +\big([F-B][E-A]-[G-D][C+2]\big)[j][j+2]\Big)[j+1].
--   $$
--   All brackets are the explicit rational functions above, all parameters range over all integers without further assumptions, and the formula includes zero and negative values of $j$.
--
--   **`QuantumSixJ.Certificate.scaledMultiplier`.** For any integers $A,B,C,E,F,j,t$, set $D=E+F-C-j$; this defines the scalar
--   $$
--   [2]\Big([j+2][t-E-1]\big([j][F-A+1][t-B]+[B-j+1][A+1][F-t+1]\big)
--   -[j][F-C+1][F-D+1][t-A][t-B]\Big).
--   $$
--   The brackets are the stated rational-function quotients. No support, sign, parity, or nonzero restrictions are imposed on any of the seven integer parameters.
--
--   **`QuantumSixJ.Certificate.flux`.** For any integers $A,B,C,E,F,j,S$, set $D=E+F-C-j$ and $G=A+B-j$; this defines the scalar
--   $$
--   \frac{(-1)^S F(S+1)}{F(S-A)F(S-B)F(S-C-1)F(S-D-1)F(E+1-S)F(F+1-S)F(G-S)}
--   \,[2]\Big([j+2][S-E-1]\big([j][F-A+1][S-B]+[B-j+1][A+1][F-S+1]\big)
--   -[j][F-C+1][F-D+1][S-A][S-B]\Big).
--   $$
--   Here $F(\cdot)$ is the signed-index factorial, distinct from the integer parameter $F$, and all bracket and factorial expressions are expanded in the conventions above. There are no hypotheses and no explicit support guard; zero denominators and negative factorial arguments use the total-field and signed-factorial conventions.
--
--   **`QuantumSixJ.Certificate.rawResidual`.** For any integers $A,B,C,E,F,j,S$, set $D=E+F-C-j$ and $G=A+B-j$, and abbreviate the following explicit products by $p_-,p_0,p_+$ solely within this paragraph:
--   $$
--   \begin{aligned}
--   p_-&=[A-j+1][B-j+1][A+1][B+1][2][j+2],\\
--   p_0&=-\Big(([A-j][E-C]-[F-D][A+2])([B-j][F-C]-[E-D][B+2])\\
--   &\hspace{18mm}+([F-B][E-A]-[G-D][C+2])[j][j+2]\Big)[j+1],\\
--   p_+&=[E-C+1][F-D+1][F-C+1][E-D+1][2][j].
--   \end{aligned}
--   $$
--   The defined scalar is exactly
--   $$
--   \begin{aligned}
--   &p_-\frac{(-1)^S F(S+1)}{F(S-A+1)F(S-B+1)F(S-C)F(S-D)F(E-1-S)F(F-1-S)F(G-S)}\\
--   {}+{}&p_0\frac{(-1)^S F(S+1)}{F(S-A)F(S-B)F(S-C)F(S-D)F(E-S)F(F-S)F(G-S)}\\
--   {}+{}&p_+\frac{(-1)^S F(S+1)}{F(S-A-1)F(S-B-1)F(S-C)F(S-D)F(E+1-S)F(F+1-S)F(G-S)}.
--   \end{aligned}
--   $$
--   The notation $F(\cdot)$ denotes the factorial and bare $F$ the integer parameter. There are no hypotheses or support restrictions, and zero denominators give zero quotients, not undefined terms.
--
--   **`QuantumSixJ.Certificate.sumLength`.** For any integers $a,b,c,d,j,l$, this defines the natural number $\max(a+b+c+d+j+l,0)+3$, where the maximum is regarded as a natural number before adding $3$. The truncation applies to the whole sum of the six integers, not to its individual terms; hence every input gives a length of at least $3$, and a nonpositive total gives length exactly $3$.
--
--   **`QuantumSixJ.Certificate.totalResidual`.** For any integers $a,b,c,d,j,l$, put $A=(a+d+j)/2$, $B=(b+c+j)/2$, $C=(a+b+l)/2$, $E=(b+d+j+l)/2$, $F=(a+c+j+l)/2$, $D=E+F-C-j$, $G=A+B-j$, and $n=\max(a+b+c+d+j+l,0)+3$. For these integers form
--   $$
--   \begin{aligned}
--   p_-&=[A-j+1][B-j+1][A+1][B+1][2][j+2],\\
--   p_0&=-\Big(([A-j][E-C]-[F-D][A+2])([B-j][F-C]-[E-D][B+2])\\
--   &\hspace{18mm}+([F-B][E-A]-[G-D][C+2])[j][j+2]\Big)[j+1],\\
--   p_+&=[E-C+1][F-D+1][F-C+1][E-D+1][2][j].
--   \end{aligned}
--   $$
--   This defines the scalar
--   $$
--   \sum_{S=0}^{n-1}\left(
--   \frac{p_-(-1)^S F(S+1)}{F(S-A+1)F(S-B+1)F(S-C)F(S-D)F(E-1-S)F(F-1-S)F(G-S)}
--   +\frac{p_0(-1)^S F(S+1)}{F(S-A)F(S-B)F(S-C)F(S-D)F(E-S)F(F-S)F(G-S)}
--   +\frac{p_+(-1)^S F(S+1)}{F(S-A-1)F(S-B-1)F(S-C)F(S-D)F(E+1-S)F(F+1-S)F(G-S)}\right).
--   $$
--   Factorial $F(\cdot)$ is distinct from the integer $F$. There are no admissibility or positivity hypotheses. The summation uses the natural numbers $0,\ldots,n-1$ cast to integers, and contains at least three terms even when the total of the six labels is negative; $D,G$ are the displayed derived integers, without separately replacing them by other half-sums on arbitrary odd inputs.
--
--   **`QuantumSixJ.Certificate.prefactor`.** For any integers $a,b,c,d,j,l$, using the four and three explicit half-sum lists $\alpha^{j,l},\beta^{j,l}$ above, this defines the scalar
--   $$
--   \frac{\prod_{i=0}^{3}\prod_{k=0}^{2}F(\beta_k^{j,l}-\alpha_i^{j,l})}{F(a)F(b)F(c)F(d)F(j)F(l)}.
--   $$
--   There is no admissibility guard: odd or negative labels still have values, using Euclidean division for the half-sums, zero for negative-index factorials, and total field division. In particular a negative one of the six denominator labels makes the value zero.
--
--   **`QuantumSixJ.Certificate.clearingFactor`.** For every integer $j$, this defines the scalar $[2][j][j+1][j+2]$, with each bracket the specified rational-function quotient. No assumption that this product is nonzero is part of the definition; it equals zero at least for $j=0,-1,-2$ because one factor is $[0]$.
--
--   **`QuantumSixJ.Certificate.mainResidual`.** For any integers $a,b,c,d,j,l$, define, within this paragraph, $m_-=N_j[(a+d-j+2)/2][(b+c-j+2)/2]$ when $H_j\land H_{j-2}$ and zero otherwise; $m_0=-N_j[2]E(a,j,d)E(b,j,c)/([j][j+2])$ when $H_j\land j\ne0$ and zero otherwise; and $m_+=N_{j+2}[(a+d-j)/2][(b+c-j)/2]$ when $H_j\land H_{j+2}$ and zero otherwise. The defined scalar is
--   $$
--   m_-U_{j-2,l}+\big(m_0-E(a,b,l)N_j\big)U_{j,l}+m_+U_{j+2,l},
--   $$
--   where $H,N,E,U$ are the explicitly expanded predicates and rational-function finite-sum expressions above. No admissibility, positivity, or nonzero condition is assumed on the six integers; the neighbor values include negative channels, the zero diagonal at $j=0$ is retained, and every quotient, including the division by $N_r$ in each $U_{r,l}$, uses total field division.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, https://arxiv.org/abs/1009.2261, Appendix finite Tet formula and Eq. (24); auxiliary factorial-shift and telescoping-certificate calculation for those formulas.

import Definitions.Def_QuantumSixJScalar

/-! Auxiliary finite-sum weights and coefficients for the telescoping proof.
The three entry functions are the diagonal and step-2 entries, written without
two-index minimum/maximum branches for factorial-shift calculations.
-/
noncomputable section
open scoped BigOperators QuantumSixJ Classical
namespace QuantumSixJ
def diagonalEntry (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ j ≠ 0 then
    -h a b c d j * ⟬2⟭ * Λ a j d * Λ b j c / (⟬j⟭ * ⟬j + 2⟭)
  else 0

def Lp2 (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ hAdmissible a b c d (j + 2) then
    h a b c d (j + 2) * ⟬(a + d - j) / 2⟭ * ⟬(b + c - j) / 2⟭
  else 0

def Lm2 (a b c d j : ℤ) : Scalar :=
  if hAdmissible a b c d j ∧ hAdmissible a b c d (j - 2) then
    h a b c d j * ⟬(a + d - (j - 2)) / 2⟭ * ⟬(b + c - (j - 2)) / 2⟭
  else 0

end QuantumSixJ
noncomputable section
namespace QuantumSixJ.Certificate
open scoped QuantumSixJ BigOperators

def rawSummand (A B C D E F G S : ℤ) : Scalar :=
  (-1 : Scalar) ^ S * ⟬S + 1⟭! /
    (⟬S - A⟭! * ⟬S - B⟭! * ⟬S - C⟭! * ⟬S - D⟭! *
      ⟬E - S⟭! * ⟬F - S⟭! * ⟬G - S⟭!)

def commonWeight (A B C E F j S : ℤ) : Scalar :=
  let D := E + F - C - j
  let G := A + B - j
  (-1 : Scalar) ^ S * ⟬S + 1⟭! *
    (⟬S - A + 1⟭!)⁻¹ * (⟬S - B + 1⟭!)⁻¹ * (⟬S - C⟭!)⁻¹ *
    (⟬S - D⟭!)⁻¹ * (⟬E - S + 1⟭!)⁻¹ * (⟬F - S + 1⟭!)⁻¹ * (⟬G - S⟭!)⁻¹

def lowerCoefficient (A B j : ℤ) : Scalar :=
  (⟬A - j + 1⟭ * ⟬B - j + 1⟭ * ⟬A + 1⟭ * ⟬B + 1⟭) * ⟬2⟭ * ⟬j + 2⟭

def upperCoefficient (C E F j : ℤ) : Scalar :=
  let D := E + F - C - j
  (⟬E - C + 1⟭ * ⟬F - D + 1⟭ * ⟬F - C + 1⟭ * ⟬E - D + 1⟭) * ⟬2⟭ * ⟬j⟭

def centerCoefficient (A B C E F j : ℤ) : Scalar :=
  let D := E + F - C - j
  let G := A + B - j
  let la := ⟬A - j⟭ * ⟬E - C⟭ - ⟬F - D⟭ * ⟬A + 2⟭
  let lb := ⟬B - j⟭ * ⟬F - C⟭ - ⟬E - D⟭ * ⟬B + 2⟭
  let ll := ⟬F - B⟭ * ⟬E - A⟭ - ⟬G - D⟭ * ⟬C + 2⟭
  let nb := -(la * lb + ll * ⟬j⟭ * ⟬j + 2⟭)
  nb * ⟬j + 1⟭

def scaledMultiplier (A B C E F j t : ℤ) : Scalar :=
  let D := E + F - C - j
  ⟬2⟭ * (⟬j + 2⟭ * ⟬t - E - 1⟭ *
    (⟬j⟭ * ⟬F - A + 1⟭ * ⟬t - B⟭ +
      ⟬B - j + 1⟭ * ⟬A + 1⟭ * ⟬F - t + 1⟭) -
    ⟬j⟭ * ⟬F - C + 1⟭ * ⟬F - D + 1⟭ * ⟬t - A⟭ * ⟬t - B⟭)

def flux (A B C E F j S : ℤ) : Scalar :=
  let D := E + F - C - j
  let G := A + B - j
  rawSummand A B (C + 1) (D + 1) (E + 1) (F + 1) G S *
    scaledMultiplier A B C E F j S

def rawResidual (A B C E F j S : ℤ) : Scalar :=
  let D := E + F - C - j
  let G := A + B - j
  lowerCoefficient A B j * rawSummand (A - 1) (B - 1) C D (E - 1) (F - 1) G S +
    centerCoefficient A B C E F j * rawSummand A B C D E F G S +
    upperCoefficient C E F j * rawSummand (A + 1) (B + 1) C D (E + 1) (F + 1) G S

def sumLength (a b c d j l : ℤ) : ℕ := (a + b + c + d + j + l).toNat + 3

def totalResidual (a b c d j l : ℤ) : Scalar :=
  let A := tetA a b c d j l
  let B := tetB a b c d j l
  ∑ k ∈ Finset.range (sumLength a b c d j l),
    rawResidual (A 0) (A 1) (A 2) (B 0) (B 1) j (k : ℤ)

def prefactor (a b c d j l : ℤ) : Scalar :=
  (∏ i : Fin 4, ∏ k : Fin 3, ⟬tetB a b c d j l k - tetA a b c d j l i⟭!) /
    (⟬a⟭! * ⟬b⟭! * ⟬c⟭! * ⟬d⟭! * ⟬j⟭! * ⟬l⟭!)

def clearingFactor (j : ℤ) : Scalar := ⟬2⟭ * ⟬j⟭ * ⟬j + 1⟭ * ⟬j + 2⟭

def mainResidual (a b c d j l : ℤ) : Scalar :=
  Lm2 a b c d j * normalizedTetSum a b c d (j - 2) l +
    (diagonalEntry a b c d j - Λ a b l * h a b c d j) * normalizedTetSum a b c d j l +
    Lp2 a b c d j * normalizedTetSum a b c d (j + 2) l

end QuantumSixJ.Certificate
end


