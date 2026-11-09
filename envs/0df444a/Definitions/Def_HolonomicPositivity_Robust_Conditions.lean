-- Prove2me | Definitions.Def_HolonomicPositivity_Robust_Conditions
-- name    : HolonomicPositivity_Robust_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:44.20405+00:00
-- url     : https://prove2.me/theorems/387b8ae2-567d-4edc-8060-fffdf0f40731
-- title:
--   Conditions (I) and (II) of Theorem 3.1, the thresholds $R_P$, and the inequalities of Lemmas 5.3 and 5.4
-- statement:
--   **Taylor coefficients.** For $P\in\mathbb R(x)$, the numbers $p_0,p_1,p_2,p_3$ are its expansion coefficients at infinity when
--
--   $$P(x)=p_0+\frac{p_1}{x}+\frac{p_2}{x^2}+\frac{p_3}{x^3}+O(x^{-4}).\tag{7}$$
--
--   **Condition (I).** $1\le\lim_{x\to\infty}P(x)\le\infty$ and $Q\ge-P$, where the limit is either a finite $\ell\ge1$ or $+\infty$.
--
--   **Condition (II).** The comparisons
--
--   $$-\frac13-\frac1{9x^2}+O(x^{-3})\le P(x)<1-\frac2x+O(x^{-2})$$
--
--   hold, and $Q(x)\ge R_P(x)+O(x^{-d})$, with $R_P$ and $d$ given by the coefficients of $P$:
--
--   1. (II-1) if $p_0>-\frac13$, then $R_P(x)=a^3-a^2-p_0a-\frac{p_1a}{x}-\frac{b}{x^2}$ and $d=3$, where $a=\frac{1+\sqrt{1+3p_0}}3$ and $b=p_2a+\frac{(a+p_0+p_1)^2}{4\sqrt{1+3p_0}}$;
--   2. (II-2) if $p_0=-\frac13$ and $p_1>0$, then $R_P(x)=\frac1{27}-\frac{p_1}{3x}$ and $d=2$;
--   3. (II-3) if $(p_0,p_1)=(-\frac13,0)$, then $R_P(x)=\frac1{27}-\frac{p_2}{3x^2}-\frac{c}{x^3}$ and $d=4$, where $c=\frac{p_2+p_3}3+\frac{2}{81\sqrt3}(1+9p_2)^{3/2}$.
--
--   **Second-order inequalities.** For functions $A,B$, inequality (6) for the quotient means
--
--   $$\frac{A(x)}{B(x)B(x-1)}\ge-\frac14-\frac1{16x^2}+O(x^{-3}).\tag{6}$$
--
--   A rational function $L$ is a witness for $(A,B)$ when $0<L(x+1)<B(x)$ and $L(x)(B(x)-L(x+1))+A(x)\ge0$ in the eventual order. For $S\in\mathbb R(x)$, put $B(x)=1-S(x+2)$, $A(x)=B(x)S(x+1)+P(x)$ and $C(x)=A(x)S(x)+Q(x)$.
--
--   These conditions are the hypotheses of the goal theorem and of its supporting lemmas.
--
--   **Formalization Note** The coefficients in condition (II) are existentially quantified together with (7). The two comparisons on $P$ bound $P$ near infinity, so the expansion exists, and it is unique, so the existential and universal readings agree. The case split is exhaustive, because the lower comparison excludes $p_0<-\frac13$ and also $p_0=-\frac13,\ p_1<0$. In case (II-3) it gives $1+9p_2\ge0$, so the real power $(1+9p_2)^{3/2}$ never meets a negative base in that case. In case (II-1), $1+3p_0>0$, so the square root in the denominator of $b$ is positive.
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2: inequality (6), Theorem 3.1 conditions (I), (II), expansion (7) PDF p.5 (XX:5); Lemmas 5.3, 5.4 PDF p.10 (XX:10).

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Comparison
open Filter Topology

namespace HolonomicPositivity.Robust

/-- The Taylor expansion (7) at infinity, PDF p.5:
`P(x) = p₀ + p₁/x + p₂/x² + p₃/x³ + O(x⁻⁴)`. The four coefficients are determined by `P`. -/
def HasTaylorExpansion (P : RatFunc ℝ) (p₀ p₁ p₂ p₃ : ℝ) : Prop :=
  EqMod (ev P) (fun x => p₀ + p₁ / x + p₂ / x ^ 2 + p₃ / x ^ 3) (-4)

/-- `a := (1 + √(1 + 3p₀)) / 3` in case (II-1). -/
noncomputable def aConst (p₀ : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 3 * p₀)) / 3

/-- `b := p₂ a + (a + p₀ + p₁)² / (4 √(1 + 3p₀))` in case (II-1). -/
noncomputable def bConst (p₀ p₁ p₂ : ℝ) : ℝ :=
  p₂ * aConst p₀ + (aConst p₀ + p₀ + p₁) ^ 2 / (4 * Real.sqrt (1 + 3 * p₀))

/-- `c := (p₂ + p₃) / 3 + 2 / (81 √3) · (1 + 9p₂)^{3/2}` in case (II-3). -/
noncomputable def cConst (p₂ p₃ : ℝ) : ℝ :=
  (p₂ + p₃) / 3 + 2 / (81 * Real.sqrt 3) * (1 + 9 * p₂) ^ (3 / 2 : ℝ)

/-- `R_P` in case (II-1): `a³ - a² - p₀ a - p₁ a / x - b / x²`. -/
noncomputable def thresholdOne (p₀ p₁ p₂ : ℝ) (x : ℝ) : ℝ :=
  aConst p₀ ^ 3 - aConst p₀ ^ 2 - p₀ * aConst p₀ - p₁ * aConst p₀ / x - bConst p₀ p₁ p₂ / x ^ 2

/-- `R_P` in case (II-2): `1/27 - p₁ / (3x)`. -/
noncomputable def thresholdTwo (p₁ : ℝ) (x : ℝ) : ℝ :=
  1 / 27 - p₁ / (3 * x)

/-- `R_P` in case (II-3): `1/27 - p₂ / (3x²) - c / x³`. -/
noncomputable def thresholdThree (p₂ p₃ : ℝ) (x : ℝ) : ℝ :=
  1 / 27 - p₂ / (3 * x ^ 2) - cConst p₂ p₃ / x ^ 3

/-- Condition (I) of Theorem 3.1: `1 ≤ lim_{x→∞} P(x) ≤ ∞` and `Q ≥ -P`. -/
def ConditionI (P Q : RatFunc ℝ) : Prop :=
  ((∃ l : ℝ, 1 ≤ l ∧ Tendsto (ev P) atTop (𝓝 l)) ∨ Tendsto (ev P) atTop atTop) ∧
    EventuallyGE (ev Q) (fun x => -ev P x)

/-- Condition (II) of Theorem 3.1:
`-1/3 - 1/(9x²) + O(x⁻³) ≤ P(x) < 1 - 2/x + O(x⁻²)` and `Q(x) ≥ R_P(x) + O(x^{-d})`, with `R_P`
and `d` given by the case of the Taylor coefficients of `P`. -/
def ConditionII (P Q : RatFunc ℝ) : Prop :=
  GeMod (ev P) (fun x => -(1 / 3) - 1 / (9 * x ^ 2)) (-3) ∧
    LtMod (ev P) (fun x => 1 - 2 / x) (-2) ∧
    ∃ p₀ p₁ p₂ p₃ : ℝ, HasTaylorExpansion P p₀ p₁ p₂ p₃ ∧
      ((-(1 / 3) < p₀ ∧ GeMod (ev Q) (thresholdOne p₀ p₁ p₂) (-3)) ∨
       (p₀ = -(1 / 3) ∧ 0 < p₁ ∧ GeMod (ev Q) (thresholdTwo p₁) (-2)) ∨
       (p₀ = -(1 / 3) ∧ p₁ = 0 ∧ GeMod (ev Q) (thresholdThree p₂ p₃) (-4)))

/-- `A(x) / (B(x) B(x-1))` satisfies the inequality (6), PDF p.5:
`≥ -1/4 - 1/(16x²) + O(x⁻³)`. -/
def SatisfiesInequalitySix (A B : ℝ → ℝ) : Prop :=
  GeMod (fun x => A x / (B x * B (x - 1))) (fun x => -(1 / 4) - 1 / (16 * x ^ 2)) (-3)

/-- The two conditions on `L` in Lemma 5.3, PDF p.10:
(1) `0 < L(x+1) < B(x)`; (2) `L(x) (B(x) - L(x+1)) + A(x) ≥ 0`, in the eventual order. -/
def IsRiccatiWitness (A B : ℝ → ℝ) (L : RatFunc ℝ) : Prop :=
  EventuallyGT (fun x => ev L (x + 1)) (fun _ => 0) ∧
    EventuallyGT B (fun x => ev L (x + 1)) ∧
    EventuallyGE (fun x => ev L x * (B x - ev L (x + 1)) + A x) (fun _ => 0)

/-- `B(x) := 1 - S(x+2)` in Lemma 5.4, PDF p.10. -/
noncomputable def scaledB (S : RatFunc ℝ) (x : ℝ) : ℝ :=
  1 - ev S (x + 2)

/-- `A(x) := B(x) S(x+1) + P(x)` in Lemma 5.4, PDF p.10. -/
noncomputable def scaledA (P S : RatFunc ℝ) (x : ℝ) : ℝ :=
  scaledB S x * ev S (x + 1) + ev P x

/-- `C(x) := A(x) S(x) + Q(x)` in Lemma 5.4, PDF p.10. -/
noncomputable def scaledC (P Q S : RatFunc ℝ) (x : ℝ) : ℝ :=
  scaledA P S x * ev S x + ev Q x

end HolonomicPositivity.Robust


