-- Prove2me | Definitions.Def_CondGeoVerif_risk
-- name    : CondGeoVerif_risk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:40.02027+00:00
-- url     : https://prove2.me/theorems/63957f47-2cbe-4070-ba80-d44e9469fc6b
-- title:
--   Gaussian marginal, risk $R_P(h)$, $\mathrm{OPT}_P(\mathcal H)$, Massart noise (2.1) and labeled laws
-- statement:
--   A law $P$ of a labeled example $(X,Y)\in\mathbb R^d\times\{-1,1\}$ has the **Gaussian feature marginal** if $X\sim N(0,I_d)$. The **risk** of a predictor $h$ is $R_P(h)=P(h(X)\ne Y)$ and $\mathrm{OPT}_P(\mathcal H)=\inf_{h\in\mathcal H}R_P(h)$.
--
--   $P$ satisfies **Massart noise** with bound $\eta$ around a target $h^*$ if
--   $$P(Y\ne h^*(X)\mid X)\le\eta\quad\text{almost surely}\qquad(2.1)$$
--   (the error probability may depend on every coordinate of $X$). $P$ is the **labeled law with base rule $h$ and error probability $p$** if $X\sim N(0,I_d)$ and $P(Y\ne h(X)\mid X)=p(X)$. With $p\equiv\eta$ and $h(x)=f(x_1,\dots,x_k)$ this is the random-noise anchor $Q$, $\mathbb E_Q[Y\mid X]=af(X_1,\dots,X_k)$ with $a=1-2\eta$.
--
--   The **sample law** of size $n$ is the product $P^{\otimes n}$.
--
--   **Formalization Note** Labels are Booleans. Conditional statements are encoded without conditional expectations: Massart noise is $P(\{X\in B,\ Y\ne h^*(X)\})\le\eta\,N(0,I_d)(B)$ for every Borel $B$, and a labeled law is characterized by its Gaussian marginal and $P(\{X\in B,\ Y\ne h(X)\})=\int_B p\,dN(0,I_d)$ for every Borel $B$; for measurable $h$ and $p$ with values in $[0,1]$ exactly one probability measure has this property. The risk of a non-measurable predictor would be an outer measure; every predictor to which the mission applies `risk` is measurable. $\mathrm{OPT}$ is a real infimum over the class, the true infimum for nonempty classes.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §2, p.3 (PDF p.6), Definition 2.1 and (2.1); Theorem B.1, p.24 (PDF p.27); §B.2, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_CondGeoVerif_projClass

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory

/-- A law `P` of a labeled example `(X, Y) ∈ ℝᵈ × {−1, 1}` has the **promised Gaussian feature
marginal** `X ∼ N(0, I_d)` (Chen, *The Conditional Geometry of Statistical Verification*,
manuscript, October 2026, sha256 07a66d18…, §2, pp.3–4 = PDF pp.6–7). Labels are `Bool`, with
`true` for `+1`. -/
def GaussMarginal {d : ℕ} (P : Measure (Vec d × Bool)) : Prop :=
  P.map Prod.fst = gauss d

/-- The risk `R_P(h) = P(h(X) ≠ Y)` of a predictor `h : ℝᵈ → {−1, 1}` (Chen, Oct. 2026, §2, p.3).

**Formalization Note** The probability is the measure of the set `{(x, y) | h x ≠ y}`; for a
non-measurable `h` this is its outer measure. Every predictor to which the mission applies `risk`
in a hypothesis or conclusion is measurable (proper outputs, or the jointly measurable improper
outputs of `IVerifier`). -/
noncomputable def risk {d : ℕ} (P : Measure (Vec d × Bool)) (h : Vec d → Bool) : ℝ :=
  (P {p | h p.1 ≠ p.2}).toReal

/-- `OPT_P(H) = inf_{h ∈ H} R_P(h)` (Chen, Oct. 2026, §2, p.3).

**Formalization Note** A real infimum over the subtype `H`; risks lie in `[0, 1]`, so the infimum
is the true one whenever `H` is nonempty. Every class to which the mission applies it is a
nonempty projection class (`d ≥ k`, `F` nonempty). -/
noncomputable def opt {d : ℕ} (P : Measure (Vec d × Bool)) (H : Set (Vec d → Bool)) : ℝ :=
  ⨅ h : H, risk P h

/-- **Massart noise** (2.1) around a target `h*` with noise bound `η` (Chen, Oct. 2026, §2, p.3):
`P(Y ≠ h*(X) | X) ≤ η` almost surely, where the error probability may depend on every coordinate
of `X`.

**Formalization Note** Stated without conditional expectations, as the set inequality
`P({X ∈ B, Y ≠ h*(X)}) ≤ η · N(0, I_d)(B)` for every Borel `B ⊆ ℝᵈ`. For a law with Gaussian
feature marginal and a measurable `h*` this is equivalent to the almost-sure bound on the
conditional error probability. -/
def IsMassart {d : ℕ} (P : Measure (Vec d × Bool)) (hstar : Vec d → Bool) (η : ℝ) : Prop :=
  ∀ B : Set (Vec d), MeasurableSet B →
    P {p | p.1 ∈ B ∧ p.2 ≠ hstar p.1} ≤ ENNReal.ofReal η * gauss d B

/-- `P` is the **labeled law with base rule `h` and error probability `p`**: `X ∼ N(0, I_d)` and,
conditionally on `X`, `Y ≠ h(X)` with probability `p(X)` (Chen, Oct. 2026, Theorem B.1 and
§B.2, pp.24–25). With `p ≡ η` and `h(x) = f(x₁, …, x_k)` this is the random-noise anchor `Q`
(`E_Q[Y | X] = a f(X₁, …, X_k)`, `a = 1 − 2η`); with `p(U, Z) = e(U, VᵀZ)` it is the hidden-frame
alternative `P_V`.

**Formalization Note** Characterized without conditional expectations: the feature marginal is
`N(0, I_d)` and `P({X ∈ B, Y ≠ h(X)}) = ∫_B p dN(0, I_d)` for every Borel `B`. For measurable
`h` and measurable `p` with values in `[0, 1]` there is exactly one such probability measure on
`ℝᵈ × Bool`. -/
def IsLabelLaw {d : ℕ} (P : Measure (Vec d × Bool)) (h : Vec d → Bool) (p : Vec d → ℝ) : Prop :=
  GaussMarginal P ∧ ∀ B : Set (Vec d), MeasurableSet B →
    P {q | q.1 ∈ B ∧ q.2 ≠ h q.1} = ∫⁻ x in B, ENNReal.ofReal (p x) ∂(gauss d)

/-- The law of an i.i.d. sample of size `n` from `P`: the product measure `P^{⊗n}` on
`(ℝᵈ × {−1, 1})ⁿ`. -/
noncomputable def sampleLaw {d : ℕ} (P : ProbabilityMeasure (Vec d × Bool)) (n : ℕ) :
    Measure (Fin n → Vec d × Bool) :=
  Measure.pi (fun _ : Fin n => (P : Measure (Vec d × Bool)))

end CondGeoVerif


