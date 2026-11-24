-- Prove2me | Definitions.Def_GoldieRenewal_Implicit_Supplement_LadderLaw
-- name    : GoldieRenewal_Implicit_Supplement_LadderLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:12:48.469606+00:00
-- url     : https://prove2.me/theorems/5696b34f-7aee-4608-8360-3312b439f3a4
-- title:
--   Ladder law η of (3.15), measures μ₊, μ₋ and the expansion (3.17) of Theorem 3.3 for both tails
-- statement:
--   Let $M$ be a random variable with law $\nu$, let $\kappa>0$, and let $M_1,M_2,\dots$ be independent, all with law $\nu$. Put $N_1^{(+)}:=\inf\{n\ge1:\ M_1\cdots M_n>0\}$.
--
--   1. **The ladder law (3.15).**
--   $$
--   \eta(B) := E\Bigl(|M_1\cdots M_{N_1^{(+)}}|^\kappa\,\mathbf 1\Bigl\{\sum_{j=1}^{N_1^{(+)}}\log|M_j|\in B\Bigr\}\Bigr),\qquad B\in\mathcal B,
--   $$
--   the integrand being $0$ on the event that $M_1\cdots M_n\le0$ for all $n\ge1$.
--   2. **The measures $\mu_\pm$** of Theorem 3.3:
--   $$
--   \mu_+(B):=E\,M^\kappa\mathbf 1_{M>0}\mathbf 1_{\log M\in B},\qquad \mu_-(B):=E|M|^\kappa\mathbf 1_{M<0}\mathbf 1_{\log|M|\in B}.
--   $$
--   3. **The expansion (3.17).** With $g_1(t)=e^{\kappa t}(P(R>e^t)-P(MR>e^t))$ and $g_{-1}(t)=e^{\kappa t}(P(R<-e^t)-P(MR<-e^t))$ (equations (3.5)–(3.6)), $\hat f(\theta)=\int e^{i\theta t}f(t)\,dt$, $\hat\mu(\theta)=\int e^{i\theta t}\mu(dt)$, and $C_+=C_-$ the constant (2.14), the upper-tail expansion is: for every admissible contour $\mathcal C$ for $1-\hat\eta$ in the strip $-\beta<\Im\theta<0$,
--   $$
--   t^\kappa P(R>t) = C_+ - \frac1{2\pi}\Re\oint_{\mathcal C} e^{-i\theta\log t}\Bigl(\frac{\hat g_1+\hat g_{-1}}{2(1-\hat\mu_+-\hat\mu_-)}+\frac{\hat g_1-\hat g_{-1}}{2(1-\hat\mu_++\hat\mu_-)}\Bigr)(\theta)\,d\theta + O(t^{-\beta/2}),\qquad t\to\infty.
--   $$
--   The lower-tail expansion is the same formula for $-R$ in place of $R$: $t^\kappa P(R<-t)$ on the left, and $\hat g_1,\hat g_{-1}$ exchanged on the right.
--
--   $\eta$ is the law that drives the renewal argument when $M$ takes both signs. It is defined for every $M$ with $P(M<0)>0$, including $M\le0$ a.s., where it equals $\mu_-^{(2)}$.
--
--   **Formalization Note** The i.i.d. sequence is the coordinate process of the infinite product $\nu^{\otimes\mathbb N}$. On the event where some partial product is positive, every factor up to $N_1^{(+)}$ is nonzero, so $|M_1\cdots M_N|^\kappa=\exp(\kappa\sum_{j\le N}\log|M_j|)$. Hence $\eta$ is the image of the restricted product measure under the ladder sum, with density $y\mapsto e^{\kappa y}$; Lean's $\log0=0$ never enters. The infinite product is the zero measure unless $\nu$ is a probability law; it is only applied to the law of a measurable $M$ on a probability space. $\mu_+$ is the published `GoldieRenewal.Rates.tiltedLaw`. The contour $\mathcal C$ is the positively oriented boundary of an axis-parallel rectangle in the strip that encloses every zero of $1-\hat\eta$ there (the published `EnclosesZerosInStrip`, as in the published Theorem 3.2). The paper prints the exponent $e^{-i\theta t}$; its proof works in the variable $\log t$, so the exponent is $e^{-i\theta\log t}$, as in the published expansions (3.8) and (3.10).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 134, (3.15), Theorem 3.3 (μ₊, μ₋, (3.17)); proof p. 156

import Mathlib
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Implicit_TailConstants

open MeasureTheory ProbabilityTheory Complex Filter Asymptotics

namespace GoldieRenewal.Implicit.Supplement

/-- The event `{M₁ ⋯ M_n > 0 for some n ≥ 1}` on the sequence space `ℕ → ℝ`, with 0-based storage
(`x j` is the paper's `M_{j+1}`). -/
def ladderSet : Set (ℕ → ℝ) :=
  {x | ∃ n : ℕ, 0 < ∏ j ∈ Finset.range (n + 1), x j}

/-- `Σ_{j=1}^{N₁^{(+)}} log|M_j|`, where `N₁^{(+)} := inf{n ≥ 1 : M₁ ⋯ M_n > 0}` (Goldie 1991,
(3.15), p. 134), on the sequence space with 0-based storage. Off `ladderSet` the value is an
unused `0`. -/
noncomputable def ladderSum (x : ℕ → ℝ) : ℝ := by
  classical
  exact if h : ∃ n : ℕ, 0 < ∏ j ∈ Finset.range (n + 1), x j then
    ∑ j ∈ Finset.range (Nat.find h + 1), Real.log |x j| else 0

/-- **The ladder law `η` of (3.15)** (Goldie 1991, p. 134), for `M` with law `ν`: with
`M₁, M₂, …` i.i.d. with law `ν` and `N₁^{(+)} := inf{n ≥ 1 : M₁ ⋯ M_n > 0}`,
`η(B) := E(|M₁ ⋯ M_{N₁^{(+)}}|^κ 1{Σ_{j=1}^{N₁^{(+)}} log|M_j| ∈ B})`, the integrand being `0` on
the event that `M₁ ⋯ M_n ≤ 0` for all `n ≥ 1`.

**Formalization Note** The i.i.d. sequence is the coordinate process under the infinite product
`ν^{⊗ℕ}` (`Measure.infinitePi`). Restricting to `ladderSet` encodes "the integrand is `0` when no
partial product is positive". On `ladderSet` every factor `M_j`, `j ≤ N₁^{(+)}`, is nonzero, so
`|M₁ ⋯ M_N|^κ = exp(κ Σ_{j ≤ N} log|M_j|)`; hence `η` is the image of the restricted product
measure under `ladderSum`, with density `y ↦ e^{κy}`. `Measure.infinitePi` is the zero measure
unless `ν` is a probability measure; it is only applied to the law of a measurable `M` on a
probability space. -/
noncomputable def ladderLawOf (ν : Measure ℝ) (κ : ℝ) : Measure ℝ :=
  (((Measure.infinitePi (fun _ : ℕ => ν)).restrict ladderSet).map ladderSum).withDensity
    (fun y => ENNReal.ofReal (Real.exp (κ * y)))

/-- The ladder law `η` of (3.15) for the random variable `M` on `(Ω, P)`: `ladderLawOf` of the law
`P.map M`. -/
noncomputable def ladderLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → ℝ) (κ : ℝ) :
    Measure ℝ :=
  ladderLawOf (P.map M) κ

/-- `μ₊(B) := E M^κ 1_{M>0} 1_{log M ∈ B}` (Goldie 1991, Theorem 3.3, p. 134): the image of `P`
restricted to `{M > 0}` under `log M`, with density `x ↦ e^{κx}` (since `M^κ = e^{κ log M}` on
`{M > 0}`). It is the published `GoldieRenewal.Rates.tiltedLaw P M κ`. -/
noncomputable def muPlus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → ℝ) (κ : ℝ) :
    Measure ℝ :=
  GoldieRenewal.Rates.tiltedLaw P M κ

/-- `μ₋(B) := E|M|^κ 1_{M<0} 1_{log|M| ∈ B}` (Goldie 1991, Theorem 3.3, p. 134): the image of `P`
restricted to `{M < 0}` under `log|M|`, with density `x ↦ e^{κx}`. -/
noncomputable def muMinus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → ℝ) (κ : ℝ) :
    Measure ℝ :=
  ((P.restrict {ω | M ω < 0}).map (fun ω => Real.log |M ω|)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (κ * x)))

/-- The contour term of (3.17) (Goldie 1991, Theorem 3.3, p. 134) at the variable `t`:
`(1/2π) ℜ ∮_𝒞 e^{−iθ log t} [ (ĝ₁ + ĝ₋₁)/(2(1 − μ̂₊ − μ̂₋)) + (ĝ₁ − ĝ₋₁)/(2(1 − μ̂₊ + μ̂₋)) ](θ) dθ`,
with `ĝ₁, ĝ₋₁` the transforms (`fourierTransform`) of `g₁, g₋₁` of (3.5)–(3.6), `μ̂±` the
transforms (`charTransform`) of `μ±`, and `𝒞` the positively oriented boundary of the rectangle
with lower-left corner `z` and upper-right corner `w` (`RectangleIntegral`).

**Formalization Note** The paper prints `e^{−iθt}`; as for (3.8) in the published
`GoldieRenewal.Rates.contourTermPos`, its proof (pp. 154–156) works in the logarithmic variable, so
the exponent is `−iθ log t`. -/
noncomputable def contourTermSigned {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M R : Ω → ℝ) (κ : ℝ) (z w : ℂ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (RectangleIntegral
      (fun θ : ℂ => Complex.exp (-(I * θ * (Real.log t : ℂ))) *
        ((GoldieRenewal.Rates.fourierTransform (fun s => (GoldieRenewal.Rates.gPos P M R κ s : ℂ)) θ +
            GoldieRenewal.Rates.fourierTransform
              (fun s => (GoldieRenewal.Rates.gNeg P M R κ s : ℂ)) θ) /
          (2 * (1 - GoldieRenewal.Rates.charTransform (muPlus P M κ) θ -
            GoldieRenewal.Rates.charTransform (muMinus P M κ) θ)) +
        (GoldieRenewal.Rates.fourierTransform (fun s => (GoldieRenewal.Rates.gPos P M R κ s : ℂ)) θ -
            GoldieRenewal.Rates.fourierTransform
              (fun s => (GoldieRenewal.Rates.gNeg P M R κ s : ℂ)) θ) /
          (2 * (1 - GoldieRenewal.Rates.charTransform (muPlus P M κ) θ +
            GoldieRenewal.Rates.charTransform (muMinus P M κ) θ)))) z w).re

/-- **Expansion (3.17)** for the upper tail (Goldie 1991, Theorem 3.3(i), p. 134), in its proved
form: for every admissible rectangle contour `𝒞` for `1 − η̂` with `η` the ladder law (3.15) (see
`GoldieRenewal.Rates.EnclosesZerosInStrip`),
`t^κ P(R > t) = C₊ − (contour term of (3.17)) + O(t^{−β/2})`, `t → ∞`,
where `C₊ = C₋` is the Case 2 constant (2.14) of Theorem 2.3 (`GoldieRenewal.Implicit.Ctwo`). -/
def ExpansionSignedPos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ)
    (κ β : ℝ) : Prop :=
  ∀ z w : ℂ,
    GoldieRenewal.Rates.EnclosesZerosInStrip
        (fun θ => 1 - GoldieRenewal.Rates.charTransform (ladderLaw P M κ) θ) β z w →
      (fun t : ℝ => t ^ κ * P.real {ω | t < R ω} -
          (GoldieRenewal.Implicit.Ctwo P M R κ - contourTermSigned P M R κ z w t))
        =O[atTop] (fun t : ℝ => t ^ (-(β / 2)))

/-- **"The same formula holds for `t^κ P(R < −t)`"** (Goldie 1991, Theorem 3.3(i), p. 134), read
as the proof does (p. 156: "for `−R` in place of `R`"): (3.17) for `−R`. Since `P(−R > t) =
P(R < −t)` and `C₊ = C₋`, this says `t^κ P(R < −t) = C₋ − (contour term of (3.17) for −R) +
O(t^{−β/2})`; replacing `R` by `−R` swaps `ĝ₁` and `ĝ₋₁`, i.e. flips the sign of the second
fraction. -/
def ExpansionSignedNeg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ)
    (κ β : ℝ) : Prop :=
  ExpansionSignedPos P M (fun ω => -R ω) κ β

end GoldieRenewal.Implicit.Supplement


