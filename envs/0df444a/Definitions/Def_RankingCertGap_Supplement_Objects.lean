-- Prove2me | Definitions.Def_RankingCertGap_Supplement_Objects
-- name    : RankingCertGap_Supplement_Objects
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:56:33.18854+00:00
-- url     : https://prove2.me/theorems/516bbfa9-0ab5-43ac-a950-9b961d6f809c
-- title:
--   Functionals, optimizers, Stieltjes measures, gaps, and $L^1$ distance for Theorems 3–8
-- statement:
--   For an admissible gain-sharing function $f$, define
--   $$
--   F_f(t)=\int_0^t f(y)\,dy,\qquad H_f(t)=F_f(t)+1-f(t).
--   $$
--   The unrestricted instance class consists of all finite online bipartite matching instances, and the certifying gap is the competitiveness minus the certifying capacity.
--
--   The exponential profile $f^\star_\infty(y)=e^{y-1}$, the constant profile $f^\star_1\equiv1$, and the step profile $f^\star_2$ are represented as total real functions that agree with the paper on $[0,1]$. For the degree-two step profile, $s^\star$ is selected from the roots in $(0,1)$ of
--   $$
--   2s^4+2s^3-8s^2-33s+7=0,
--   $$
--   and $w^\star=2/((1-s^\star)(3-s^\star))$.
--
--   A probability measure $\mu$ supported on $[0,1]$ is the Stieltjes measure of $f$ when $\mu([0,y])=f(y)$ for every $y\in[0,1]$. The $L^1([0,1])$ distance is $\int_0^1|f(y)-g(y)|\,dy$.
--
--   These objects provide the shared vocabulary for the six supplement theorems.
--
--   **Formalization Note** The paper's profiles have domain $[0,1]$; clamped or constant values outside that interval only make them total functions and do not change any source instance or score. Theorem 5 proves that the root set defining $s^\star$ is a singleton, preventing an empty-infimum value.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), eqs. (12)–(13), p.7; eqs. (15), (17)–(18), (22), p.8; eq. (32), p.11

import Mathlib
import Definitions.Def_RankingCertGap_CertifyingCapacity

set_option autoImplicit false

open MeasureTheory

namespace RankingCertGap.Supplement

/-- The unrestricted class of all finite online bipartite instances, used for the untilded
`d = ∞` quantities. Xu, arXiv:2610.17545 (held file sha256 75896dd9…), Table 1 and Theorem 3,
pp.7–8.

**Formalization Note.** This is not an "infinite-degree" instance class: it is the class of all
finite instances, exactly as the footnote to Table 1 specifies. -/
def unrestricted : InstClass := Set.univ

/-- `F_f(t) := ∫₀ᵗ f(y) dy`, eq. (13), p.7. -/
noncomputable def Ff (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ y in (0 : ℝ)..t, f y

/-- `H_f(t) := F_f(t) + 1 - f(t)`, eq. (13), p.7. -/
noncomputable def Hf (f : ℝ → ℝ) (t : ℝ) : ℝ := Ff f t + 1 - f t

/-- The certifying gap `Δ_ᵔ(𝒮) := γ(ᵔ) - Γ_𝒮(ᵔ)`, eq. (6), p.3. -/
noncomputable def gapC (S : Set (ℝ → ℝ)) (C : InstClass) : ℝ := gammaC C - GammaC S C

/-- The exponential profile `f★_∞(y) = exp(y - 1)` on `[0,1]`, eq. (15), p.8.

**Formalization Note.** The source profile has domain `[0,1]`. The argument is clamped to `[0,1]`
to give the total `ℝ → ℝ` representative required by the published `classF`; this changes no source
value or score. -/
noncomputable def expProfile (y : ℝ) : ℝ := Real.exp (min 1 (max 0 y) - 1)

/-- The constant profile `f★₁ ≡ 1`, eq. (17), p.8. -/
def oneProfile (_ : ℝ) : ℝ := 1

/-- The quartic in eq. (18), p.8, whose unique root in `(0,1)` is `s★`. -/
def rootPoly (s : ℝ) : ℝ := 2 * s ^ 4 + 2 * s ^ 3 - 8 * s ^ 2 - 33 * s + 7

/-- `s★`, eq. (18), p.8, selected as the infimum of the roots in `(0,1)`.

Theorem 5 states that this set has exactly one element, so this definition has no empty-set or
multiple-root ambiguity in use. -/
noncomputable def sStar : ℝ := sInf {s : ℝ | s ∈ Set.Ioo 0 1 ∧ rootPoly s = 0}

/-- `w★ := 2 / ((1-s★)(3-s★))`, eq. (22), p.8. -/
noncomputable def wStar : ℝ := 2 / ((1 - sStar) * (3 - sStar))

/-- The step-profile optimizer `f★₂` of eq. (22), p.8.

**Formalization Note.** Values below `0` and above `1` extend the printed profile monotonically;
only values on `[0,1]` are part of the source object. -/
noncomputable def fStar (y : ℝ) : ℝ := if y < sStar then 0 else if y < 1 then wStar else 1

/-- A probability measure `μ` is the Stieltjes measure `π_f` of the source profile `f` when its
distribution function on `[0,1]` is `f`: `f(y) = μ([0,y])`. Xu, eq. (12) and the display below
eq. (22), pp.5, 8.

**Formalization Note.** Measures live on `ℝ` and are identified by their values on lower intervals.
The theorem uses measures supported on `[0,1]`; `IsProbabilityMeasure` prevents the zero-measure
degeneracy. -/
def HasStieltjesMeasure (f : ℝ → ℝ) (mu : Measure ℝ) : Prop :=
  IsProbabilityMeasure mu ∧ mu (Set.Icc (0 : ℝ) 1) = 1 ∧
    ∀ y ∈ Set.Icc (0 : ℝ) 1, mu (Set.Iic y) = ENNReal.ofReal (f y)

/-- The Lebesgue `L¹([0,1])` distance used in eq. (32), p.11. -/
noncomputable def l1Dist (f g : ℝ → ℝ) : ℝ := ∫ y in (0 : ℝ)..1, |f y - g y|

end RankingCertGap.Supplement


